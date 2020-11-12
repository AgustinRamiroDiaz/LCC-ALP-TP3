module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import Data.Maybe ( Maybe(Just, Nothing), maybe, fromJust )
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversion' []

conversion' :: [String] -> LamTerm -> Term
conversion' b (LVar n)        = maybe (Free (Global n)) Bound (n `elemIndex` b)
conversion' b (LApp t u)      = conversion' b t :@: conversion' b u
conversion' b (LAbs n t u)    = Lam t (conversion' (n : b) u)
conversion' b (LLet n u v)    = Let (conversion' b u) (conversion' (n : b) v)
conversion' b (LAs u t)       = As (conversion' b u) t
conversion' _ LUnit           = Unit
conversion' b (LFst u)        = Fst (conversion' b u)
conversion' b (LSnd u)        = Snd (conversion' b u)
conversion' b (LPair u v)     = Pair (conversion' b u) (conversion' b v)
conversion' _ LZero           = Zero
conversion' b (LSuc u)        = Suc (conversion' b u)
conversion' b (LRec u v w)    = Rec (conversion' b u) (conversion' b v) (conversion' b w)

-----------------------
--- eval
-----------------------

sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n)              = Free n
sub i t (u :@: v)             = sub i t u :@: sub i t v
sub i t (Lam t' u)            = Lam t' (sub (i + 1) t u)
sub i t (Let u v)             = Let (sub i t u) (sub (i + 1) t v)
sub i t (As u t')             = As (sub i t u) t'
sub _ _ Unit                  = Unit
sub i t (Fst u)               = Fst $ sub i t u
sub i t (Snd u)               = Snd $ sub i t u
sub i t (Pair u v)            = Pair (sub i t u) (sub i t v)
sub _ _ Zero                  = Zero
sub i t (Suc u)               = Suc $ sub i t u
sub i t (Rec u v w)           = Rec (sub i t u) (sub i t v) (sub i t w)


-- evaluador de términos
eval :: NameEnv Value Type -> Term -> Value
eval _ (Bound _)             = error "variable ligada inesperada en eval"
eval e (Free n)              = fst $ fromJust $ lookup n e
eval _ (Lam t u)             = VLam t u
eval e (Lam _ u :@: Lam s v) = eval e (sub 0 (Lam s v) u)
eval e (Lam _ u :@: v)       = let v' = eval e v in eval e (sub 0 (quote v') u)
eval e (u :@: v)             = case eval e u of VLam t u' -> eval e (Lam t u' :@: v)
                                                _ -> error "Error de tipo en run-time, verificar type checker"
eval e (Let u v)             = let u' = eval e u in eval e (sub 0 (quote u') v)
eval e (As u _)              = eval e u
eval _ Unit                  = VUnit
eval e (Fst u)               = case eval e u of VPair v _ -> v
                                                _ -> error "fst aplicado a algo distinto de Pair"
eval e (Snd u)               = case eval e u of VPair _ v -> v
                                                _ -> error "snd aplicado a algo distinto de Pair"
eval e (Pair u v)            = VPair (eval e u) (eval e v)
eval _ Zero                  = VNum NZero
eval e (Suc u)               = case eval e u of VNum nv -> VNum (NSuc nv)
                                                _ -> error "suc aplicado a algo distinto de Nat"
eval e (Rec u v w)           = case eval e w of VNum NZero -> eval e u
                                                VNum (NSuc nv) -> let nt = quote (VNum nv) in eval e (v :@: (Rec u v nt) :@: nt)
                                                _ -> error "Se aplico R con el tercer termino no Nat"

-----------------------
--- quoting
-----------------------

quote :: Value -> Term
quote (VLam t f)       = Lam t f
quote VUnit            = Unit
quote (VPair v1 v2)    = Pair (quote v1) (quote v2)
quote (VNum NZero)     = Zero
quote (VNum (NSuc nv)) = Suc $ quote $ VNum nv

----------------------
--- type checker
-----------------------

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=) :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v

-- fcs. de error
matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i)   = ret (c !! i)
infer' _ e (Free n)    = case lookup n e of Nothing -> notfoundError n
                                            Just (_, t) -> ret t
infer' c e (t :@: u)   = infer' c e t >>=
                         \tt -> infer' c e u >>=
                         \tu -> case tt of FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
                                           _ -> notfunError tt
infer' c e (Lam t u)   = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let u v)   = infer' c e u >>= \tu -> infer' (tu : c) e v
infer' c e (As u t)    = infer' c e u >>= \tu -> if tu == t then ret t else matchError t tu
infer' _ _ Unit        = ret UnitT
infer' c e (Fst t)     = infer' c e t >>= \tp -> case tp of PairT tf _ -> ret tf
                                                            _ -> err "fst aplicado a algo distinto de Pair"
infer' c e (Snd t)     = infer' c e t >>= \tp -> case tp of PairT _ ts -> ret ts
                                                            _ -> err "snd aplicado a algo distinto de Pair"
infer' c e (Pair u v)  = do tf <- infer' c e u
                            ts <- infer' c e v
                            ret $ PairT tf ts
infer' _ _ Zero        = ret NatT
infer' c e (Suc t)     = do nt <- infer' c e t
                            case nt of NatT -> ret NatT; otro -> matchError NatT otro
infer' c e (Rec u v w) = do tu <- infer' c e u
                            tv <- infer' c e v
                            tw <- infer' c e w
                            case tw of NatT -> case tv of (FunT a (FunT NatT _)) -> if a == tu then ret a else matchError a tu
                                                          _ -> matchError (FunT tu (FunT NatT tu)) tv
                                       _ -> matchError NatT tw


----------------------------------
