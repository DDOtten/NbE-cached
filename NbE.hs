{-
This is an iteration on a blogpost by Zhixuan Yang (https://yangzhixuan.github.io/NbE.html)
discussing an efficient implementation of normalisation by evaluation (NbE) for untyped lambda calculus.
Zhixuan builds up to an efficient implementation using cached normal forms to avoid recomputation.

In this file we implement a further variation (`nf8` at the end of the file) that avoids the need for the
`forceShifts` function, which is a function that forces the application of shifts in cached normal forms.
This optimisation is based on storing the number of shifts at the root of the cached normal forms: instead of
storing a ~TmS with lazy weakenings we store a ~Tm and the number of shifts that need to be applied to the normal form.

I believe the computational complexity of `nf8` is the same as `nf7`, since both have to traverse every
cached normal form once per occurrence to apply the needed shifts (which dependend on the number of additional
binders encountered before substituting), but I have not worked this out in detail yet.

I did compare the output and performance of `nf7` and `nf8` on the original adversarial example and two new ones,
and they match, with `nf8` being slightly faster on my computer. The main advantage of `nf8` is that it is
simpler than `nf7` by shifting the work from the `forceShifts` function to reification. This means that we 
avoiding the need for a version of terms with lazy weakenings, the need for additional datastructures, and return to
the ussual evaluate/reificate and syntactic/semantic structure of NbE. However, a more detailed analasis of
computational behaviour is needed so please let me know if I made a mistake!
-}

{-# LANGUAGE Strict, ViewPatterns, PatternSynonyms, InstanceSigs #-}

module NbE where

type LazyList a = [a]

data Tm = Var Int | App Tm Tm | Abs Tm deriving Eq

infixl `App`

-- `subst s x t` substitutes `t` for every occurrence of `x` in `s`.
subst :: Tm -> Int -> Tm -> Tm
subst (Var n)   x t = if x == n then t else Var n
subst (App f a) x t = App (subst f x t) (subst a x t)
subst (Abs b)   x t = Abs (subst b (x + 1) (shift 0 1 t)) where

-- `shift x i t` increments all variables in `t` that are `>= x` by `i`.
shift :: Int -> Int -> Tm -> Tm
shift x 0 t = t
shift x i (Var n) = if n >= x then Var (n + i) else Var n
shift x i (App f a) = App (shift x i f) (shift x i a)
shift x i (Abs b) = Abs (shift (x+1) i b)

-- `beta b a` stands for beta-reduction for `(\. b) a` (substituting `a` for
-- variable of de Bruijn index 0 in `b`). Because `b` lives in one level deeper
-- than `a`, we use `shift 0 1` to bring `a` to the same level of `b`.
-- Also after substitution, we want to remove the lambda abstraction, so we
-- need to do `shift 0 (-1)` for the result of substitution.
beta :: Tm -> Tm -> Tm
beta b a = shift 0 (-1) (subst b 0 (shift 0 1 a))

-- `fv t` computes the biggest de Bruijn index of all free variables in a term
-- `t`. If a term has no free variables, the result is -1.
fv :: Tm -> Int
fv (Var n) = n
fv (Abs b) = max (-1) (fv b - 1)
fv (App f a) = max (fv f) (fv a)

-- `showTm ns t` computes the string representation of a term and the precedence
-- of the outermost syntactic constructor. The argument `ns` is the list of
-- names for the free variables.
showTm :: Int -> Tm -> (String, Int)
showTm ns (Var n) = ("x" ++ show (ns - n - 1), 100)
showTm ns (Abs b) =
  let (s, _) = showTm (ns + 1) b
  in ("\\x" ++ show ns ++ ". " ++ s, 0)
showTm ns (App f a) =
  let (s1, p1) = showTm ns f
      (s2, p2) = showTm ns a
      s1' = if p1 >= 50 then s1 else "(" ++ s1 ++ ")"
      s2' = if p2 > 50  then s2 else "(" ++ s2 ++ ")"
  in (s1' ++ " " ++ s2', 50)

instance Show Tm where
  show t = let n = fv t in fst (showTm (n+1) t)

-- >>> Abs (Var 0 `App` Var 0)
-- \x0. x0 x0

-- >>> Abs (Var 0 `App` Var 0) `App` (Abs (Var 0))
-- (\x0. x0 x0) (\x0. x0)

-- >>> Abs (Var 0 `App` Var 0) `App` (Abs (Var 0)) `App` (Abs (Var 0))
-- (\x0. x0 x0) (\x0. x0) (\x0. x0)

-- >>> Abs (Var 0 `App` Var 0) `App` (Abs (Abs (Var 1)) `App` Abs (Var 0))
-- (\x0. x0 x0) ((\x0. \x1. x0) (\x0. x0))


-- nf0 ----------------------------------------------------------------------------------------------------------

nf0 :: Tm -> Tm
nf0 (Var n) = Var n
nf0 (Abs b) = Abs (nf0 b)
nf0 (App f a) =
   let f' = nf0 f
       a' = nf0 a
   in case f' of
        Abs b -> nf0 (beta b a')
        _ -> App f' a'

-- Church numeral increment
cinc :: Tm
cinc = Abs (Abs (Abs (Var 2 `App` Var 1 `App` (Var 1 `App` Var 0))))

-- Church numeral 0
c0, c1, c2 :: Tm
c0 = Abs (Abs (Var 0))
c1 = cinc `App` c0
c2 = cinc `App` c1

-- Church numeral addition
cadd :: Tm
cadd = Abs $ Abs $ Abs $ Abs $
  Var 3 `App` Var 1 `App` (Var 2 `App` Var 1 `App` Var 0)

-- Church numeral multiplication
cmul :: Tm
cmul = Abs $ Abs $ Abs $ Abs $
  Var 3 `App` (Var 2 `App` Var 1) `App` Var 0

-- nf1 ----------------------------------------------------------------------------------------------------------

wnf1 :: Tm -> Tm
wnf1 (App f a) =
  let f' = wnf1 f
      ~a' = wnf1 a
  in case f' of
       Abs b -> wnf1 (beta b a')
       _ -> App f' a'
wnf1 t = t

nf1 :: Tm -> Tm
nf1 (Var v) = Var v
nf1 (Abs b) = Abs (nf1 b)
nf1 (App f a) =
  let f' = wnf1 f
      ~a' = wnf1 a
  in case f' of
       Abs b -> nf1 (beta b a')
       _ -> App (reify1 f') (reify1 a')

reify1 :: Tm -> Tm
reify1 (Var v) = Var v
reify1 (Abs b) = Abs (reify1 (wnf1 b))
reify1 (App f a) = App (reify1 f) (reify1 a)

nf1' :: Tm -> Tm
nf1' = reify1 . wnf1

-- A term that is expensive to normalise
expensiveTm :: Int -> Tm
expensiveTm n = Abs (churchNum n `App` (cAnd `App` cTrue) `App` cTrue)

-- Church encoding of Boolean values
cTrue, cFalse :: Tm
cTrue = Abs (Abs (Var 1))
cFalse = Abs (Abs (Var 0))

-- Conjunction of Boolean values
cAnd :: Tm
cAnd = Abs (Abs (Abs (Abs (Var 3 `App` (Var 2 `App` Var 1 `App` Var 0) `App` Var 0))))

-- `churchNum n` is `cinc` applied to zero `n` times.
churchNum :: Int -> Tm
churchNum n = foldr (\_ r -> cinc `App` r) c0 [1 .. n]

-- nf2 ----------------------------------------------------------------------------------------------------------

data Val2 = Closure2 Tm Subst2 | Spine2 Int (LazyList Val2)
type Subst2 = LazyList Val2

shift0Val :: Int -> Val2 -> Val2
shift0Val i (Spine2 n as) = Spine2 (n + i) (shift0List i as)
shift0Val i (Closure2 b sub) = Closure2 b (shift0List i sub)

shift0List :: Int -> Subst2 -> Subst2
shift0List i = map (shift0Val i)

wnf2 :: Tm -> Subst2 -> Val2
wnf2 (Abs b) sub = Closure2 b sub
wnf2 (Var n) sub = sub !! n
wnf2 (App f a) sub =
  let f' = wnf2 f sub
      ~a' = wnf2 a sub
  in case f' of
       Closure2 b sub' -> shift0Val (-1) (wnf2 b (shift0List 1 (a' : sub')))
       Spine2 v as -> Spine2 v (a' : as)

reify2 :: Val2 -> Tm
reify2 (Closure2 b sub) = Abs (reify2 (wnf2 b (Spine2 0 [] : shift0List 1 sub)))
reify2 (Spine2 v as) = foldr (\a r -> r `App` reify2 a) (Var v) as

nf2 :: Tm -> Tm
nf2 t = let n = fv t
        in reify2 (wnf2 t (reflect2 n))

reflect2 :: Int -> Subst2
reflect2 n = map (\v -> Spine2 v []) [0 .. n]

-- nf3 ----------------------------------------------------------------------------------------------------------

wnf3 :: Tm -> Subst2 -> Val2
wnf3 (Var n) sub = sub !! n
wnf3 (Abs b) sub = Closure2 b sub
wnf3 (App f a) sub =
  let f' = wnf3 f sub
      ~a' = wnf3 a sub
  in case f' of
       Closure2 b sub' -> wnf3 b (a' : sub')
       Spine2 v as -> Spine2 v (a' : as)

nf3 :: Tm -> Tm
nf3 t = let n = fv t
        in reify2 (wnf3 t (reflect2 n))

-- nf4 ----------------------------------------------------------------------------------------------------------

data Val4 = Closure4 (Int -> Val4 -> Val4) | Spine4 Int (LazyList Val4)
type Subst4 = LazyList Val4

wnf4 :: Tm -> Subst4 -> Val4
wnf4 (Var n) sub = sub !! n
wnf4 (Abs b) sub = Closure4 (\i (~a) -> wnf4 b (a : shift0List4 i sub))
wnf4 (App f a) sub =
  let f' = wnf4 f sub
      ~a' = wnf4 a sub
  in case f' of
       Closure4 b -> b 0 a'
       Spine4 v as -> Spine4 v (a' : as)

reify4 :: Val4 -> Tm
reify4 (Closure4 b) = Abs $ reify4 (b 1 (Spine4 0 []))
reify4 (Spine4 v as) = foldr (\a r -> r `App` reify4 a) (Var v) as

shift0Val4 :: Int -> Val4 -> Val4
shift0Val4 0 v = v
shift0Val4 i (Spine4 n as) = Spine4 (n + i) (shift0List4 i as)
shift0Val4 i (Closure4 b) = Closure4 (b . (+i))

shift0List4 :: Int -> Subst4 -> Subst4
shift0List4 0 vs = vs
shift0List4 i vs = map (shift0Val4 i) vs

reflect4 :: Int -> Subst4
reflect4 n = map (\v -> Spine4 v []) [0 .. n]

nf4 :: Tm -> Tm
nf4 t = let n = fv t
        in reify4 (wnf4 t (reflect4 n))

-- nf5 ----------------------------------------------------------------------------------------------------------

reify5 :: Int -> Val2 -> Tm
reify5 lvl (Closure2 b sub) = Abs (reify5 (lvl + 1) (wnf3 b (Spine2 lvl [] : sub)))
reify5 lvl (Spine2 v as) = foldr (\a s -> s `App` reify5 lvl a) (Var (lvl - v - 1)) as

reflect5 :: Int -> Subst2
reflect5 n = map (\v -> Spine2 (n - v) []) [0 .. n]

nf5 :: Tm -> Tm
nf5 t = let n = fv t
        in reify5 (n+1) (wnf3 t (reflect5 n))

-- nf6 ----------------------------------------------------------------------------------------------------------

nbeAdversarialExploit :: Tm
nbeAdversarialExploit =
  Abs (foldr (\_ r -> r `App` Var 0) (Var 1) [1..1000000]) `App` expensiveTm 100

data SList a = Nil | Cons_ Int ~a (SList a) deriving Show

data Val6 = Closure6 Tm Subst6 | Spine6 Int (SList Val6)
type Subst6 = SList Val6

class Shift0 a where
  shift0 :: Int -> a -> a

instance Shift0 a => Shift0 (SList a) where
  shift0 :: Shift0 a => Int -> SList a -> SList a
  shift0 i Nil = Nil
  shift0 i (Cons_ j v vs) = Cons_ (i + j) v vs

instance Shift0 Val6 where
  shift0 :: Int -> Val6 -> Val6
  shift0 i (Closure6 b sub) = Closure6 b (shift0 i sub)
  shift0 i (Spine6 j as) = Spine6 (i + j) (shift0 i as)

data ListView a x = NilView | ConsView ~a x

viewSList :: Shift0 a => SList a -> ListView a (SList a)
viewSList Nil = NilView
viewSList (Cons_ i v vs)
  | i /= 0 = ConsView (shift0 i v) (shift0 i vs)
  | otherwise = ConsView v vs

pattern Cons :: Shift0 a => a -> SList a -> SList a
pattern Cons v vs <- (viewSList -> ConsView v vs) where
  Cons ~v vs = Cons_ 0 v vs

lookupSL :: Shift0 a => SList a -> Int -> a
lookupSL Nil _ = error "index out of range"
lookupSL (Cons v vs) i = if i == 0 then v else lookupSL vs (i-1)

foldrSL :: Shift0 a => (a -> r -> r) -> r -> SList a -> r
foldrSL f r Nil = r
foldrSL f r (Cons v vs) = f v (foldrSL f r vs)

dropSL :: Shift0 a => Int -> SList a -> SList a
dropSL 0 as = as
dropSL i Nil = Nil
dropSL i (Cons _ as) = dropSL (i-1) as

wnf6 :: Tm -> Subst6 -> Val6
wnf6 (Var n) sub = lookupSL sub n
wnf6 (Abs b) sub = Closure6 b sub
wnf6 (App f a) sub =
  let f' = wnf6 f sub
      ~a' = wnf6 a sub
  in case f' of
       Closure6 b sub' -> wnf6 b (Cons a' sub')
       Spine6 v as -> Spine6 v (Cons a' as)

reify6 :: Val6 -> Tm
reify6 (Closure6 t sub) = Abs (reify6 (wnf6 t (Cons (Spine6 0 Nil) (shift0 1 sub))))
reify6 (Spine6 v as) = foldrSL (\a r -> r `App` reify6 a) (Var v) as

reflect6 :: Int -> Subst6
reflect6 n = foldr (\x rs -> Cons (Spine6 x Nil) rs) Nil [0 .. n]

nf6 :: Tm -> Tm
nf6 t = let n = fv t
        in reify6 (wnf6 t (reflect6 n))

-- nf7 ----------------------------------------------------------------------------------------------------------

data Val7 = Closure7 Tm Subst7 | Spine7 Int (SList Val7)
          | Cached7 ~TmS Val7
type Subst7 = SList Val7

-- Terms with lazy tagging for `shift0 i`
data TmS = AbsS Int TmS | AppS Int TmS TmS | VarS Int

instance Shift0 TmS where
  shift0 i (AbsS j b) = AbsS (i + j) b
  shift0 i (AppS j f a) = AppS (i + j)  f a
  shift0 i (VarS j) = VarS (i + j)

instance Shift0 Val7 where
  shift0 :: Int -> Val7 -> Val7
  shift0 i (Closure7 b sub) = Closure7 b (shift0 i sub)
  shift0 i (Spine7 j as) = Spine7 (i + j) (shift0 i as)
  shift0 i (Cached7 n v) = Cached7 (shift0 i n) (shift0 i v)

ignoreCache :: Val7 -> Val7
ignoreCache (Cached7 _ v) = v
ignoreCache v = v

makeCache :: Val7 -> Val7
makeCache v@(Cached7 _ _) = v
makeCache v = Cached7 (reify7 v) v

wnf7 :: Tm -> Subst7 -> Val7
wnf7 (Var n) sub = lookupSL sub n
wnf7 (Abs b) sub = Closure7 b sub
wnf7 (App f a) sub =
  let f' = wnf7 f sub
      ~a' = makeCache (wnf7 a sub)
  in case ignoreCache f' of
       Closure7 b sub' -> wnf7 b (Cons a' sub')
       Spine7 v as -> Spine7 v (Cons a' as)

reify7 :: Val7 -> TmS
reify7 (Closure7 t sub) = AbsS 0 (reify7 (wnf7 t (Cons (Spine7 0 Nil) (shift0 1 sub))))
reify7 (Spine7 v as) = foldrSL (\a r -> AppS 0 r (reify7 a)) (VarS v) as
reify7 (Cached7 c _) = c

reflect7 :: Int -> SList Val7
reflect7 n = foldr (\x rs -> Cons (Spine7 x Nil) rs) Nil [0 .. n]

forceShiftsSpec :: TmS -> Tm
forceShiftsSpec (VarS v) = Var v
forceShiftsSpec (AbsS i b) =
  shift 0 i (Abs (forceShiftsSpec b))
forceShiftsSpec (AppS i f a) =
  shift 0 i (App (forceShiftsSpec f) (forceShiftsSpec a))

instance Shift0 Int where
  shift0 i j = i + j

forceShifts :: SList Int -> TmS -> Tm
forceShifts ss (VarS v) = Var (lookupSL ss v)
forceShifts ss (AbsS i b) =
  let ss' = Cons 0 (shift0 1 (dropSL i ss))
  in Abs (forceShifts ss' b)
forceShifts ss (AppS i f a) =
  let ss' = dropSL i ss
  in App (forceShifts ss' f)
         (forceShifts ss' a)

nf7 :: Tm -> Tm
nf7 t = let n = fv t 
            ss = foldr (\v rs -> Cons v rs) Nil [0 .. n]
        in forceShifts ss (reify7 (wnf7 t (reflect7 n)))

-- `nf7` is much faster on the `nbeAdversarialExploit` program that `nf5` was slow:
-- >>> fv (nf7 nbeAdversarialExploit)
-- 0

-- nf8 ----------------------------------------------------------------------------------------------------------

{-}
This is an alternative implementation (nf8) where instead of storing TmS (terms
with lazy shift tags) in the cached
normal forms like nf7, we store a Tm (normal form without lazy shifts) and the
number of shifts/weakenings at the root. This means reify8 can produce a Tm
directly, without needing the forceShifts function.
-}

-- changed Cached ~Tm Val to Cached Int ~Tm Val, where the Int is the number of shifts at the root
data Val8 = Closure8 Tm Subst8 | Spine8 Int (SList Val8)
          | Cached8 Int ~Tm Val8
type Subst8 = SList Val8

instance Shift0 Val8 where
  shift0 :: Int -> Val8 -> Val8
  shift0 i (Closure8 b sub) = Closure8 b (shift0 i sub)
  shift0 i (Spine8 j as) = Spine8 (i + j) (shift0 i as)
  shift0 i (Cached8 j t v) = Cached8 (i + j) t (shift0 i v)

-- Auxiliary functions for cached normal forms
ignoreCache8 :: Val8 -> Val8
ignoreCache8 (Cached8 _ _ v) = v
ignoreCache8 v = v

makeCache8 :: Val8 -> Val8
makeCache8 v@(Cached8 _ _ _) = v
makeCache8 v = Cached8 0 (reify8 v) v

-- Weak normaliser for Val8
wnf8 :: Tm -> Subst8 -> Val8
wnf8 (Var n) sub = lookupSL sub n
wnf8 (Abs b) sub = Closure8 b sub
wnf8 (App f a) sub =
  let f' = wnf8 f sub
      ~a' = makeCache8 (wnf8 a sub)
  in case ignoreCache8 f' of
      Closure8 b sub' -> wnf8 b (Cons a' sub')
      Spine8 v as -> Spine8 v (Cons a' as)

-- Reify for Val8: produces Tm directly, applying shifts from cached forms
reify8 :: Val8 -> Tm
reify8 (Closure8 t sub) = Abs (reify8 (wnf8 t (Cons (Spine8 0 Nil) (shift0 1 sub))))
reify8 (Spine8 v as) = foldrSL (\a r -> r `App` reify8 a) (Var v) as
reify8 (Cached8 i t _) = shift 0 i t

-- Reflection for Val8
reflect8 :: Int -> SList Val8
reflect8 n = foldr (\x rs -> Cons (Spine8 x Nil) rs) Nil [0 .. n]

-- Normaliser nf8: no forceShifts needed since reify8 produces Tm directly
nf8 :: Tm -> Tm
nf8 t = let n = fv t in reify8 (wnf8 t (reflect8 n))

-- Test: nf8 should be fast on the original adversarial example
-- >>> fv (nf8 nbeAdversarialExploit)
-- 0
-- >>> nf7 nbeAdversarialExploit == nf8 nbeAdversarialExploit
-- True

-- maps n to \f. \x. f^n x
numeral :: Int -> Tm
numeral n = Abs (Abs (iterate (App (Var 1)) (Var 0) !! n))

-- targets normalizers that do eager shifting
deep :: Tm
deep = App (Abs (foldr (\_ t -> Abs t) (Var 50000) [1..50000])) (numeral 1000000)

-- maps t0 and t1 to \x. x t0 t1
pair :: Tm -> Tm -> Tm
pair t0 t1 = Abs (App (App (Var 0) t0) t1)

-- targets normalizers that destroy DAG sharing
sharing :: Tm
sharing = foldr (\_ t -> Abs t) (iterate (\t -> pair t t) (numeral 1000) !! 10) [1..10]

-- >>> nf7 deep == nf8 deep
-- True
-- >>> nf7 sharing == nf8 sharing
-- True