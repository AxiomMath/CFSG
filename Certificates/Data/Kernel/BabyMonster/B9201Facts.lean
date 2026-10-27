module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Logic.Function.Basic
public import CFSG.Sporadic.Bridge.BData

public section

namespace CFSG.KC.BM.B9201

open CFSG.Monster.B.Primes.Native

variable {M : Type*} [Monoid M]

@[expose] def insStepM (r : ℕ → M) : Ins → ℕ → M
  | .mu i j k => Function.update r k (r i * r j)
  | .iv _ _ => r
  | .pwr e i k => Function.update r k (r i ^ e)

@[expose] def runM (prog : List Ins) (a b : M) : ℕ → M :=
  prog.foldl insStepM fun i => if i = 1 then a else if i = 2 then b else 1

@[expose] def tM (a b : M) (k : ℕ) : M := runM CFSG.Sporadic.Bridge.B.bProg a b
  (CFSG.Sporadic.Bridge.B.bTreg k)

@[expose] def lp (t : ℕ → M) (l : List ℕ) : M := (l.map t).prod

@[expose] def chain2 : List ℕ := [0, 1, 2, 3, 4, 8, 9, 10]

@[expose] def rT (t : ℕ → M) : M := lp t [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def rqT (t : ℕ → M) : M := lp t chain2

@[expose] def sT (t : ℕ → M) : M := lp t [4, 8, 9, 10]

@[expose] def apT (t : ℕ → M) : M := (rT t ^ 7 * sT t) ^ 15

@[expose] def hT (t : ℕ → M) : M := (sT t * rT t) ^ 10

@[expose] def RelsT (t : ℕ → M) : Prop :=
  t 0 * t 0 = 1 ∧ (t 0 * t 1) ^ 3 = 1 ∧
    (∀ j ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10], t 0 * t j = t j * t 0) ∧
    (∀ i < 7, rT t * t i = t (i + 1) * rT t) ∧
    (∀ i < 7, rqT t * t (chain2.getD i 0) = t (chain2.getD (i + 1) 0) * rqT t) ∧
    t 5 * t 8 = t 8 * t 5 ∧ t 5 * (t 9 * t 10) = t 9 * t 10 * t 5 ∧
    t 6 * t 7 * t 8 = t 8 * (t 6 * t 7) ∧ t 6 * t 7 * (t 9 * t 10) = t 9 * t 10 * (t 6 * t 7) ∧
    lp t [4, 3, 2, 4, 5, 6, 4, 8, 9] ^ 10 = 1 ∧ lp t [4, 3, 2, 5, 6, 7, 8] ^ 9 = 1 ∧
    lp t [4, 3, 2, 5, 8, 9, 10] ^ 9 = 1

@[expose] def B9201Facts (a b : M) : Prop :=
  ∃ t : ℕ → M, (∀ k < 11, tM a b k = t k) ∧ RelsT t ∧
    ∃ G Gi : M, b * G = G * (t 0 * t 1) ∧ a * (G * hT t) = G * hT t * apT t ∧ G * Gi = 1

end CFSG.KC.BM.B9201

end
