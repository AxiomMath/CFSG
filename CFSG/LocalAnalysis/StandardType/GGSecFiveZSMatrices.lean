module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Matrix.Diagonal

@[expose] public noncomputable section

namespace CFSG.StandardType.ZS

local instance factPrimeThirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

def piMat {n : ℕ} (i j : Fin n) (α : ZMod 13) : Matrix (Fin n) (Fin n) (ZMod 13) :=
  fun r c => if r = i ∧ c = j then α else if r = j ∧ c = i then α⁻¹
    else if r = c ∧ r ≠ i ∧ r ≠ j then 1 else 0

def aMat : Matrix (Fin 4) (Fin 4) (ZMod 13) :=
  fun r c => (if r = c then 1 else 0) - 7

def herRefl {n : ℕ} (v vb : Fin n → ZMod 13) : Matrix (Fin n) (Fin n) (ZMod 13) :=
  1 - (2 / (∑ i, v i * vb i)) • Matrix.of fun r c => v r * vb c

def om : ZMod 13 := 3

end CFSG.StandardType.ZS
