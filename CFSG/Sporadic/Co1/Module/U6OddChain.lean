module

public import Certificates.Data.CFSGNative.Co1.U6OddCheck
public import CFSG.Sporadic.Co1.Module.CoTwoDataInputs
public import CFSG.Sporadic.Co1.Module.OddNativeBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative Matrix
open CFSG.Sporadic.Co1.U6OddNative
open CFSG.Sporadic.Co1.Module (co1Act)
open CFSG.Sporadic.Co1.Module.CoTwo

attribute [local instance] Odd.vecAct Odd.vecSMul

variable {rr : ℕ → Array ℕ} {reg : ℕ → NativeSporadic.Co1}

theorem finite_co1 : Finite NativeSporadic.Co1 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)

@[expose] def vstab (v : Vec24) : Subgroup NativeSporadic.Co1 where
  carrier := {g | co1Act g v = v}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Odd.co1Act_mul', hh, hg]
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact Odd.co1Act_one' v
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    calc co1Act g⁻¹ v = co1Act g⁻¹ (co1Act g v) := by rw [hg]
      _ = v := by rw [← Odd.co1Act_mul', inv_mul_cancel, Odd.co1Act_one']

theorem mem_vstab {g : NativeSporadic.Co1} {v : Vec24} : g ∈ vstab v ↔ co1Act g v = v := Iff.rfl

@[expose] def chainGrp (u₁ u₂ : ℕ) (base : List ℕ) : ℕ → Subgroup NativeSporadic.Co1
  | 0 => vstab (toVecD 24 u₁) ⊓ vstab (toVecD 24 u₂)
  | n + 1 => chainGrp u₁ u₂ base n ⊓ vstab (toVecD 24 (base.getD n 0))

theorem mem_chainGrp {u₁ u₂ : ℕ} {base : List ℕ} {n : ℕ} {g : NativeSporadic.Co1} :
    g ∈ chainGrp u₁ u₂ base n ↔ co1Act g (toVecD 24 u₁) = toVecD 24 u₁ ∧
      co1Act g (toVecD 24 u₂) = toVecD 24 u₂ ∧
      ∀ j < n, co1Act g (toVecD 24 (base.getD j 0)) = toVecD 24 (base.getD j 0) := by
  induction n with
  | zero => simp [chainGrp, Subgroup.mem_inf, mem_vstab]
  | succ n ih =>
    simp only [chainGrp, Subgroup.mem_inf, ih, mem_vstab]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨h1, h2, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact h3 j h
      · rw [h]; exact h4
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2, fun j hj => h3 j (by omega)⟩, h3 n (by omega)⟩

theorem chainGrp_le_zero (u₁ u₂ : ℕ) (base : List ℕ) (n : ℕ) :
    chainGrp u₁ u₂ base n ≤ chainGrp u₁ u₂ base 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact inf_le_left.trans ih

end CFSG.Sporadic.Co1.Module.U6Odd
