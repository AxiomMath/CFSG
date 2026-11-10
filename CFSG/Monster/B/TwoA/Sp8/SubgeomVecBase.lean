
module

public import CFSG.Monster.B.TwoA.Sp8.SubgeomLin
public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem deltaPair_45 : deltaPair 4 5 = deltaPair 2 4 + deltaPair 2 5 := by
  rw [deltaPair, deltaPair, deltaPair, ← Submodule.Quotient.mk_add]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem dhat_45 : dhat 4 5 = dhat 2 4 * dhat 2 5 := by
  have h : DQ (deltaPair 4 5) = DQ (deltaPair 2 5) * DQ (deltaPair 2 4) := by
    rw [deltaPair_45, DQ_add, DQ_comm]
  rw [dhat, dhat, dhat, dbar, dbar, dbar, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  change rhoEquiv (rMinus 4 5) = rhoEquiv (rMinus 2 4) * rhoEquiv (rMinus 2 5)
  rw [rMinus, rMinus, rMinus, h, rhoEquiv_mul]

theorem bvec_std : bvec 8 1 = Pi.single 0 1 ∧ bvec 8 2 = Pi.single 1 1 ∧
    bvec 8 4 = Pi.single 2 1 ∧ bvec 8 24 = Pi.single 3 1 + Pi.single 4 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext k <;> fin_cases k <;> rfl

def a8StdVec : ℕ → Submodule (ZMod 2) V8
  | 1 => span (ZMod 2) {bvec 8 1}
  | 2 => span (ZMod 2) {bvec 8 1, bvec 8 2}
  | 3 => span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4}
  | 4 => span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4, bvec 8 24}
  | _ => ⊥

theorem b0_apply (v w : V8) : b0 v w = ∑ i, ∑ j, v i * gram0 i j * w j :=
  Matrix.toBilin'_apply _ _ _

theorem stdGram_check : ∀ a ∈ [1, 2, 4, 24], ∀ c ∈ [1, 2, 4, 24],
    (∑ i : Fin 8, ∑ j : Fin 8, bvec 8 a i * gram0 i j * bvec 8 c j) = 0 := by
  decide +kernel

theorem stdVec_four_isotropic : IsTotallyIsotropic b0 (a8StdVec 4) := by
  refine isTotallyIsotropic_span fun s hs t ht => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rw [b0_apply]
  rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;>
    exact stdGram_check _ (by simp) _ (by simp)

end CFSG.Monster.B.TwoA.Sp8
