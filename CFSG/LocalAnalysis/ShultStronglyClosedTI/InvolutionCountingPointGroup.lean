module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingFixedPoints
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem exists_ne_of_one_lt_card {X : Type*} (hX : 1 < Nat.card X) (x : X) : ∃ y : X, y ≠ x := by
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hX
  exact exists_ne x

theorem mem_and_ne_one_of_sdiff_eq_conjugacyWithin {Q : Subgroup G} {z : G} {α : Ω}
    (hQz : (Q : Set G) \ {1} = conjugacyWithin (MulAction.stabilizer G α) z) :
    z ∈ Q ∧ z ≠ 1 := by
  have hz : z ∈ conjugacyWithin (MulAction.stabilizer G α) z := ⟨1, by simp⟩
  rw [← hQz] at hz
  exact ⟨hz.1, hz.2⟩

theorem mem_of_isConj_of_smul_eq_self {Q : Subgroup G} {z x : G} {α : Ω}
    (hQz : (Q : Set G) \ {1} = conjugacyWithin (MulAction.stabilizer G α) z)
    (hzfix : ∀ β : Ω, z • β = β ↔ β = α) (hx : IsConj z x) (hxα : x • α = α) : x ∈ Q := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hx
  have hkα : k • α = α := ((conj_smul_eq_self_iff hzfix k α).mp hxα).symm
  have hmem : k * z * k⁻¹ ∈ conjugacyWithin (MulAction.stabilizer G α) z :=
    ⟨⟨k⁻¹, inv_mem (MulAction.mem_stabilizer_iff.mpr hkα)⟩, by simp⟩
  rw [← hQz] at hmem
  exact hmem.1

end CFSG.ShultStronglyClosedTI.InvolutionCounting
