module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Common
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

namespace Row18

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

section HSData

variable {X : Type} [Group X]

theorem card_of_equiv_HS
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .HS)) : Nat.card X = 2 ^ 9 * 86625 := by
  obtain ⟨e⟩ := hX
  have e' : X ≃* NativeSporadic.HS := e
  rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.HS.card_HS]
  norm_num

theorem isSimpleGroup_of_equiv_HS
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .HS)) : IsSimpleGroup X := by
  obtain ⟨e⟩ := hX
  have e' : X ≃* NativeSporadic.HS := e
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e'

theorem eq_one_of_central_of_equiv_HS
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .HS)) {z : X} (hz : ∀ a, z * a = a * z) :
    z = 1 := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [card_of_equiv_HS hX]; norm_num)
  have := isSimpleGroup_of_equiv_HS hX
  refine eq_one_of_central_of_simple (exists_noncomm_of_simple_not_prime ?_) hz
  rw [card_of_equiv_HS hX]
  norm_num

end HSData

section Lemma2Inputs

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem center_trivial_HS {N : Subgroup K}
    (hN : Nonempty (↥N ≃* NativeSporadic.Carrier .HS)) :
    ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1 := by
  intro z hz hzc
  have := eq_one_of_central_of_equiv_HS hN (z := ⟨z, hz⟩) (fun a => Subtype.ext (hzc a a.2))
  exact congrArg Subtype.val this

theorem three_conj_inner_HS
    {N : Subgroup K} [N.Normal]
    (hN : Nonempty (↥N ≃* NativeSporadic.Carrier .HS)) :
    ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹ := by
  obtain ⟨e⟩ := hN
  refine three_conj_inner_of_outer_le_two ?_
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two

end Lemma2Inputs

end Row18

end Stellmacher.L3YC

end CFSG.Quasithin
