module

public import CFSG.RankThree.PartOne.SEITZ2.G2Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartOne.SEITZ2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form
  entrywiseFixedGroup_eq_fixedFieldImage)


section Main


theorem fieldAutData_G2_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (hpair : ∀ (σ : K ≃+* K), orderOf σ = p → ∀ g : adjointGroup .G2 K,
      (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ →
      Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
        ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ ∨
        ¬ p ∣ Nat.card (g2Fixed σ)) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have : Fact p.Prime := ⟨hp⟩
  refine fieldAutData_of_standard (MulAut.conj : adjointGroup .G2 K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut .G2 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane hp hf hK E hEc
  · intro α hα
    obtain ⟨h0, σ, hσ, h⟩ := exists_conj_entrywise hp hf hK α hα
    refine ⟨(MulAut.conj h0)⁻¹, ?_, entrywiseAdjointAut .G2 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · exact (MulAut.conj : adjointGroup .G2 K →* MulAut _).range.inv_mem ⟨h0, rfl⟩
    · rw [← h]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_entrywise_eq, fixedSubgroup_entrywise_eq]
    exact g2Fixed_congr (fixedField_eq_of_orderOf Nat.prime_two (by omega) hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    rw [fixedSubgroup_entrywise_eq] at hx hc
    exact eq_one_of_central_g2Fixed σ hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d ⟨g, rfl⟩ hne
    rw [fixedSubgroup_entrywise_eq] at hne ⊢
    exact hpair σ hσ g hne

end Main

end CFSG.RankThree.PartTwo.Sec4.E27
