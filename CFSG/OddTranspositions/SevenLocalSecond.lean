module

public import CFSG.OddTranspositions.SevenThreeTransitive
public import CFSG.OddTranspositions.AalphaCommute
public import CFSG.OddTranspositions.FaithfulBlocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mem_alpha_or_DalphaStar_of_commute (hC : HypothesisC D) {x : G}
    (hxD : x ∈ D) (hxd : Commute x hC.d) :
    x ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
  by_cases hxα : x ∈ hC.alpha
  · exact Or.inl hxα
  · right
    obtain ⟨γ, hγclass, hxγ⟩ :=
      exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hxD
    have hγα : γ ≠ hC.alpha := by
      intro h
      exact hxα (h ▸ hxγ)
    have hmem : γ ∈ perp D hC.alpha ∪ Aalpha D hC.alpha := by
      rw [perp_union_Aalpha_eq_blockClass]
      exact hγclass
    rw [Set.mem_union] at hmem
    rcases hmem with hγp | hγA
    · rcases mem_perp_iff.mp hγp with hγD | hγαeq
      · exact ⟨γ, hγD, hxγ⟩
      · exact absurd hγαeq hγα
    · exact absurd hxd (not_commute_of_mem_AalphaStar hC ⟨γ, hγA, hxγ⟩ hC.d_mem_alpha)

theorem DalphaStar_triangles_of_localSecond (hC : HypothesisC D)
    (hL : LocalSecond D) :
    ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha,
      ∀ t ∈ DalphaStar D hC.alpha,
        IsTriangle D x y t → orderOf (x * t * y) = 4 := by
  intro x hx y hy t ht htri
  obtain ⟨-, hxd⟩ := HypothesisC.DalphaStar_subset_commute hC hx
  obtain ⟨-, hyd⟩ := HypothesisC.DalphaStar_subset_commute hC hy
  obtain ⟨-, htd⟩ := HypothesisC.DalphaStar_subset_commute hC ht
  exact hL hC.d (hC.isBlock_alpha.subset hC.d_mem_alpha) x y t hxd hyd htd htri

end CFSG.OddTranspositions
