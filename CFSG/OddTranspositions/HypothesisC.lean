module

public import CFSG.OddTranspositions.BlockTransitive
public import CFSG.OddTranspositions.BlockCover

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {D : Set G}

theorem reach_of_not_disconnected (h : ¬ Disconnected D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) : Reach D a b := by
  by_contra hab
  exact h ⟨a, ha, b, hb, hab⟩

structure HypothesisC (D : Set G) where
  setup : Asc72.Setup G D
  conn : ¬ Disconnected D
  d : G
  hd : d ∈ D
  E : Set G
  hE : IsMaxOrbit D d E

namespace HypothesisC

variable (hC : HypothesisC (G := G) D)

@[expose] def alpha : Set G := normSet D hC.E \ hC.E

theorem alpha_eq_normSet_diff : hC.alpha = normSet D hC.E \ hC.E := rfl

theorem d_mem_alpha : hC.d ∈ hC.alpha :=
  OddLocal.self_mem_F hC.setup.normal hC.hd hC.hE

theorem isMaxBlock_alpha : IsMaxBlock D hC.alpha :=
  isMaxBlock_normSet_diff hC.setup
    (fun a ha b hb => reach_of_not_disconnected hC.conn ha hb) hC.hd hC.hE

theorem isBlock_alpha : IsBlock D hC.alpha := IsMaxBlock.isBlock hC.isMaxBlock_alpha

theorem DalphaStar_alpha : DalphaStar D hC.alpha = hC.E :=
  DalphaStar_eq_maxOrbit hC.setup hC.conn hC.hd hC.hE

theorem Halpha_transitive :
    ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha,
      ∃ h ∈ Halpha D hC.alpha, h * x * h⁻¹ = y :=
  Halpha_transitive_DalphaStar_of_isMaxOrbit hC.setup hC.conn hC.hd hC.hE

theorem normalizer_transitive :
    ∀ β ∈ Dalpha D hC.alpha, ∀ γ ∈ Dalpha D hC.alpha,
      ∃ g ∈ Subgroup.normalizer hC.alpha, (fun x => g * x * g⁻¹) '' β = γ :=
  normalizer_transitive_Dalpha_of_isMaxOrbit hC.setup hC.conn hC.hd hC.hE

theorem DalphaStar_subset_commute (hC : HypothesisC (G := G) D) :
    DalphaStar D hC.alpha ⊆ {x | x ∈ D ∧ Commute x hC.d} := by
  intro x hx
  have hxE : x ∈ hC.E := by rwa [hC.DalphaStar_alpha] at hx
  exact ⟨(OddLocal.subset_commSet hC.setup.normal hC.hE hxE).1,
    (OddLocal.subset_commSet hC.setup.normal hC.hE hxE).2.1⟩

theorem AalphaStar_eq_diff_alpha (hC : HypothesisC (G := G) D) :
    AalphaStar D hC.alpha = {x | x ∈ D ∧ ¬ Commute x hC.d} \ hC.alpha := by
  ext x
  constructor
  · rintro ⟨β, hβ, hxβ⟩
    obtain ⟨hβclass, hβnot⟩ := mem_Aalpha_iff.mp hβ
    have hxD : x ∈ D :=
      (AalphaStar_subset hC.setup.normal hC.isBlock_alpha) ⟨β, hβ, hxβ⟩
    have hxα : x ∉ hC.alpha := by
      intro hx
      exact (Set.disjoint_left.mp (disjoint_alpha_AalphaStar hC.isBlock_alpha) hx)
        ⟨β, hβ, hxβ⟩
    refine ⟨⟨hxD, ?_⟩, hxα⟩
    intro hcomm
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβclass
    have hβne : β ≠ hC.alpha := fun h => hβnot (mem_perp_iff.mpr (Or.inr h))
    have hgene : (fun y => g * y * g⁻¹) '' hC.alpha ≠ hC.alpha := by
      rw [← hg]
      exact hβne
    have hbimg : x ∈ (fun y => g * y * g⁻¹) '' hC.alpha := hg ▸ hxβ
    have hall := commute_block_of_mem_apply hC.setup.normal hC.setup.oddT hC.isBlock_alpha
      hgene hC.d_mem_alpha hbimg hcomm.symm
    have hβD : β ⊆ D := by
      rw [hg]
      rintro b ⟨a, ha, rfl⟩
      exact hC.setup.normal g a (hC.isBlock_alpha.subset ha)
    have hDalpha : β ∈ Dalpha D hC.alpha := by
      refine ⟨hβclass, hβD, hβne, ?_⟩
      intro a ha b hb
      rw [hg] at hb
      exact hall a ha b hb
    exact hβnot (mem_perp_iff.mpr (Or.inl hDalpha))
  · rintro ⟨⟨hxD, hnc⟩, hxα⟩
    obtain ⟨β, hβclass, hxβ⟩ :=
      exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hxD
    have hβne : β ≠ hC.alpha := fun h => hxα (h ▸ hxβ)
    have hβnot : β ∉ perp D hC.alpha := by
      rw [mem_perp_iff]
      rintro (hDα | hα)
      · obtain ⟨-, -, -, hcomm⟩ := mem_Dalpha_iff.mp hDα
        exact hnc (hcomm hC.d hC.d_mem_alpha x hxβ).symm
      · exact hβne hα
    exact ⟨β, ⟨hβclass, hβnot⟩, hxβ⟩

theorem eq_alpha_union (hC : HypothesisC (G := G) D) :
    D = hC.alpha ∪ DalphaStar D hC.alpha ∪ AalphaStar D hC.alpha := by
  ext x
  constructor
  · intro hxD
    by_cases hxα : x ∈ hC.alpha
    · exact Or.inl (Or.inl hxα)
    · obtain ⟨β, hβclass, hxβ⟩ :=
        exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hxD
      by_cases hβDα : β ∈ Dalpha D hC.alpha
      · exact Or.inl (Or.inr ⟨β, hβDα, hxβ⟩)
      · refine Or.inr ⟨β, ⟨hβclass, ?_⟩, hxβ⟩
        rw [mem_perp_iff]
        rintro (h | h)
        · exact hβDα h
        · exact hxα (h ▸ hxβ)
  · rintro ((hxα | hxE) | hxA)
    · exact hC.isBlock_alpha.subset hxα
    · exact DalphaStar_subset hC.isBlock_alpha hxE
    · exact (AalphaStar_subset hC.setup.normal hC.isBlock_alpha) hxA

end HypothesisC

end CFSG.OddTranspositions
