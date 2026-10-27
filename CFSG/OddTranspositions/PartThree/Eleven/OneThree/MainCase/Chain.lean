module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Local

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

section NotCommute

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_not_commute_centSet (hC : HypothesisC D) {z v x : G}
    (hgen : ∀ d ∈ DalphaStar D hC.alpha, ∃ l ∈ localGroup (DalphaStar D hC.alpha) z,
      ∃ k ∈ kBlock D hC.alpha, d = l * (k * v * k⁻¹) * l⁻¹)
    (hxD : x ∈ D) (hxu : ¬ Commute hC.d x) (hxα : x ∉ hC.alpha)
    (hxK : ∀ k ∈ kBlock D hC.alpha, Commute x (k * v * k⁻¹)) :
    ∃ y ∈ centSet (DalphaStar D hC.alpha) z, ¬ Commute x y := by
  classical
  by_contra hcon
  have hxcent : ∀ y ∈ centSet (DalphaStar D hC.alpha) z, Commute x y := by
    intro y hy
    by_contra hxy
    exact hcon ⟨y, hy, hxy⟩
  have hxL : localGroup (DalphaStar D hC.alpha) z ≤
      Subgroup.centralizer ({x} : Set G) := by
    rw [localGroup, Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hxcent y hy).eq.symm
  have hxE : ∀ d ∈ DalphaStar D hC.alpha, Commute x d := by
    intro d hd
    obtain ⟨l, hl, k, hk, hdk⟩ := hgen d hd
    have hxl : Commute x l :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hxL hl)).symm
    have hxkv : Commute x (k * v * k⁻¹) := hxK k hk
    rw [hdk]
    exact (hxl.mul_right hxkv).mul_right hxl.inv_right
  have hxN : x ∈ Subgroup.normalizer hC.E := by
    refine Subgroup.centralizer_le_normalizer hC.E ?_
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : n ∈ DalphaStar D hC.alpha := by
      rw [hC.DalphaStar_alpha]
      exact hn
    exact (hxE n hn').eq.symm
  have hxnotE : x ∉ hC.E := by
    intro hxE'
    have hxE'' : x ∈ DalphaStar D hC.alpha := by
      rw [hC.DalphaStar_alpha]
      exact hxE'
    exact hxu (hC.DalphaStar_subset_commute hxE'').2.symm
  exact hxα (by
    rw [hC.alpha_eq_normSet_diff]
    exact ⟨⟨hxD, hxN⟩, hxnotE⟩)

end NotCommute

section Chain

variable {G : Type} [Group G] {D : Set G}

theorem exists_conj_localGroup_of_chain (hD : IsOddTransp D) {z u x y v l : G}
    (hu : u ∈ centSet D z) (hx : x ∈ centSet D z) (hy : y ∈ centSet D z)
    (hux : ¬ Commute u x) (hxy : ¬ Commute x y) (hl : l ∈ localGroup D z)
    (hlyv : l * y * l⁻¹ = v) : ∃ g ∈ localGroup D z, g * u * g⁻¹ = v := by
  obtain ⟨g1, hg1, hg1'⟩ := hD.exists_conj hu.1 hx.1 hux
  obtain ⟨g2, hg2, hg2'⟩ := hD.exists_conj hx.1 hy.1 hxy
  have hsub1 : ({u, x} : Set G) ⊆ centSet D z := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hx
  have hsub2 : ({x, y} : Set G) ⊆ centSet D z := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hx
    · exact hy
  have hg1L : g1 ∈ localGroup D z := Subgroup.closure_mono hsub1 hg1
  have hg2L : g2 ∈ localGroup D z := Subgroup.closure_mono hsub2 hg2
  refine ⟨l * g2 * g1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hg2L) hg1L, ?_⟩
  have hconj : (l * g2 * g1) * u * (l * g2 * g1)⁻¹ = l * y * l⁻¹ := by
    calc (l * g2 * g1) * u * (l * g2 * g1)⁻¹
        = l * (g2 * (g1 * u * g1⁻¹) * g2⁻¹) * l⁻¹ := by group
      _ = l * (g2 * x * g2⁻¹) * l⁻¹ := by rw [hg1']
      _ = l * y * l⁻¹ := by rw [hg2']
  exact hconj.trans hlyv

end Chain

end CFSG.OddTranspositions.PartThree.ElevenThree
