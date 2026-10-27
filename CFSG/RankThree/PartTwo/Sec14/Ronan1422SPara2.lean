module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SPoint
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

namespace Pt

theorem isHyperplane_B (h : Pt A c L) : IsHyperplane A (A ⊓ L) := by
  refine ⟨inf_le_left, ?_⟩
  rw [h.std.isE27.2, h.card_B]

theorem lB_eq_bot (h : Pt A c L) : lB A (A ⊓ L) = ⊥ := by
  refine CFSG.RankThree.PartTwo.Sec14.lB_eq_bot fun b d L' hcfg => ?_
  obtain ⟨hB, hbΩ, -⟩ := hcfg
  have hbB : b ∈ A ⊓ L := hB ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  rw [h.omega] at hbΩ
  obtain ⟨w, hw, hwb⟩ := hbΩ
  have hwc : w * c * w⁻¹ ∈ A ⊓ L := by
    have h1 : w * c * w⁻¹ ∈ Subgroup.zpowers b := by
      rw [hwb]
      exact ⟨c, Subgroup.mem_zpowers c, rfl⟩
    exact (Subgroup.zpowers_le.mpr hbB) h1
  have hcB : c ∈ A ⊓ L := by
    have := (Subgroup.mem_normalizer_iff.mp (h.wb (inv_mem hw)) _).mp hwc
    simpa [mul_assoc] using this
  exact h.not_mem hcB.2

theorem le_pPrimeCoreOf_centralizer_B (h : Pt A c L) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hUB : U ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) :
    U ≤ pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) := by
  set B := A ⊓ L with hBdef
  set CB := Subgroup.centralizer (B : Set G) with hCB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := (h.iq U hU2 hAU).2 B h.isHyperplane_B
  have hUinf : U ⊓ CB = U := inf_eq_left.mpr hUB
  rw [hUinf, qBound, h.lB_eq_bot, sup_bot_eq] at hQ
  have hXB : xA A ≤ CB := by
    refine (pPrimeCoreOf_le 3 _).trans ?_
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
  have hYn : ((pPrimeCoreOf 3 CB).subgroupOf CB).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pPrimeCoreOf_le 3 CB)).mpr
      (le_normalizer_pPrimeCoreOf 3 CB)
  have hXodd : (Nat.card (xA A)).Coprime 2 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h.x_odd)
  exact CFSG.AGLEmbedding.le_of_le_sup_of_coprime_card_of_le hUB (pPrimeCoreOf_le 3 CB) hXB
    hYn hU2 hXodd hQ

end Pt

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
