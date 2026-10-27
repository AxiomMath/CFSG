module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialRankFinal
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_three_of_isExtraspecialExpP_le
    {Q H : Subgroup G}
    (hQH : Q ≤ H)
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    2 ≤ CFSG.Open.pRank 3 H := by
  classical
  let QH : Subgroup ↥H := Q.subgroupOf H
  have hQH' : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥QH := by
    unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ
    obtain ⟨hcard, hexp, hcomm, hcenter⟩ := hQ
    let e : ↥QH ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQH
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Nat.card_congr e.toEquiv).trans hcard
    · exact (Monoid.exponent_eq_of_mulEquiv e).trans hexp
    · have h := congrArg (Subgroup.map (e.symm : ↥Q →* ↥QH)) hcomm
      rw [_root_.map_commutator_eq ↥Q (e.symm : ↥Q →* ↥QH),
        MonoidHom.range_eq_top_of_surjective (e.symm : ↥Q →* ↥QH) e.symm.surjective,
        Subgroup.map_center_eq e.symm] at h
      exact h
    · rw [← Subgroup.card_map_of_injective (K := Subgroup.center ↥QH) (f := (e : ↥QH →* ↥Q)) e.injective,
        Subgroup.map_center_eq e]
      exact hcenter
  have htop : Subgroup.centralizer ((⊥ : Subgroup ↥H) : Set ↥H) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Subgroup.coe_bot]
    exact Set.singleton_subset_iff.mpr (Subgroup.one_mem _)
  have hQX : QH ≤ Subgroup.centralizer ((⊥ : Subgroup ↥H) : Set ↥H) := by
    rw [htop]
    exact le_top
  have h := two_le_pRank_three_centralizer_of_isExtraspecialExpP_exists
    (G := ↥H) (Q := QH) (X := ⊥) hQH' hQX
  rw [htop] at h
  rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
