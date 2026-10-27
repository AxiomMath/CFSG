module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem exists_isElemAbelian_card_nine_le_centralizer
    {G : Type} [Group G] [Finite G] {L Q P Y : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L))
    (hYP : Y ≤ P) (hYc : Nat.card Y = 3) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≤ Subgroup.centralizer (Y : Set G) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  by_cases hYQ : Y ≤ Q
  · have hrank : 2 ≤ CFSG.Open.pRank 3 Q := by
      rw [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
        Nat.prime_three hQ]
      exact hLrank
    obtain ⟨E, hYE, hEQ, hEea, hEcard⟩ :=
      CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
        hQ.isPGroup hrank hYQ hYc
    exact ⟨E, hEQ.trans hQ.le, fun g hg => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (((CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).mp hEea).1 g hg y
        (hYE hy)).symm, hEea, by rw [hEcard]; norm_num⟩
  · obtain ⟨E, hEinf, hEea, hEcard⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 3) (k := 2)
        Nat.prime_three (H := Subgroup.centralizer (Y : Set G) ⊓ L) (h61 Y hYP hYc hYQ)
    exact ⟨E, hEinf.trans inf_le_right, hEinf.trans inf_le_left, hEea,
      by rw [hEcard]; norm_num⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
