module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight61Conclusion
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_of_extraspecial_left_of_pRank_le_three
    {P Q C : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hQP : Q ≤ P) (hCP : C ≤ P) (hP3 : IsPGroup 3 P)
    (hPrank : CFSG.Open.pRank 3 P ≤ 3)
    (hcomm : ∀ q ∈ Q, ∀ c ∈ C, q * c = c * q)
    (hint : Q ⊓ C = ⊥) :
    IsCyclic C := by
  have hQrank : 2 ≤ CFSG.Open.pRank 3 Q :=
    two_le_pRank_three_of_isExtraspecialExpP_le (G := G) (Q := Q) (H := Q) le_rfl hQ
  have hadd := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
    (Y := G) (q := 3) (A := Q) (B := C) Nat.prime_three hcomm hint
  have hsup : CFSG.Open.pRank 3 (Q ⊔ C) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (sup_le hQP hCP)).trans hPrank
  have hCrank : CFSG.Open.pRank 3 C ≤ 1 := by omega
  refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
    (Γ := ↥C) (p := 3) Nat.prime_three (by norm_num) (hP3.to_le hCP) ?_
  rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
