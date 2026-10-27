module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoEightMany
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoEightOneExclusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_case163_4_of_sl2_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    Case163_4 D V₀ V hV L := by
  have hs1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  rcases lt_or_eq_of_le hs1 with hs | hs
  · exact s168e3_case163_4_of_sl2_eight_of_one_lt_s c hcomp hthin hs hrow
  · exact (s168e3_false_of_sl2_eight_of_s_eq_one c hcomp hthin hs.symm hrow).elim

theorem s168e3_concl163F_of_sl2_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    Concl163F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (s168e3_case163_4_of_sl2_eight c hcomp hthin hrow)))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
