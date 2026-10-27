module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaFourMinusEightO1a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCTA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s15_ne_three_of_omegaMinus_four_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    s15 D.M V₀ V hV L ≠ 3 := by
  intro hs
  have hO1 : s15O1a D V :=
    s168e3_O1a_of_omegaMinus_four_eight_of_s_eq_three c hcomp hthin hs hrow
  obtain ⟨K, hK, hbar⟩ :=
    s16h_exists_cover D c.std.h127 c.std.h119 c.setting.hyp151.hyp125 hcomp
  have h3 : 3 ∣ Nat.card ↥(lBar V₀ V hV L) :=
    s16h_three_dvd_of_isOmegaMinus hcomp.2.2 hrow.1
  obtain ⟨t, htA, ht2, ht1, htr, hW⟩ := c.conc
  have hRank : CFSG.Open.pRank 3 K = 1 :=
    s16h_pRank_three_eq_one_of_thin_cover D c.setting hcomp hW hthin h3 hK hbar
  have hStrong3 :=
    s16h_stronglyEmbedded_of_pRank_one_cover D h82 c.setting
      (by omega : 2 < s15 D.M V₀ V hV L) hK hbar hRank
  exact (s15_Three_not_O1a_of_unique c.std.h61 c.std.h63 c.std.h127
    c.setting.hyp151.hyp125 (Or.inr hStrong3)) hO1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
