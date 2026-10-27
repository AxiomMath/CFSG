module

public import CFSG.RankThree.PartOne.S11d.ThreeCompAssemble4
public import CFSG.RankThree.PartOne.S11d.ThreeCompAssemble3
public import CFSG.RankThree.PartOne.S11d.HighRankAll
public import CFSG.RankThree.PartOne.S11d.LowRankVacuous
public import CFSG.RankThree.PartOne.S11d.ThreeCompEasy
public import CFSG.RankThree.PartOne.TCX.G2.FixedRank
public import CFSG.RankThree.PartOne.TCX.Tri.FixedRank
public import CFSG.RankThree.PartOne.TCX.Ree.FixedRank
public import CFSG.RankThree.PartOne.S11d.PSUThreeComp
public import CFSG.RankThree.PartOne.S11d.PSUThreeA
public import CFSG.RankThree.PartOne.TCP.AlFinal
public import CFSG.RankThree.PartOne.TCO.OmegaMinusFour

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.RankThree.PartOne.TCX CFSG.RankThree.PartOne.FieldFix

theorem threeComponents_of_allTagsR
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hTE : TwoExcPair)
    (h3D4 : ThreeCompT .trialityD4) (h2F4 : ThreeCompT .twistedF4) : ThreeComponents := by
  have hF : ∀ t, TagFixedFacts t :=
    tagFixedFacts_all chevalleySubfieldNonLocalized largeReeTitsNonLocalized
  have hBt : ∀ t, ThreeCompBL t := by
    intro t
    cases t
    · exact (threeCompT_PSL (hF .PSL)).toB.toL
    · exact threeCompBL_PSU
    · exact threeCompBL_PSp
    · exact threeCompT_POmegaOdd.toB.toL
    · exact threeCompBL_POmegaPlus
    · exact threeCompBL_POmegaMinus
    · exact TCX.G2.threeCompT_G2.toB.toL
    · exact threeCompBL_F4
    · exact threeCompBL_E6
    · exact threeCompBL_E7
    · exact threeCompBL_E8
    · exact threeCompBL_twistedE6
    · exact h3D4.toB.toL
    · exact threeCompT_Sz.toB.toL
    · exact threeCompT_twistedG2.toB.toL
    · exact h2F4.toB.toL
    · exact threeCompT_Tits.toB.toL
  have hT : ∀ t, FixedRankTL t := by
    intro t
    cases t
    · exact (fixedRankT_PSL (hF .PSL)).toL
    · exact fixedRankTL_PSU
    · exact fixedRankTL_PSp
    · exact fixedRankT_POmegaOdd.toL
    · exact fixedRankTL_POmegaPlus
    · exact fixedRankTL_POmegaMinus
    · exact TCX.G2.fixedRankT_G2.toL
    · exact fixedRankTL_F4
    · exact fixedRankTL_E6
    · exact fixedRankTL_E7
    · exact fixedRankTL_E8
    · exact fixedRankTL_twistedE6
    · exact TCX.Tri.fixedRankT_trialityD4.toL
    · exact fixedRankT_Sz.toL
    · exact fixedRankT_twistedG2.toL
    · exact TCX.Ree.fixedRankT_twistedF4.toL
    · exact fixedRankT_Tits.toL
  have hA : ∀ t, ThreeCompAL t := by
    intro t
    cases t
    · exact (threeCompT_PSL (hF .PSL)).toAL
    · exact threeCompAL_PSU_of_survivor psuThreeA
    · exact threeCompAL_PSp
    · exact threeCompT_POmegaOdd.toAL
    · exact threeCompAL_of_highRank (not_lowRank_highTags _ (Or.inl rfl))
    · exact fun T _ _ p hp hp5 hLR2 h2 n f₀ _ hM hlow =>
        (false_of_pOmegaMinus_four hp hp5 hLR2 h2 hM hlow).elim
    · exact TCX.G2.threeCompT_G2.toAL
    · exact threeCompAL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inl rfl)))
    · exact threeCompAL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inl rfl))))
    · exact threeCompAL_of_highRank
        (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact threeCompAL_of_highRank
        (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact threeCompAL_of_highRank
        (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    · exact h3D4.toAL
    · exact threeCompT_Sz.toAL
    · exact threeCompT_twistedG2.toAL
    · exact h2F4.toAL
    · exact threeCompT_Tits.toAL
  exact threeComponents_of_tagsLR KEXC.oddCenterLie_holds hF hBt hGA TCX.highRankFalse_all hTE
    (fieldFixedRankL_of_tags KEXC.oddCenterLie_holds hT hGA TCX.highRankFalse_all)
    (lieFieldOnComponentR_of_tags KEXC.oddCenterLie_holds hGA TCX.highRankFalse_all hA)

end CFSG.RankThree.PartOne
