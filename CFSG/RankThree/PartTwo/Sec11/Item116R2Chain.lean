module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2K1
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusCfg
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CentrelessFacts
public import CFSG.RankThree.PartTwo.Sec11.Item116R1H1bCfg
public import CFSG.RankThree.PartTwo.Sec11.Item116R1SuzukiAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

namespace CFSG.RankThree.PartTwo.Sec11

theorem threeCoverModelA'_of_sectionFourHyp {Q : Type} [Group Q] [Finite Q] (hS : SectionFourHyp Q)
    (h : ThreeCoverModelA Q) : ThreeCoverModelA' Q := by
  rcases h with ⟨p, e, hp, he, hpi⟩ | h
  · haveI := hp
    exact Or.inl ⟨p, e, hp, he, Sec4.Census.two_or_le_two_of_isoLThreePi hS he hpi, hpi⟩
  · exact Or.inr h

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem twoStarAtCD_of_inputs_k1
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (hZ : ZElement) (hK2 : KFacts.KPSz) (hcl : CensusDCentreless) : ResidueR1TwoStarCD :=
  twoStarAtCD_of_zElement (item116P2b_of_core h45 hcore) hP2c h45 hZ
    (censusD_of h113 cyclicSylowThreeOutAbelian_holds hcl) (suzukiAutFacts_of_kpSz hK2)

end Certified

end CFSG.RankThree.PartTwo.Sec11

end
