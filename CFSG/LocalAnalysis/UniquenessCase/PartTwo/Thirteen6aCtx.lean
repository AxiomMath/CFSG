module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Ctx (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop where
  thin : ThinList13
  cyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian
  ext : DataExt D
  sg : UC6S846.SigmaStd D
  s13 : Setting13 D
  r82 : F08.R82 D
  r76 : F07.R76Sig D
  r614 : UC6.R6_14 D
  r638 : UC6.R6_38 D
  shape : ∀ L ∈ calC D.M, ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n)
  r1 : S17.R17_1At D V₀ V hV
  r22 : S17.R17_2_2At D V₀ V hV
  r23 : S17.R17_2_3At D V₀ V hV
  r332 : S17.R17_33_2At D V₀ V
  r333 : S17.R17_33_3At D V₀ V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
