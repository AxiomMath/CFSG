module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Push
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Five
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89OmegaY
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89OmegaOfY
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89WeakClosed
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Act
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Split
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89OddCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Module
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89QGroupA
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89QGroupB
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Dickson
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89O2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Chief
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89J2Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Mod2
public import Certificates.Certificate2326
public import Certificates.Certificate3951
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate117
public import Certificates.Certificate110
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate120
public import Certificates.Certificate10019
public import Certificates.Certificate14984
public import Certificates.Certificate1491001
public import Certificates.Certificate1491002
public import Certificates.Certificate1491003
public import Certificates.Certificate1491004
public import Certificates.Certificate1491005
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89J2AutCoreProof
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KMod2Proof
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCharProof
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89G2Five
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.LC_generalized_fitting_self_centralizing
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import Certificates.Kernel.J4Count.Prim
import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R71 R72)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

theorem r889_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (hsig3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaThree D) (h71 : R71 D) (h72 : R72 D)
    (h6_14 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_14 D)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.K332Z3)
    (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch) (h869M : R869M D) (h869N : R869N D)
    (h881 : R881 D) (h882 : R882 D) (h885 : R885 D) (h886 : R886 D) (h887 : R887 D)
    (h888 : R888 D) (hAlt6 : FiveEmbeddedNoAlt6) : R889 D := by
  have hJ2 : J2AutCore := j2AutCore_holds
  have hMod2 : Alt6ModTwoCore := alt6ModTwoCore_holds
  have hChar : Alt6CharCore := alt6CharCore_holds
  have hG2 : G2FiveRankCore := g2FiveRankCore_holds
  have hFacts : AllFacts889 D := s889_facts D h882 h885 h886
  have hrank : Rank889 D := s889_rank D hsig3 h885
  have hY := s889_y D hrank h869N h881 h882 h885 h886 h888
  have hOmega : S889Omega D := s889_omega_of_y D hSg h6_14 h885 h886 h887 hY
  have hFive : S889Five D := s889_five_of_facts D hSg h71 h72 h885 hAlt6 hFacts
  have hWC : S889WeakClosed D := s889_weak_closed D h882 h885 h886 h887 h888
  have hSplit : S889Split D :=
    s889_split D hSg hK332 hSch hG2 h885 h887 hrank hFacts hFive s889_act hWC
  have hOdd : S889OddCore D := s889_odd_core D hSg h885 hFacts hFive
  have hO2 : S889O2 D :=
    s889_o2_of_parts D hSg h885 h887 hrank hFacts hSplit hOdd (s889_module hChar) s889_qmin
      s889_qrank (s889_dickson s889_act)
  have hChief : S889Chief D :=
    s889_chief_of_parts D hSg h885 h887 hrank hFacts hSplit hOdd s889_qmin s889_qrank
      (s889_dickson s889_act)
  exact r889_of_parts D h881 h882 h885 h869M hOmega hO2 hChief
    (s889_j2aut D h882 h885 hFacts hJ2) (s889_mod2 D hSg h885 h887 hFacts hMod2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
