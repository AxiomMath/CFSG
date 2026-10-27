module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09s
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5Proof
import CFSG.RankThree.PartTwo.KFacts.KS44Sz
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import Certificates.Certificate43
public import CFSG.CGT.PushingUpLit.CGT6.SixThreeCore
import CFSG.LocalAnalysis.UniquenessCase.UC6R2
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5Proof
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R99
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5Proof
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.SixThree
public import CFSG.CGT.PushingUpLit.SixThreeC
public import CFSG.CGT.PushingUpLit.SixThreeSylow
public import CFSG.CGT.PushingUpLit.SixThreeV
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def R913A5S (D : Data G) : Prop :=
  ∀ Y H D₃ S : Subgroup G, Hyp97 D Y H D₃ S → IsAlt (Bar2 (Opp 3 Y)) 5 →
    CFSG.ABGLocalTools.IsSylowOf 2 S H →
    H = I9 H ⊔ (H ⊓ D.M) ∨ LieModel (Lbar9 Y H) .PSL 3 5 1

theorem r917A5_of_r913A5S
    (D : Data G) (h912 : R912A5 D) (h913 : R913A5S D) : R917A5 D := by
  intro Y H D₃ S hY hA5 hR hSM
  rcases h913 Y H D₃ S hY hA5 (h912 Y H D₃ S hY hA5 hR).1 with h | hLie
  · exact h.trans (sup_comm _ _)
  · exact eq_sup_I9_of_lie hY hA5 hR hSM (h912 Y H D₃ S hY hA5 hR).1 hLie

theorem r923K1_holds_of_r913A5S
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hSch : KFactCatalogSchreier)
    (hKF : KFactShape92NoFaithfulA5) (h63 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore)
    (D : Data G) (h640 : UC6.R6_40_1 D) (h92 : R92 D) (h913 : R913A5S D) : R923K1 D :=
  r923K1_holds hG3 hSch hKF D h92
      (r922A5_of_r917A5 CFSG.RankThree.PartTwo.KFacts.kpSz D
          (r912A5_of_inputs D (r99_holds D) (r910_holds D) (r911_of h63 D h640) (r9R5_holds D))
          (r917A5_of_r913A5S D
              (r912A5_of_inputs D (r99_holds D) (r910_holds D) (r911_of h63 D h640) (r9R5_holds D))
              h913))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
