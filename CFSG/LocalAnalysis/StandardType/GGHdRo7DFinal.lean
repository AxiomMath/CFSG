module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DAssembly
import CFSG.LocalAnalysis.StandardType.GGHdRo7CFullWeyl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CGen
import CFSG.LocalAnalysis.StandardType.GGHdRo7CNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7CRefl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CSignX
import CFSG.LocalAnalysis.StandardType.GGHdRo7DAJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7DClassLarge
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFixBlock
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFixWeyl
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.LocalAnalysis.StandardType.GGHdRo7DKModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7DNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7DPlaneCount
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceU
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceV
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallFinal
import CFSG.LocalAnalysis.StandardType.GGHdRo7DStab
import CFSG.LocalAnalysis.StandardType.GGHdRo7NoTV
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUGraph
import CFSG.LocalAnalysis.StandardType.GGHdRo7XDatum

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

theorem ggResDCorank2Input_of_models (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hLM : DLModelLeaf) (hKM : DKModelLeaf) : GGResDCorank2Input :=
  ggResDCorank2Input_of_leaves hX hJ hRig hLB hKG d_normalizer_holds d_fixWeyl_holds
    d_reduceU_holds d_reduceV_holds d_classLarge_holds d_linSmall_holds c2_normalizer_holds
    c2_refl_holds su_graph_holds noTV_holds
    xDatumGraph_holds hLM d_lstab_holds hKM d_kstab_holds d_aj_holds

theorem ggResDCorank2Input_of_kModel (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hKM : DKModelLeaf) : GGResDCorank2Input :=
  ggResDCorank2Input_of_models hX hJ hRig hLB hKG
    (d_lModel_of_side hRig (d_sideCoord_of_frame d_frameOmega_holds)) hKM

theorem ggResDCorank2Input_proved (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput') :
    GGResDCorank2Input :=
  ggResDCorank2Input_of_kModel hX hJ hRig hLB hKG
    (d_kModel_of_side d_frameOmega_holds (d_jBlockOmega_of d_fixBlock_holds d_planeCount_holds)
      (d_sideCoord_of_frame d_frameOmega_holds))

end CFSG.StandardType.HdRo7D
