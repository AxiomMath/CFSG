module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Assembly
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3AJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Model
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Normalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3PWeyl
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3RankLower
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3RankUpper
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3ReduceM
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3ReduceV
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Refl
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3ReflFix
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SideMat
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SideTor
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallAssembly
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallReal
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallNorm
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallWit
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallE8
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Stab
import CFSG.LocalAnalysis.StandardType.GGHdRo7DClassLarge
import CFSG.LocalAnalysis.StandardType.GGHdRo7NoTV
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUGraph
import CFSG.LocalAnalysis.StandardType.GGHdRo7XDatum

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7D

theorem ggResSUCorank3Input_proved
    (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput') :
    GGResSUCorank3Input :=
  ggResSUCorank3Input_of_leaves hX hJ hRig hLB hKG a3_normalizer_holds a3_reflFix_holds
    a3_pWeyl_holds a3_reflU_holds a3_reflM9_holds a3_stabCard_holds a3_reduceM_holds
    a3_reduceV_holds d_classLarge_holds
    (Small.a3_linSmall_of_leaves Small.a9_real_holds Small.a9_norm_holds Small.a9_wit_holds
      Small.a9_e8_holds)
    su_graph_holds noTV_holds xDatumGraph_holds
    (a3_lModel_of_side a3_rankLower_holds a3_rankUpper_holds a3_sideTor_holds a3_sideMat_holds)
    a3_lstab_holds
    (a3_kModel_of_side a3_rankLower_holds a3_rankUpper_holds a3_sideTor_holds a3_sideMat_holds)
    a3_kstab_holds a3_aj_holds

end CFSG.StandardType.HdRo7A3
