module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffSpSpQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoSpVacuous
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOmCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDense
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

section Rows


theorem ggSecFiveBCoordBOffSpSpInput_of_orth_lin_large (hO : GGSecFiveBCoordBOffSpOn fun _ _ lab =>
    lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))
    (hA : GGSecFiveBCoordBOffQTwoLinInput) (hL : GGSecFiveBCoordBOffSpSpLargeInput) :
    GGSecFiveBCoordBOffSpSpInput :=
  ggSecFiveBCoordBOffSpSpInput_of_qTwo_large
    (ggSecFiveBCoordBOffQTwoInput_of_families ggSecFiveBCoordBOffQTwoSpInput_holds hO hA) hL

end Rows

section Large


theorem ggSecFiveBCoordBOffSpSpLargeInput_of_label (hK : GGSecFiveBCoordBDenseNbrLabelInput)
    (hU : GGSecFiveBCoordBUniInput) (hJ : BMaxJoinInput) (hS : GGSecFiveBCoordBSparseLargeInput) :
    GGSecFiveBCoordBOffSpSpLargeInput :=
  ggSecFiveBCoordBOffSpSpLargeInput_of_dense
    (ggSecFiveBCoordBOmChartInput_of_mp ggInnerDiagMpInput_holds)
    (ggSecFiveBCoordBDenseNbrLargeInput_of_label hK) hU hJ hS

end Large

end CFSG.StandardType

end
