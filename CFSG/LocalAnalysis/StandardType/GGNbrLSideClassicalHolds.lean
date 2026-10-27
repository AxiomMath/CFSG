module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpData
import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniData
import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthData
import CFSG.LocalAnalysis.StandardType.GGNbrLSideLinData

public section

namespace CFSG.StandardType

theorem ggNbrLSideUnitaryData_of_certificates :
    GGNbrLSideUnitaryData :=
  ggNbrLSideUnitaryData_holds CFSG.LocalAnalysis.GLTheoremA.cls_det
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

theorem ggNbrLSideSymplecticData_of_certificates :
    GGNbrLSideSymplecticData :=
  ggNbrLSideSymplecticData_holds CFSG.LocalAnalysis.GLTheoremA.cls_det
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

theorem ggNbrLSideOrthogonalData_of_certificates :
    GGNbrLSideOrthogonalData :=
  ggNbrLSideOrthogonalData_holds CFSG.LocalAnalysis.GLTheoremA.cls_det
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

theorem ggNbrLSideLinearData_of_certificates :
    GGNbrLSideLinearData :=
  ggNbrLSideLinearData_holds CFSG.LocalAnalysis.GLTheoremA.cls_det
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

end CFSG.StandardType

end
