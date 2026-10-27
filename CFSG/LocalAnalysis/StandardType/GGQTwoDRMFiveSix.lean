module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseType
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFive
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabSix
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly


theorem ggQTwoRMInputOn_five (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoRMInputOn fun m => m = 5 :=
  ggQTwoRMInputOn_five_of_inputs hTBF hWI
    ((ggQTwoDRMBaseTypeInputOn_of_ne_six hTBF hWI).mono fun m (hm : m = 5) =>
      ⟨by omega, by omega⟩)


theorem ggQTwoRMInputOn_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hZS : ZS.UseInput) : GGQTwoRMInputOn fun m => m = 6 :=
  have hT := ggQTwoDRMBaseTypeInputOn_six hTBF hWI
  ggQTwoRMInputOn_of_inputs (fun m (hm : m = 6) => by omega)
    (ggQTwoDSelModuleInputOn_of_selectedModule (fun m (hm : m = 6) => by omega) hTBF hWI)
    (ggQTwoDRMBaseInputOn_of_type hT)
    (ggQTwoDRMStabInputOn_six_of_type ggLNoncyclicInput_holds hT) hZS

theorem ggQTwoRMInputOn_five_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hZS : ZS.UseInput) : GGQTwoRMInputOn fun m => m = 5 ∨ m = 6 :=
  (ggQTwoRMInputOn_five hTBF hWI).or (ggQTwoRMInputOn_six hTBF hWI hZS)

end CFSG.StandardType.QTwo

end
