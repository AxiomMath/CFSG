module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcSevenAux
import CFSG.LocalAnalysis.StandardType.GGForkA8NotReflHolds
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrExcSevenReflInput_holds
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGSecFiveA8TablePInput) : GGNbrExcSevenReflInput := by
  have hMp : GGInnerDiagMpInput := ggInnerDiagMpInput_holds
  intro G _ _ p B Bs x L D J h y K hK hp hexc
  subst hp
  rcases hexc with hA8 | hE6
  · obtain ⟨χ, hχ⟩ :=
      ggForkA8NotReflInput_of_mp hMp G B Bs x L D J h.1 h.2.2.1 y K hK hA8
    exact not_ggReflGenerated_of_hom_three χ hχ
  · exact (ggWTP8_secFiveE6TwoSeven_false hRig hTCJ hTP h hK rfl hE6).elim

end CFSG.StandardType

end
