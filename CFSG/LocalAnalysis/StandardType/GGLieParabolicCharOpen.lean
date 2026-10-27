module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharLin
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharSp
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharUni
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOrthD
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOrthTail
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharRee

public section

namespace CFSG.StandardType

theorem ggLieParabolicCharInputOn_open :
    GGLieParabolicCharInputOn GGLieParabolicOpenIndex := by
  rintro K _ _ ⟨e, hv⟩ hd
  cases e with
  | A r q => exact ggLieParabolicCharInputOn_A K ⟨.A r q, hv⟩ ⟨r, q, rfl⟩
  | twistedA r q => exact ggLieParabolicCharInputOn_twistedA K ⟨.twistedA r q, hv⟩ ⟨r, q, rfl⟩
  | B r q => exact ggLieParabolicCharInputOn_B K ⟨.B r q, hv⟩ ⟨r, q, rfl⟩
  | C r q => exact ggLieParabolicCharInputOn_C K ⟨.C r q, hv⟩ ⟨r, q, rfl⟩
  | D r q => exact ggLieParabolicCharInputOn_D K ⟨.D r q, hv⟩ ⟨r, q, rfl⟩
  | twistedD r q => exact ggLieParabolicCharInputOn_twistedD K ⟨.twistedD r q, hv⟩ ⟨r, q, rfl⟩
  | reeG2 m => exact ggLieParabolicCharInputOn_reeG2 K ⟨.reeG2 m, hv⟩ ⟨m, rfl⟩
  | _ => exact False.elim hd

end CFSG.StandardType
