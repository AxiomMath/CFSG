module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagLie
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inputs

public section

namespace CFSG.StandardType.TableCRes

theorem ggTCInputG6InnerDiagLang_holds :
    GGTCInputG6InnerDiagLang := by
  intro τ L _ _ _ p₀ p S hτ _ hp hp2 d t hd ht hdp htp hd1 K hK
  have hτ' : τ = .E6 ∨ τ = .E8 := hτ.elim (fun h => Or.inr h) (fun h => Or.inl h.1)
  exact langTorus_innerDiagOn_lie hτ' S hp hp2 hd ht hdp htp hd1 hK

theorem ggTCInputG6InnerDiagLangTw_holds :
    GGTCInputG6InnerDiagLangTw := by
  intro L _ _ _ p₀ S _ d t hd ht hd3 ht3 hd1 K hK
  exact langTorus_innerDiagOn_E6_three S hd ht hd3 ht3 hd1 hK

end CFSG.StandardType.TableCRes

end
