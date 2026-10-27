module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInnDiagE6
public import CFSG.LocalAnalysis.StandardType.GGFinModelInnDiagTw

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ggFixGp_conj_innDiagU
    {t : StatedLieTag} (ht6 : t = .E6 ∨ t = .twistedE6) {n f : ℕ} (hf : 1 ≤ f)
    (hinj : Function.Injective (ggIota t n f hf)) (m : ModGL (langTag t) GGL)
    (hm : m ∈ ggFixGp t f)
    (hmN : m ∈ Subgroup.normalizer ((ggIota t n f hf).range : Set (ModGL (langTag t) GGL))) :
    GGInnDiagU t n f (ggConjAut (ggIota t n f hf) hinj ⟨m, hmN⟩) := by
  rcases ht6 with rfl | rfl
  · exact ggFixGp_conj_innDiagU_E6 hf hinj m hm hmN
  · exact ggFixGp_conj_innDiagU_twE6 hf hinj m hm hmN

end CFSG.StandardType.GGFinModel
