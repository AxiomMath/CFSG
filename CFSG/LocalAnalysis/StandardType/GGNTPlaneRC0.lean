module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneFrame
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneClassify

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.NTPlane

theorem langNontoralCompField_of_input
    (hS : LangNontoralStructure) (hA : LangNontoralA2Descent) (hD : LangNontoralD4Fixed) :
    LangNontoralCompField := by
  intro L _ _ _ p₀ S hAlg D hDmodel habel hcard hnt K hK
  obtain ⟨S', D', a, n, K', hq, hnf, hK', hiff, hKcard, hKqcard⟩ :=
    ntp_frame S hAlg D hDmodel habel hcard hnt K hK
  rcases ntp_compField_normalForm hS hA hD S' D' a n hnf K' hK' with hfield | ⟨hq2, h2, hq2'⟩
  · exact Or.inl (hiff.mpr hfield)
  · exact Or.inr ⟨hq.symm.trans hq2, by rw [hcard]; norm_num, hKcard ▸ h2, hKqcard ▸ hq2'⟩

theorem langNontoralCompField_of_centralizerInput
    (h : LangNontoralCentralizerInput) : LangNontoralCompField :=
  langNontoralCompField_of_input h.1 h.2.1 h.2.2

end CFSG.StandardType.TableCRes

end
