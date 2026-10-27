module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveAbs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveAct
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSetup
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem w3Lem85TwoGap5_holds : W3Lem85TwoGap5 G := by
  intro V H T U hD X _ φ hφ h2 hn
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hKT := hD.eq_sup
  obtain ⟨φ', hφ', hS'⟩ := exists_ambient_barMap h83 hKT hφ
  have hSit : BarSituation X (barSub (kGenIn V H) φ V) := by
    rw [← hS']
    exact barSituation_of_hyp711 (AmbientH.hyp711 h83 hKT) hφ'
  have hcen : CentralInSylow X (barSub (kGenIn V H) φ V) := by
    rw [← hS'] at h2 ⊢
    exact centralInSylow_of_hyp83 h83 hKT hφ' h2
  obtain ⟨ρ, Z₁, hρ, hρinj, hAct, hZ⟩ := gap5_exists_action hD hφ
  obtain ⟨hU2, hU⟩ := gap5_U_facts hD
  obtain ⟨Y, _, ψ, hψs, hψk, hY⟩ := gap5_abstract hSit h2 hcen hn ρ hρinj hAct hU2 hU
    (fun x s u hs hu hxs hfix => gap5_dichotomy_X hD hφ hρ hZ x hs hu hxs hfix)
  exact gap5_kBarCenterShape_of_symSix (ψ.comp φ) (hψs.comp hφ.surjective)
    (fun k => (hψk (φ k)).trans (hZ k)) hY

end CFSG.LocalAnalysis.WeakClosure81

end
