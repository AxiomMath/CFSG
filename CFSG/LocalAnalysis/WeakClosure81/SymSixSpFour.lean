module

public import CFSG.Quasithin.Background.RonanE68S6
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem isSpGp_four_one_of_isSymGp_six {X : Type} [Group X] (h : IsSymGp X 6) :
    IsSpGp X 4 1 := by
  obtain ⟨e⟩ := h
  refine ⟨2, by norm_num, ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  exact ⟨e.trans CFSG.Quasithin.RonanE68.Psi.symm⟩

theorem isSymGp_six_of_isSpGp_four_one {X : Type} [Group X] (h : IsSpGp X 4 1) :
    IsSymGp X 6 := by
  obtain ⟨k, hk, F, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hk2 : k = 2 := by omega
  subst hk2
  let e1 : CFSG.Open.StatedSp 2 F ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    CFSG.SignalizerFunctorTheorem.NonLocal.spTwoTwoEquiv hcard
  let e2 : CFSG.ComponentClassification.PresentationLocal.sympFour ≃* CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp (ZMod 2) :=
    MulEquiv.subgroupCongr CFSG.Quasithin.RonanE68.sympFour_eq_antiSp
  let e3 : CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp (ZMod 2) ≃* CFSG.Open.StatedSp 2 (ZMod 2) :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSpEquiv (ZMod 2)
  exact ⟨e.trans ((e1.trans e2).trans (e3.trans CFSG.Quasithin.RonanE68.Psi))⟩

end CFSG.LocalAnalysis.WeakClosure81
