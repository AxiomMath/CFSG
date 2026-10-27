module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNInner
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNData
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoComponentsThreeInput

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo

theorem ggQ2s08_roComponentsThree_holds
    (hRig : GGLabelRigidInput) :
    GGQ2S08ROComponentsThreeInput := by
  intro G _ _ B Bs x L D J hS _ M hShape labL hMark hLab hBig hWeyl heven h3 f hFrame
  classical
  have hW : ∃ e : Fin labL.rank ≃ M.Λ, M.coxeter = (CoxeterMatrix.A labL.rank).reindex e := by
    simpa only [GGQ2LabelWeyl, hLab.1] using hWeyl
  obtain ⟨e, he⟩ := hW
  have hn9 : 9 ≤ labL.rank := hBig.2.2
  have hodd : Odd labL.rank := by
    obtain ⟨r, hr⟩ := heven
    exact ⟨r - 1, by omega⟩
  have h3n : ¬ 3 ∣ labL.rank := by omega
  obtain ⟨c⟩ := ggQ2s08rN_exists_data_of_odd hRig (by omega) hodd h3n hS M hMark
    ⟨hLab.1, rfl, hLab.2⟩ f hFrame
  obtain ⟨w, hw⟩ := c.frame_cmp M hShape.2.2.2.2 he f hFrame
  refine ⟨fun j => c.comp (w j), fun j => c.comp_le _, fun j => ?_,
    fun j => c.le_normalizer_comp _, fun j => c.four_dvd_card_automizer _,
    fun i j hij => c.comp_sup fun h => hij (w.injective h)⟩
  exact c.comp_pComponent (w j) (b := Additive.toMul (M.model.symm (f j))) (hw j).1 (hw j).2

end CFSG.StandardType

end
