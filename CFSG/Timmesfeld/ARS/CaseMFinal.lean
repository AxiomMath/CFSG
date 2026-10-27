module

public import CFSG.Timmesfeld.ARS.CaseMMain
public import CFSG.Timmesfeld.ARS.CaseMSULevi

public section

namespace CFSG.Timmesfeld.ARS

namespace CaseM

theorem suDictInput : SUDictInput := by
  intro G _ R A A₀ hS E C P Q hfr f hf Φ hker hrange hΔ
  obtain ⟨Φ', hker', hrange', hΔ', hP, hQ⟩ := hS.exists_aligned_su_dict hfr hf Φ hker hrange hΔ
  exact ⟨Φ', hker', hrange', hP, hQ, fun a b hab γ hγ =>
    hS.commuting_diffRoot_su hfr hf Φ' hker' hrange' hΔ' hP hQ hab hγ⟩

end CaseM

theorem caseMFrameInput_of_leviInput (hLevi : CaseMLeviInput) : CaseMFrameInput :=
  caseMFrameInput_of hLevi CaseM.suDictInput

end CFSG.Timmesfeld.ARS
