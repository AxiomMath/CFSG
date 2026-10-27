module

public import CFSG.Quasithin.Recognition.M12AmalAutLFacts
public import CFSG.Quasithin.Recognition.M12AmalAutJMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut CFSG.Quasithin.AmalTransport

theorem autM12AmalgamLocal_unfolded
    :
    ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseAutM12 H L2 → AutLocalConcl H L2 := by
  intro G _ _ H L2 hcase
  obtain ⟨hAm, -, hV, -, -⟩ := hcase
  obtain ⟨Y, _, ⟨eY⟩, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hAm
  obtain ⟨m⟩ := autM12PermModel
  let f : Y ≃* AutG := eY.trans m.symm
  have hpair' := IsYAmalgamPair.map f hpair
  obtain ⟨φ, hφ⟩ := aut_pair_cases hpair'
  have iso' := isoMap (isoMap iso f) φ
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · have h : AutLocalConcl ((M₁.map f.toMonoidHom).map φ.toMonoidHom)
        ((M₂.map f.toMonoidHom).map φ.toMonoidHom) := by
      rw [hA, hB]
      exact autLocalConcl_model
    have hcore : pCoreOf 2 ((M₁.map f.toMonoidHom).map φ.toMonoidHom) ≤
        (M₁.map f.toMonoidHom).map φ.toMonoidHom ⊓ (M₂.map f.toMonoidHom).map φ.toMonoidHom := by
      rw [hA, hB]
      exact pCoreOf_A_le_inf
    exact AutLocalConcl.of_iso iso' hcore h
  · exfalso
    have e₁ : ↥H ≃* ↥autData.B := iso'.φ1.trans (MulEquiv.subgroupCongr hB)
    have hcard := autCardCenterOfEq (autPCoreOfCongr e₁)
    exact aut_card_center_B_ne_two (hcard.symm.trans hV.2.2)

end CFSG.Quasithin
