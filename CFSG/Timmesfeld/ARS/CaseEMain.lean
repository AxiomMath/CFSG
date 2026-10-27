module

public import CFSG.Timmesfeld.ARS.CaseEOutput
public import CFSG.Timmesfeld.ARS.CaseEStep

public section

namespace CFSG.Timmesfeld.ARS

theorem caseEStep_of (hns : CaseENonSimplyLacedInput) : CaseEStep := by
  intro G _ R h IH A hA hcoat hAne hmax A₀ hA₀ h1 hnd
  have hS := Sec13.of_caseE h hA hcoat hAne hmax hA₀ h1 hnd
  obtain ⟨E₀, hE₀, -⟩ := id hnd
  have hcomp := comp_eq_leviSet_of_card_eq_one h hA hAne hA₀ h1 hE₀
  have hnd' : ∃ X ∈ Levi.comp R A A₀ E₀, ∃ Y ∈ Levi.comp R A A₀ E₀, Special R X Y := by
    rw [hcomp]
    exact hnd
  have key : ∀ S : Set (Subgroup G), S = leviSet R A A₀ → ∀ {r : ℕ}
      {adj : Fin r → Fin r → Prop}, HasConfigIn R S adj →
        ∃ P Q : Fin r → Subgroup G, IsConfig R adj P Q ∧
          (∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀) ∧
          ⨆ k, (P k ⊔ Q k) = levi R A A₀ := by
    rintro S rfl r adj ⟨P, Q, hX, hPQ, hgen⟩
    exact ⟨P, Q, hX, hPQ, hgen⟩
  have hnsl : ∀ S : Set (Subgroup G), S = leviSet R A A₀ →
      ¬ (NonSimplyLacedOutcome (↥(gen S) ⧸ Subgroup.center ↥(gen S)) ∧
        NSLData (↥(gen S) ⧸ Subgroup.center ↥(gen S)) (quotClass (gen S) S)) := by
    rintro S rfl
    exact hns G R h IH A hA hcoat hAne hmax A₀ hA₀ h1 hnd
  rcases Levi.output IH h hA hAne hA₀ hE₀ hnd' with ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | hc | hc | hc | hn
  · obtain ⟨P, Q, hX, hPQ, hgen⟩ := key _ hcomp hc
    exact hS.output_A hm hX hPQ hgen
  · obtain ⟨P, Q, hX, hPQ, hgen⟩ := key _ hcomp hc
    exact hS.output_D hm hX hPQ hgen
  · obtain ⟨P, Q, hX, hPQ, hgen⟩ := key _ hcomp hc
    exact hS.output_E6 hX hPQ hgen
  · obtain ⟨P, Q, hX, hPQ, hgen⟩ := key _ hcomp hc
    exact hS.output_E7 hX hPQ hgen
  · obtain ⟨P, Q, hX, hPQ, hgen⟩ := key _ hcomp hc
    exact (hS.not_isConfig_E8 hX hPQ hgen).elim
  · exact (hnsl _ hcomp hn).elim

end CFSG.Timmesfeld.ARS
