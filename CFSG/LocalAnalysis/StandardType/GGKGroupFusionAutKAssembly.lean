module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKClassical
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKExc

public section

namespace CFSG.StandardType

theorem ggLieOutRankTwoAt_of_three_or_ge_five {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (hd : d.1.characteristic = p) (h3 : p = 3 → GGLieOutRankTwoAt d)
    (h5 : 5 ≤ p → GGLieOutRankTwoAt d) : GGLieOutRankTwoAt d := by
  intro hfin hs hnab hp2
  have hp : p.Prime := hd ▸ TauCeti.LieTypeIndex.characteristic_prime d.1
  rw [hd] at hp2
  by_cases hp3 : p = 3
  · exact h3 hp3 hfin hs hnab (hd ▸ hp2)
  · have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
    have h1 := hp.two_le
    exact h5 (by omega) hfin hs hnab (hd ▸ hp2)

@[expose] def GGLieOutRankTwoRestLabel : TauCeti.LieTypeIndex → Prop
  | .A r q => r = 1 ∧ q.p = 3
  | .B r q => 3 ≤ r ∧ q.p = 3
  | .D _ q => q.p = 3
  | .twistedD _ q => q.p = 3
  | .E6 q => q.p = 3
  | .twistedE6 q => q.p = 3
  | _ => False

@[expose] def GGLieOutRankTwoRestInput : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, GGLieOutRankTwoRestLabel d.1 → GGLieOutRankTwoAt d

section Assembly


theorem ggLieOutRankTwoInput_of_rest (h : GGLieOutRankTwoRestInput) : GGLieOutRankTwoInput := by
  refine ggLieOutRankTwoInput_of_forall fun d => ?_
  obtain ⟨d, hv⟩ := d
  have hR : GGLieOutRankTwoRestLabel d → GGLieOutRankTwoAt ⟨d, hv⟩ := h ⟨d, hv⟩
  cases d with
  | A r q =>
    refine ggLieOutRankTwoAt_of_three_or_ge_five (TauCeti.LieTypeIndex.characteristic_A r q)
      (fun h3 => ?_) fun h5 => ggLieOutRankTwoAt_A r q hv (Or.inr h5)
    by_cases hr : r = 1
    · exact hR ⟨hr, h3⟩
    · have := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      exact ggLieOutRankTwoAt_A r q hv (Or.inl (by omega))
  | twistedA r q => exact ggLieOutRankTwoAt_twistedA r q hv
  | B r q =>
    refine ggLieOutRankTwoAt_of_three_or_ge_five (TauCeti.LieTypeIndex.characteristic_B r q)
      (fun h3 => ?_) fun h5 => ggLieOutRankTwoAt_B r q hv (Or.inr h5)
    by_cases hr : r = 2
    · exact ggLieOutRankTwoAt_B r q hv (Or.inl hr)
    · have := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      exact hR ⟨by omega, h3⟩
  | C r q => exact ggLieOutRankTwoAt_C r q hv
  | D r q =>
    exact ggLieOutRankTwoAt_of_three_or_ge_five (TauCeti.LieTypeIndex.characteristic_D r q)
      (fun h3 => hR h3) fun h5 => ggLieOutRankTwoAt_D r q hv h5
  | twistedD r q =>
    exact ggLieOutRankTwoAt_of_three_or_ge_five (TauCeti.LieTypeIndex.characteristic_twistedD r q)
      (fun h3 => hR h3) fun h5 => ggLieOutRankTwoAt_twistedD r q hv h5
  | E6 q =>
    exact ggLieOutRankTwoAt_of_three_or_ge_five (TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun h3 => hR h3) fun h5 => ggLieOutRankTwoAt_E6 q hv h5
  | E7 q => exact ggLieOutRankTwoAt_E7 q hv
  | E8 q => exact ggLieOutRankTwoAt_E8 q hv
  | F4 q => exact ggLieOutRankTwoAt_F4 q hv
  | G2 q => exact ggLieOutRankTwoAt_G2 q hv
  | twistedE6 q =>
    exact ggLieOutRankTwoAt_of_three_or_ge_five (TauCeti.LieTypeIndex.characteristic_twistedE6 q)
      (fun h3 => hR h3) fun h5 => ggLieOutRankTwoAt_twistedE6 q hv h5
  | trialityD4 q => exact ggLieOutRankTwoAt_trialityD4 q hv
  | suzuki m =>
    exact fun _ _ _ hp2 => absurd (TauCeti.LieTypeIndex.characteristic_suzuki m) hp2
  | reeG2 m => exact ggLieOutRankTwoAt_reeG2 m hv
  | reeF4 m =>
    exact fun _ _ _ hp2 => absurd (TauCeti.LieTypeIndex.characteristic_reeF4 m) hp2
  | tits => exact fun _ _ _ hp2 => absurd TauCeti.LieTypeIndex.characteristic_tits hp2

end Assembly

end CFSG.StandardType
