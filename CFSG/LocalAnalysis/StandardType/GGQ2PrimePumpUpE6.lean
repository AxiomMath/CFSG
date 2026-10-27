module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models

@[expose] def PumpUpTwistedE6Input : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (W Wk : Subgroup K) (ζ ξ : MulAut K)
    (Q A : Subgroup (MulAut K)), PumpUpAut W Wk ζ ξ Q A →
      LieModel (K ⧸ center K) .twistedE6 0 2 1 → False

private theorem false_of_pumpUpAut_E6
    {K : Type} [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K}
    {Q A : Subgroup (MulAut K)} (h : PumpUpAut W Wk ζ ξ Q A)
    (h6 : LieModel (K ⧸ center K) .E6 0 2 1) : False := by
  classical
  let π : K →* K ⧸ center K := QuotientGroup.mk' (center K)
  have hWcl : StatedClassicalModel W .PSU 5 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.W_model
    · exact hc
    · omega
  haveI : IsSimpleGroup W := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWcl
  have hWc : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hWcl
  have hWnp : ¬ (Nat.card W).Prime := by
    rw [hWc]
    norm_num
  have hπW : Function.Injective (π.comp W.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have hs' : s ∈ center W := mem_center_iff.2 fun b => Subtype.ext (mem_center_iff.1 hs b)
    rwa [CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup hWnp] at hs'
  have hdvd : Nat.card W ∣ Nat.card (K ⧸ center K) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hπW).toEquiv]
    exact card_subgroup_dvd_card _
  obtain ⟨-, hc | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := h6
  · exact hc.2
  cases d with
  | E6 q =>
    obtain ⟨hp, hf⟩ := hd
    have hm := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hp e
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E6 hm, hp, hf,
      hWc] at hdvd
    have h11 : ¬ 11 ∣ ordE6 (2 ^ 1) := by
      unfold ordE6
      norm_num
    exact h11 ((by norm_num : 11 ∣ 13685760).trans hdvd)
  | _ => exact hd

theorem pumpUpE6Input_of_twisted
    (h : PumpUpTwistedE6Input) : PumpUpE6Input := by
  intro K _ _ W Wk ζ ξ Q A hA h6
  rcases h6 with h6 | h6
  · exact false_of_pumpUpAut_E6 hA h6
  · exact h K W Wk ζ ξ Q A hA h6

end CFSG.GGQ2Prime
