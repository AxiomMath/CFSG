module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FieldMain
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCTField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6)

local instance twistedE6PilotQ2FieldCTNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotQ2FieldCTNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank :=
  ⟨by decide⟩

@[expose] def triangleWord : List (Fin TwistTag.E6.tag.rank) := [4, 5, 3, 4]

@[expose] def TwistedE6TwoFieldFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → ∀ hK : Nat.card K = (2 ^ 1) ^ 2,
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq le_rfl hK) e t (modelToG e A) →
        ∃ φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G,
          IsCompatible (adjDatumE6 K).leviAmalgam φ ∧ (∃ J, ∃ x, φ J x ≠ 1) ∧
          centralizerPerfectCore (modelToG e A) ≤ ⨆ J, (φ J).range ∧
          t ∈ normalizer ((⨆ J, (φ J).range : Subgroup G) : Set G)

theorem twistedE6TwoFieldCTInput_of_family (h : TwistedE6TwoFieldFamilyInput) :
    TwistedE6TwoFieldCTInput := by
  intro G _ _ L k K _ _ _ hset hk hK σ hσ e t htC ht A hAJ hA hcyc Φ
  obtain ⟨φ, hφ, hnt, hEX, htN⟩ := h G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc Φ
  have : Finite K := finite_of_card hK
  obtain ⟨ψ, hsurj, hker, hqs, hZ, -⟩ :=
    exists_surjective_iSup_range_of_isCompatible_adj φ hφ hnt (G₀ := ⨆ J, (φ J).range) rfl
  have hodd : Odd (Nat.card (center (⨆ J, (φ J).range : Subgroup G))) := by
    have h1 : Nat.card (center (⨆ J, (φ J).range : Subgroup G)) ∣ 3 := by
      rw [hZ]
      refine (Subgroup.card_map_dvd _ ψ).trans ?_
      rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K).1]
      exact Nat.gcd_dvd_left 3 _
    exact Odd.of_dvd_nat (by decide) h1
  exact ⟨⨆ J, (φ J).range, Subgroup.isPerfect_iff.1 hqs.1, hodd,
    ⟨((E6Pilot.centerQuotientIsogenyEquiv (K := K)).symm.trans
      (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ)).symm⟩, htN, hEX⟩

theorem twistedE6TwoFieldRowInput_of_family (hR : TwistedE6TwoDiagonalRigidity)
    (hF : TwistedE6TwoFieldFamilyInput) : TwistedE6TwoFieldRowInput :=
  twistedE6TwoFieldRowInput_of_CT hR (twistedE6TwoFieldCTInput_of_family hF)

end CFSG.SeitzReduction.TwistedE6Pilot
