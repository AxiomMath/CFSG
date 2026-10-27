module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapCT
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

local instance twistedE6PilotSwapUniqueNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem unitsRange_facts (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    3 ≤ Nat.card (Units.map (algebraMap k K).toMonoidHom).range ∧
      Odd (Nat.card (Units.map (algebraMap k K).toMonoidHom).range) ∧
      (∀ c ∈ (Units.map (algebraMap k K).toMonoidHom).range,
        Units.map σ.toMonoidHom c = c) ∧ ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  refine ⟨F4Pilot.three_le_natCard_range_unitsMap _ h4, ?_, ?_, hσι⟩
  · rw [F4Pilot.natCard_range_unitsMap, Nat.card_units, hk]
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    obtain ⟨m, hm⟩ := h2
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  · rintro _ ⟨u, rfl⟩
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    exact hσι u

theorem false_of_swapRow_2E6 (hset : SeitzSetting G L) (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (hP : SeitzQ2.SwapPairExclusion (graphFixedRootGroup TwistTag.E6 K σ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hX : SwapCover t (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range
      .X)) (modelToG e (su6Levi σ)) (neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range
        .X))
    (hY : SwapCover t (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range
      .Y)) (modelToG e (omegaMinusLevi σ))
        (neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y)) :
    False := by
  have : Finite K := finite_of_card hK
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow
    (show Nat.card K = 2 ^ (2 * f) by rw [hK, ← pow_mul, mul_comm])
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  set A := (Units.map (algebraMap k K).toMonoidHom).range with hAdef
  obtain ⟨hA3, hAo, hA, hσι⟩ := unitsRange_facts (K := K) hf2 hk hσ
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hL := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  have hZ := hset.center_eq_bot
  have hOut := (outer_solvable_and_center_eq_bot_twistedE6 hK σ e).1
  have htL := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨G₁, hqs, -, h₁₂, hδL, hsurj, hpieces⟩ :=
    exists_swapFactor_2E6 e A hL hZ hA3 hAo hA (algebraMap k K) hσι h4 htL htt hX hY
  have hRp : ∀ r, ⁅relRankOne σ r, relRankOne σ r⁆ = relRankOne σ r :=
    commutator_relRankOne_of_le (algebraMap k K) hσι h4
  have huniq := SeitzQ2.unique_of_swapFactors_of_neighbours_of_swapPairExclusion hset hOut e hP ht
    hKt hqs h₁₂ hδL hsurj (fun r => relTorusG e A r) (fun r => relRankOneG e r)
    (fun r => modelToG_le e _) (fun r => relRankOneG_le_centralizer e A r)
    (fun r => modelToG_perfect e (relRankOne_le_C0 σ r) (hRp r)) (iSup_relRankOneG e hσs)
    (fun r => hpieces r)
  have : IsSimpleGroup G := hset.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hqs h₁₂ rfl huniq

end CFSG.SeitzReduction.TwistedE6Pilot
