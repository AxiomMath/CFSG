module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
import CFSG.LocalAnalysis.UniquenessCase.Lie.CoprimeLift
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcD4Two
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcE6
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcRee
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcTwisted
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

section Centre


theorem uc22pwex_card_center_dvd_three {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {n : ℕ} (hn : 2 < n)
    (h : LieModel (K ⧸ center K) .E6 0 2 n ∨ LieModel (K ⧸ center K) .twistedE6 0 2 n) :
    Nat.card (center K) ∣ 3 := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases h with h | h
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := uc22pwex_e6_model h
    have h1 := uc22p20r_card_center_dvd_hopf e
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier
      (K := F) (by rw [hF]; omega)
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv] at h1
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ ZMod _),
      Nat.card_zmod] at h1
    exact h1.trans (Nat.gcd_dvd_left _ _)
  · obtain ⟨F, _, _, hF, σ, hσ, ⟨e⟩⟩ := (h.chevalleyExceptionalModel (by decide)).2
    have h1 := uc22p20r_card_center_dvd_hopf e
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_hopfMultiplier
        (K := F) (θ := σ) (q := 2 ^ n) (by omega) hF hσ
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv] at h1
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ ZMod _),
      Nat.card_zmod] at h1
    exact h1.trans (Nat.gcd_dvd_left _ _)

theorem uc22pwex_e_holds : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (center K)) → center K ≠ ⊥ → ∀ n : ℕ, 2 < n →
    (LieModel (K ⧸ center K) .E6 0 2 n ∨ LieModel (K ⧸ center K) .twistedE6 0 2 n) →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → p ≠ 3 → uc22p20oBorelWit K p 4 := by
  intro K _ _ hq _ _ n hn hL p hp hpn hp3
  have h3 := uc22pwex_card_center_dvd_three hq hn hL
  have hcop : ¬ p ∣ Nat.card (center K) := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h.trans h3))
  refine uc22pwlie_borelWit_of_central_quotient (Z := center K) le_rfl hp hcop ?_
  rcases hL with h | h
  · exact uc22pwex_e6_borelWit h hp hpn hp3
  · exact uc22pwex_twE6_borelWit h hp hpn hp3

end Centre

section TwoFamilies


theorem uc22pwex_d4_holds (hN : uc22p20rNativeGriess) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ n : ℕ, LieModel (K ⧸ center K) .trialityD4 0 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → uc22p20oBorelWit K p 2 := by
  intro K _ _ hq hodd n hL p hp hpn
  have hNo : uc22p20oNoOddMult .trialityD4 0 n := by
    unfold uc22p20oNoOddMult
    obtain ⟨⟨-, hn1, -⟩, -⟩ := hL.chevalleyExceptionalModel (by decide)
    rcases (show n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | h
    · simp
    · simp
    · simp [h]
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .trialityD4 0 n hNo hL
  refine uc22pwlie_borelWit_of_central_quotient (Z := center K) le_rfl hp
    (by rw [hZ, Subgroup.card_bot]; exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)) ?_
  exact uc22pwex_d4_borelWit hL hp hpn

theorem uc22pwex_f4_holds (hN : uc22p20rNativeGriess) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ n : ℕ, LieModel (K ⧸ center K) .twistedF4 0 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → uc22p20oBorelWit K p 2 := by
  intro K _ _ hq hodd n hL p hp hpn
  obtain ⟨-, hadm, -⟩ := hL.reeTitsModel (by decide)
  have hn3 : 2 < n := by have := hadm.2.2.2.2.2; omega
  have hNo : uc22p20oNoOddMult .twistedF4 0 n := by
    unfold uc22p20oNoOddMult; simp [hn3]
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .twistedF4 0 n hNo hL
  refine uc22pwlie_borelWit_of_central_quotient (Z := center K) le_rfl hp
    (by rw [hZ, Subgroup.card_bot]; exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)) ?_
  exact uc22pwex_f4_borelWit hL hp hpn

end TwoFamilies

section D4Two


theorem uc22pwex_d4two_holds (hN : uc22p20rNativeGriess) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    LieModel (K ⧸ center K) .trialityD4 0 2 1 → uc22p20oRankWit K 3 2 := by
  intro K _ _ hq hodd hL
  have hNo : uc22p20oNoOddMult .trialityD4 0 1 := by
    unfold uc22p20oNoOddMult; simp
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .trialityD4 0 1 hNo hL
  obtain ⟨e⟩ := uc22pwex_equiv_quot_of_center_eq_bot hZ
  obtain ⟨E, hE, hc⟩ := uc22pwex_d4two_rankWit hL
  exact uc22pwex_rankWit_of_equiv e E hE hc

end D4Two

end CFSG.LocalAnalysis.UniquenessCase.UC22
