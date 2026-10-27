module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerLift
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.LieType.Universal

namespace TwE6Per


theorem ggTwE6TorusLiftInput_holds : GGTwE6TorusLiftInput := by
  intro K _ _ n p hn hK hp hpn
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  set k := GaloisField 2 (2 * n)
  set θ : k →+* k := frobQ 2 n
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 n hn
  have hk : Nat.card k = (2 ^ n) ^ 2 := card_galoisField_two_mul 2 n hn
  obtain ⟨q, -, hqk⟩ := TwE6Delta.exists_sc_surjection hn hK
  have hq2 : ∀ z ∈ q.ker, z * z = 1 → z = 1 := by
    intro z hz hzz
    have hc := hqk hz
    have hcard : Nat.card (Subgroup.center (fixedGroup k θ)) = Nat.gcd 3 (2 ^ n + 1) :=
      (card_center_fixedGroup (k := k) (θ := θ) (q := 2 ^ n) hk
        (fun c => by rw [show θ c = frobQ 2 n c from rfl, frobQ_apply])).1
    have h1 : orderOf z ∣ 3 := by
      have h2 : orderOf (⟨z, hc⟩ : Subgroup.center (fixedGroup k θ)) ∣
          Nat.card (Subgroup.center (fixedGroup k θ)) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hcard] at h2
      exact h2.trans (Nat.gcd_dvd_left 3 _)
    have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
    have h3 : orderOf z ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 3 2 = 1 by norm_num] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hpk : p ∣ Nat.card k - 1 := by
    rw [hk, show ((2 : ℕ) ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact Dvd.dvd.mul_right hpn _
  obtain ⟨μ, hμo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := k) hpk
  have hμp : μ ^ p = 1 := by rw [← hμo]; exact pow_orderOf_eq_one μ
  have hμ : μ * μ ≠ 1 := by
    intro h
    have : orderOf μ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hμo] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hθμ : Units.map (θ : k →* k) μ = μ⁻¹ := by
    have hq1 : μ ^ (2 ^ n + 1) = 1 := by
      obtain ⟨m, hm⟩ := hpn
      rw [hm, pow_mul, hμp, one_pow]
    have e : Units.map (θ : k →* k) μ = μ ^ 2 ^ n := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      exact frobQ_apply 2 n _)
    rw [e]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hq1])
  by_cases h3 : p = 3
  · subst h3
    rw [TwE6Delta.liftRank_three]
    exact ggTorusLift_four_of_hom hθ μ hθμ q hqk hq2 hμ hp hp2 hμp
  · rw [TwE6Delta.liftRank_of_ne h3]
    exact ggTorusLift_five_of_hom hθ μ hθμ q hqk hq2 hμ hp hp2 h3 hμp

end TwE6Per

end CFSG.StandardType
