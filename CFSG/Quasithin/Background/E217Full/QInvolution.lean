module

public import CFSG.Quasithin.Background.D2Params
import CFSG.Quasithin.Background.D2Cyclic

public section

namespace CFSG.Quasithin.E217Full.LemmaQ

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem mem_fixV_zpowers {z : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers z) ↔ z v = v := by
  constructor
  · intro h
    exact h z (Subgroup.mem_zpowers z)
  · intro h x hx
    have : Subgroup.zpowers z ≤ MulAction.stabilizer (MulAut V) v := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hx

theorem commSeries_zpowers_three [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {z : MulAut V}
    (hz : z * z = 1) : commSeries (Subgroup.zpowers z) 3 = ⊥ := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  have h1 : commSeries (Subgroup.zpowers z) 1 ≤ fixV (Subgroup.zpowers z) := by
    rw [commSeries_one]
    exact commV_zpowers_le_fixV hV hz2
  have h2 : commSeries (Subgroup.zpowers z) 2 = ⊥ := by
    have e : commSeries (Subgroup.zpowers z) 2 =
        commSub (commSeries (Subgroup.zpowers z) 1) (Subgroup.zpowers z) := rfl
    rw [e, eq_bot_iff]
    refine (commSub_mono h1 le_rfl).trans ?_
    rw [commSub_eq_bot_iff.2 le_rfl]
  have e3 : commSeries (Subgroup.zpowers z) 3 =
      commSub (commSeries (Subgroup.zpowers z) 2) (Subgroup.zpowers z) := rfl
  rw [e3, h2, commSub_eq_bot_iff]
  exact bot_le

theorem index_fixV_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hV16 : Nat.card V = 16)
    {z : MulAut V} (hz : z * z = 1) (hz1 : z ≠ 1) :
    (fixV (Subgroup.zpowers z)).index = 2 ∨ (fixV (Subgroup.zpowers z)).index = 4 := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  have hrkV : rk V = 4 := by
    unfold rk
    rw [hV16, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  have hsum := rk_commV_add_rk_fixV z
  have hle := rk_mono (commV_zpowers_le_fixV hV hz2)
  have hidxrk := rkIdx_fixV_zpowers z
  have hri : rkIdx (fixV (Subgroup.zpowers z)) ≤ 2 := by omega
  have hdvd : (fixV (Subgroup.zpowers z)).index ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = Nat.card V by rw [hV16]; norm_num]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, hj4, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hjr : rkIdx (fixV (Subgroup.zpowers z)) = j := by
    unfold rkIdx
    rw [hj, padicValNat.prime_pow]
  have hne : (fixV (Subgroup.zpowers z)).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hz1
    ext v
    have hv : v ∈ fixV (Subgroup.zpowers z) := by rw [h1]; exact Subgroup.mem_top v
    rw [mem_fixV_zpowers] at hv
    rw [hv, MulAut.one_apply]
  rw [hj] at hne ⊢
  have hj2 : j ≤ 2 := by omega
  interval_cases j
  · exact absurd rfl hne
  · left; rfl
  · right; rfl

theorem qhatOf_le_one_of_index_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X : Subgroup (MulAut V)} {z : MulAut V} (hzX : z ∈ X) (hz : z * z = 1) (hz1 : z ≠ 1)
    (hidx : (fixV (Subgroup.zpowers z)).index = 2) : qhatOf X ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  unfold qhatOf
  rw [kq_le_iff]
  refine ⟨Subgroup.zpowers z, ⟨Subgroup.zpowers_le.2 hzX, ?_, ?_, ?_⟩,
    commSeries_zpowers_three hV hz, ?_⟩
  · intro h
    exact hz1 (Subgroup.zpowers_eq_bot.1 h)
  · intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self z m n).eq
  · intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num [hz2]
  · rw [rAV_zpowers hz1 hz2, ← rkIdx_fixV_zpowers]
    unfold rkIdx
    rw [hidx]
    norm_num

end CFSG.Quasithin.E217Full.LemmaQ
