module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16t_a_false_of_inverted {T : Type} [CommGroup T] [Finite T] (hT : ∀ v : T, v ^ 2 = 1)
    (hodd : Odd (rk T)) {z a : MulAut T} (hz : z ^ 7 = 1) (hfix : ∀ v : T, z v = v → v = 1)
    (ha : a * z * a⁻¹ = z⁻¹) : False := by
  classical
  have hsq : ∀ v : T, v * v = 1 := fun v => by rw [← pow_two]; exact hT v
  have hzmod : ∀ n m : ℕ, n % 7 = m → z ^ n = z ^ m := fun n m h => by
    rw [pow_eq_pow_mod n hz, h]
  have eadd : ∀ (k l : ℕ) (v : T), (z ^ k) ((z ^ l) v) = (z ^ (k + l)) v := by
    intro k l v
    rw [pow_add]
    rfl
  have e7 : ∀ v : T, (z ^ 7) v = v := fun v => by rw [hz]; rfl
  have e8 : ∀ v : T, (z ^ 8) v = (z ^ 1) v := fun v => by rw [hzmod 8 1 rfl]
  have e9 : ∀ v : T, (z ^ 9) v = (z ^ 2) v := fun v => by rw [hzmod 9 2 rfl]
  have e10 : ∀ v : T, (z ^ 10) v = (z ^ 3) v := fun v => by rw [hzmod 10 3 rfl]
  have hN : ∀ v : T, v * (z ^ 1) v * (z ^ 2) v * (z ^ 3) v * (z ^ 4) v * (z ^ 5) v *
      (z ^ 6) v = 1 := by
    intro v
    apply hfix
    have hstep : ∀ (k : ℕ) (w : T), z ((z ^ k) w) = (z ^ (k + 1)) w := by
      intro k w
      have := eadd 1 k w
      rwa [pow_one, add_comm] at this
    have h1 : z v = (z ^ 1) v := by rw [pow_one]
    simp only [map_mul, hstep, h1, Nat.reduceAdd, e7]
    ac_rfl
  have hinv : z⁻¹ = z ^ 6 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ' z 6, hz]
  have hak : ∀ (k m : ℕ), z ^ (6 * k) = z ^ m → ∀ w : T, a ((z ^ k) w) = (z ^ m) (a w) := by
    intro k m hkm w
    have h1 : a * z ^ k * a⁻¹ = (z⁻¹) ^ k := by rw [← conj_pow, ha]
    have h2 : a * z ^ k = (z ^ m) * a := by
      rw [mul_inv_eq_iff_eq_mul] at h1
      rw [h1, hinv, ← pow_mul, hkm]
    calc a ((z ^ k) w) = (a * z ^ k) w := rfl
      _ = ((z ^ m) * a) w := by rw [h2]
      _ = (z ^ m) (a w) := rfl
  have ha1 : ∀ w : T, a ((z ^ 1) w) = (z ^ 6) (a w) := hak 1 6 rfl
  have ha2 : ∀ w : T, a ((z ^ 2) w) = (z ^ 5) (a w) := hak 2 5 (hzmod 12 5 rfl)
  have ha3 : ∀ w : T, a ((z ^ 3) w) = (z ^ 4) (a w) := hak 3 4 (hzmod 18 4 rfl)
  have ha4 : ∀ w : T, a ((z ^ 4) w) = (z ^ 3) (a w) := hak 4 3 (hzmod 24 3 rfl)
  have ha5 : ∀ w : T, a ((z ^ 5) w) = (z ^ 2) (a w) := hak 5 2 (hzmod 30 2 rfl)
  have ha6 : ∀ w : T, a ((z ^ 6) w) = (z ^ 1) (a w) := hak 6 1 (hzmod 36 1 rfl)
  let s : T →* T := MonoidHom.mk' (fun v => (z ^ 1) v * (z ^ 2) v * (z ^ 4) v) (by
    intro x y
    simp only [map_mul]
    ac_rfl)
  let t : T →* T := MonoidHom.mk' (fun v => (z ^ 3) v * (z ^ 5) v * (z ^ 6) v) (by
    intro x y
    simp only [map_mul]
    ac_rfl)
  have hs : ∀ v, s v = (z ^ 1) v * (z ^ 2) v * (z ^ 4) v := fun v => rfl
  have ht : ∀ v, t v = (z ^ 3) v * (z ^ 5) v * (z ^ 6) v := fun v => rfl
  have hI1 : ∀ v : T, s v * t v = v := by
    intro v
    have h := hN v
    rw [hs, ht]
    calc (z ^ 1) v * (z ^ 2) v * (z ^ 4) v * ((z ^ 3) v * (z ^ 5) v * (z ^ 6) v)
        = (z ^ 1) v * (z ^ 2) v * (z ^ 4) v * ((z ^ 3) v * (z ^ 5) v * (z ^ 6) v) * (v * v) := by
          rw [hsq, mul_one]
      _ = (v * (z ^ 1) v * (z ^ 2) v * (z ^ 3) v * (z ^ 4) v * (z ^ 5) v * (z ^ 6) v) * v := by
          ac_rfl
      _ = v := by rw [h, one_mul]
  have hI3 : ∀ v : T, s (t v) = 1 := by
    intro v
    have h := hN v
    simp only [hs, ht, map_mul, eadd, Nat.reduceAdd, e7, e8, e9, e10]
    calc _ = (v * (z ^ 1) v * (z ^ 2) v * (z ^ 3) v * (z ^ 4) v * (z ^ 5) v * (z ^ 6) v) *
          (v * v) := by ac_rfl
      _ = 1 := by rw [h, hsq, mul_one]
  have hI4 : ∀ u : T, a (s u) = t (a u) := by
    intro u
    simp only [hs, ht, map_mul, ha1, ha2, ha4]
    ac_rfl
  have hI5 : ∀ u : T, a (t u) = s (a u) := by
    intro u
    simp only [hs, ht, map_mul, ha3, ha5, ha6]
    ac_rfl
  have hker : s.ker = t.range := by
    ext x
    constructor
    · intro hx
      have hsx : s x = 1 := hx
      refine ⟨x, ?_⟩
      have h1 := hI1 x
      rw [hsx, one_mul] at h1
      exact h1
    · rintro ⟨y, rfl⟩
      exact hI3 y
  have hcard : Nat.card T = Nat.card t.range * Nat.card s.range := by
    rw [← Subgroup.card_ker_mul_card_range s, hker]
  have hle1 : Nat.card s.range ≤ Nat.card t.range := by
    have hle : s.range.map a.toMonoidHom ≤ t.range := by
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨a u, (hI4 u).symm⟩
    rw [← Subgroup.card_map_of_injective (f := a.toMonoidHom) a.injective]
    exact Subgroup.card_le_of_le hle
  have hle2 : Nat.card t.range ≤ Nat.card s.range := by
    have hle : t.range.map a.toMonoidHom ≤ s.range := by
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨a u, (hI5 u).symm⟩
    rw [← Subgroup.card_map_of_injective (f := a.toMonoidHom) a.injective]
    exact Subgroup.card_le_of_le hle
  have heq : Nat.card t.range = Nat.card s.range := le_antisymm hle2 hle1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrk : rk T = 2 * padicValNat 2 (Nat.card s.range) := by
    unfold rk
    rw [hcard, heq, ← pow_two, padicValNat.pow]
  rw [hrk] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) (even_two_mul _)

theorem s16t_a_conj_eq_or_inv {Γ : Type} [Group Γ] {z w : Γ} (hz : z ^ 7 = 1)
    (hzw : w * z * w⁻¹ ∈ Subgroup.zpowers z) {k : ℕ} (hw : w ^ (2 ^ k) = 1) :
    w * z * w⁻¹ = z ∨ w * z * w⁻¹ = z⁻¹ := by
  by_cases hz1 : z = 1
  · left
    rw [hz1]
    simp
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf z = 7 := orderOf_eq_prime hz hz1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hzw
  have hj' : w * z * w⁻¹ = z ^ j := hj.symm
  have hconj : ∀ m : ℕ, w ^ m * z * (w ^ m)⁻¹ = z ^ (j ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc w ^ (m + 1) * z * (w ^ (m + 1))⁻¹ = w * (w ^ m * z * (w ^ m)⁻¹) * w⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            group
        _ = w * z ^ (j ^ m) * w⁻¹ := by rw [ih]
        _ = (w * z * w⁻¹) ^ (j ^ m) := by rw [conj_zpow]
        _ = (z ^ j) ^ (j ^ m) := by rw [hj']
        _ = z ^ (j ^ (m + 1)) := by rw [← zpow_mul, pow_succ']
  have h1 : z ^ (j ^ (2 ^ k)) = z := by
    have := hconj (2 ^ k)
    rwa [hw, inv_one, mul_one, one_mul, eq_comm] at this
  have h2 : ((7 : ℕ) : ℤ) ∣ j ^ (2 ^ k) - 1 := by
    rw [← hord]
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  have h3 : (j : ZMod 7) ^ (2 ^ k) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (j ^ (2 ^ k) - 1) 7).2 h2
    push_cast at this
    exact sub_eq_zero.1 this
  have hx0 : (j : ZMod 7) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at h3
    exact zero_ne_one h3
  have h6 : (j : ZMod 7) ^ 6 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hdvd1 : orderOf (j : ZMod 7) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 : orderOf (j : ZMod 7) ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
  have hi1 : i ≤ 1 := by
    by_contra hcon
    have h4 : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
    rw [← hio] at h4
    have h5 := h4.trans hdvd2
    omega
  have hsq : (j : ZMod 7) ^ 2 = 1 := by
    have : orderOf (j : ZMod 7) ∣ 2 := by
      rw [hio]
      interval_cases i <;> simp
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have h5 : (j : ZMod 7) = 1 ∨ (j : ZMod 7) = -1 :=
    mul_self_eq_one_iff.1 (by rwa [← pow_two])
  rcases h5 with h5 | h5
  · left
    rw [hj']
    have h7 : ((7 : ℕ) : ℤ) ∣ j - 1 := by
      have : ((j - 1 : ℤ) : ZMod 7) = 0 := by
        rw [Int.cast_sub, Int.cast_one, h5]
        exact sub_self _
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 this
    rw [← hord] at h7
    have h8 := orderOf_dvd_iff_zpow_eq_one.1 h7
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h8
    exact h8
  · right
    rw [hj']
    have h7 : ((7 : ℕ) : ℤ) ∣ j + 1 := by
      have : ((j + 1 : ℤ) : ZMod 7) = 0 := by
        rw [Int.cast_add, Int.cast_one, h5]
        exact neg_add_cancel _
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 this
    rw [← hord] at h7
    have h8 := orderOf_dvd_iff_zpow_eq_one.1 h7
    rw [zpow_add, zpow_one] at h8
    exact eq_inv_of_mul_eq_one_left h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
