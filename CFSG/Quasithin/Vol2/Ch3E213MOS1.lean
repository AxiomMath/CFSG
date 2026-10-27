module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.Ch3E213M.Dih

open DihedralGroup

variable {k : ℕ}

theorem r_mem_zpowers (a : ZMod k) : r a ∈ Subgroup.zpowers (r 1 : DihedralGroup k) :=
  ⟨(a.cast : ℤ), by
    show (r 1 : DihedralGroup k) ^ (a.cast : ℤ) = r a
    rw [r_one_zpow, ZMod.intCast_zmod_cast]⟩

theorem card_le_two_of_le_zpowers {V : Subgroup (DihedralGroup k)}
    (hV : V ≤ Subgroup.zpowers (r 1)) (hsq : ∀ v ∈ V, v * v = 1) : Nat.card V ≤ 2 := by
  have : IsCyclic ↥V := Subgroup.isCyclic_of_le hV
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
  have htop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hfin : Nat.card ↥V = orderOf g := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top]
  rw [hfin]
  have h1 : g ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (hsq _ g.2)
  exact orderOf_le_of_pow_eq_one two_pos h1

theorem le_zpowers_of_forall_ne {V : Subgroup (DihedralGroup k)} (h : ∀ i : ZMod k, sr i ∉ V) :
    V ≤ Subgroup.zpowers (r 1) := by
  intro v hv
  cases v with
  | r a => exact r_mem_zpowers a
  | sr a => exact absurd hv (h a)

theorem r_neg_two_mem {V : Subgroup (DihedralGroup k)} (hV : ∀ v ∈ V, r 1 * v * (r 1)⁻¹ ∈ V)
    {i : ZMod k} (hi : sr i ∈ V) : r (-2) ∈ V := by
  have h1 : r 1 * sr i * (r 1)⁻¹ = sr (i - 2) := by
    rw [inv_r, r_mul_sr, sr_mul_r]
    congr 1
    ring
  have h2 : sr i * sr (i - 2) = r (-2) := by
    rw [sr_mul_sr]
    congr 1
    ring
  rw [← h2]
  exact V.mul_mem hi (h1 ▸ hV _ hi)

theorem card_le_two_of_normal (hk : ¬ k ∣ 4) {V : Subgroup (DihedralGroup k)}
    (hV : ∀ v ∈ V, r 1 * v * (r 1)⁻¹ ∈ V) (hsq : ∀ v ∈ V, v * v = 1) : Nat.card V ≤ 2 := by
  refine card_le_two_of_le_zpowers (le_zpowers_of_forall_ne fun i hi => hk ?_) hsq
  have h := hsq _ (r_neg_two_mem hV hi)
  rw [r_mul_r, ← r_zero] at h
  have h4 : ((4 : ℕ) : ZMod k) = 0 := by
    have h' : (-2 : ZMod k) + -2 = 0 := r.inj h
    have : ((4 : ℕ) : ZMod k) = -((-2 : ZMod k) + -2) := by push_cast; ring
    rw [this, h', neg_zero]
  exact (ZMod.natCast_eq_zero_iff 4 k).mp h4

theorem card_le_two_of_le_normal (hk : ∀ j : ℕ, k ≠ 2 ^ j) {N V : Subgroup (DihedralGroup k)}
    (hN : ∀ v ∈ N, r 1 * v * (r 1)⁻¹ ∈ N) (h2 : ∀ x ∈ N, ∃ j : ℕ, x ^ 2 ^ j = 1) (hVN : V ≤ N)
    (hsq : ∀ v ∈ V, v * v = 1) : Nat.card V ≤ 2 := by
  refine card_le_two_of_le_zpowers (le_zpowers_of_forall_ne fun i hi => ?_) hsq
  obtain ⟨j, hj⟩ := h2 _ (r_neg_two_mem hN (hVN hi))
  rw [r_pow, ← r_zero] at hj
  have h0 : ((2 ^ (j + 1) : ℕ) : ZMod k) = 0 := by
    have h' : (-2 : ZMod k) * ((2 ^ j : ℕ) : ZMod k) = 0 := r.inj hj
    have : ((2 ^ (j + 1) : ℕ) : ZMod k) = -((-2 : ZMod k) * ((2 ^ j : ℕ) : ZMod k)) := by
      push_cast
      ring
    rw [this, h', neg_zero]
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    ((ZMod.natCast_eq_zero_iff _ k).mp h0)
  exact hk m hm

theorem exists_eq_r_of_odd {g : DihedralGroup k} (hg : Odd (orderOf g)) : ∃ i, g = r i := by
  cases g with
  | r i => exact ⟨i, rfl⟩
  | sr i =>
    rw [orderOf_sr] at hg
    exact absurd hg (by decide)

theorem orderOf_r_two_pow {a m : ℕ} (hk : k = 2 ^ a * m) (hm : 2 ≤ m) :
    orderOf (r ((2 ^ a : ℕ) : ZMod k)) = m := by
  have hpos : 0 < 2 ^ a := pow_pos two_pos a
  have hlt : 2 ^ a < k := by
    rw [hk]
    calc 2 ^ a = 2 ^ a * 1 := (mul_one _).symm
      _ < 2 ^ a * m := Nat.mul_lt_mul_of_pos_left (by omega) hpos
  have : NeZero k := ⟨by omega⟩
  have hd : 2 ^ a ∣ k := by
    rw [hk]
    exact Dvd.intro m rfl
  rw [orderOf_r, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.gcd_eq_right hd, hk,
    Nat.mul_div_cancel_left _ hpos]

theorem eq_zero_or_eq_half (hk : Even k) (hk0 : k ≠ 0) {i : ZMod k} (h : i + i = 0) :
    i = 0 ∨ i = ((k / 2 : ℕ) : ZMod k) := by
  have : NeZero k := ⟨hk0⟩
  have hlt := ZMod.val_lt i
  have hdvd : k ∣ 2 * i.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, two_mul, h]
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hc2
    have : k * 2 ≤ k * c := Nat.mul_le_mul_left k (by omega)
    omega
  interval_cases c
  · left
    have : i.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val i, this, Nat.cast_zero]
  · right
    obtain ⟨j, hj⟩ := hk
    have : i.val = k / 2 := by omega
    rw [← ZMod.natCast_zmod_val i, this]

theorem orderOf_r_half (hk : Even k) (hk3 : 3 ≤ k) : orderOf (r ((k / 2 : ℕ) : ZMod k)) = 2 := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨j, hj⟩ := hk
  rw [orderOf_r, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h1 : k / 2 = j := by omega
  rw [h1, show k = 2 * j by omega, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by omega)]

theorem mem_center_iff' (hk : Even k) (hk3 : 3 ≤ k) {x : DihedralGroup k} :
    x ∈ Subgroup.center (DihedralGroup k) ↔ x = 1 ∨ x = r ((k / 2 : ℕ) : ZMod k) := by
  rw [center_eq_closure_of_even_ne_two hk (by omega)]
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, orderOf_r_half hk hk3, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_center_of_comm (hk : Even k) (hk5 : 5 ≤ k) {x : DihedralGroup k} (hx : x * x = 1)
    (hc : r 1 * x * (r 1)⁻¹ * x⁻¹ ∈ Subgroup.center (DihedralGroup k)) :
    x ∈ Subgroup.center (DihedralGroup k) := by
  rw [mem_center_iff' hk (by omega)]
  cases x with
  | r i =>
    have h2 : i + i = 0 := by
      rw [r_mul_r, ← r_zero] at hx
      exact r.inj hx
    rcases eq_zero_or_eq_half hk (by omega) h2 with h | h
    · left
      rw [h, r_zero]
    · right
      rw [h]
  | sr i =>
    exfalso
    have h1 : r 1 * sr i * (r 1)⁻¹ * (sr i)⁻¹ = r 2 := by
      rw [inv_r, inv_sr, r_mul_sr, sr_mul_r, sr_mul_sr]
      congr 1
      ring
    rw [h1, mem_center_iff' hk (by omega)] at hc
    have : NeZero k := ⟨by omega⟩
    rcases hc with h | h
    · rw [← r_zero] at h
      have h' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast r.inj h
      have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 k).mp h')
      omega
    · have h' : ((2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := by exact_mod_cast r.inj h
      have h'' := (ZMod.natCast_eq_natCast_iff' 2 (k / 2) k).mp h'
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h''
      obtain ⟨j, hj⟩ := hk
      omega

end CFSG.Quasithin.Ch3E213M.Dih
