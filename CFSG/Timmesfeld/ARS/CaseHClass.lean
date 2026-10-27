module

public import CFSG.Timmesfeld.ARS.CaseHSharp
public import CFSG.Timmesfeld.ARS.CaseHBW
public import CFSG.Timmesfeld.ARS.CaseHDigits

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

theorem eq_one_of_units_trivial {F E : Type} [Field F] [Field E] [Finite F] (e : F →+* E)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (h : ∀ l : Fˣ, e l = 1) : n = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have h1 : g = 1 := Units.ext (e.injective (by rw [h g, Units.val_one, map_one]))
  rw [h1, orderOf_one, Nat.card_units F, hF] at hg
  have h2 : 2 ^ n = 2 ^ 1 := by omega
  exact Nat.pow_right_injective (le_refl 2) h2

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)
  [CharP E 2] [Finite F] [CharP F 2] [Finite E] (e : F →+* E)
  (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1) {τ : F} (hτ0 : τ ≠ 0)
  (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem classify {n m : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hE : Nat.card E = 2 ^ m) :
    (m = n ∧ ∀ s, c.sharp s = s ^ 2) ∨
      (m = 3 * n ∧ ∀ s, c.sharp s = s ^ (2 ^ n + 2 ^ (2 * n))) ∨ (n = 1 ∧ m = 2) := by
  have := S.hyp.finite
  obtain ⟨d, hdlt, hd⟩ := c.exists_sharp_pow e he hτ0 hτ
  obtain ⟨k, hk⟩ := c.exists_card_eq_pow
  rw [hF, hE, ← pow_mul] at hk
  have hmk : m = n * k := Nat.pow_right_injective (le_refl 2) hk
  have hE2 : 2 ≤ Nat.card E := by
    have := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hm1 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    rw [hE, this, pow_zero] at hE2
    omega
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    rw [this, mul_zero] at hmk
    omega
  have he0 : ∀ l : Fˣ, e l ≠ 0 := fun l => (map_ne_zero e).2 l.ne_zero
  have hC2 : ∀ l : Fˣ, (e l) ^ d = (e l) ^ 2 := fun l => by
    rw [← hd _ (he0 l), c.sharp_e e he hτ0 hτ l, sq]
  have hC1 : ∀ s : E, s ≠ 0 → ∃ x : F, x ≠ 0 ∧ s ^ (d + 1) = e x := fun s hs =>
    ⟨_, c.nu_ne_zero _, by rw [pow_succ, ← hd s hs, c.sharp_mul_self_eq e he hτ0 hτ hs]⟩
  have hFq : ∀ x : F, x ^ (2 ^ n) = x := by
    have := Fintype.ofFinite F
    intro x
    rw [← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  by_cases hk1' : k = 1
  ·
    left
    refine ⟨by rw [hmk, hk1', mul_one], fun s => ?_⟩
    have hbij : Function.Bijective e :=
      e.injective.bijective_of_nat_card_le (by rw [hF, hE, hmk, hk1', mul_one])
    by_cases hs : s = 0
    · rw [hs, c.sharp_zero]
      ring
    obtain ⟨x, rfl⟩ := hbij.2 s
    have hx : x ≠ 0 := fun h => hs (by rw [h, map_zero])
    have := c.sharp_e e he hτ0 hτ (Units.mk0 x hx)
    rw [Units.val_mk0] at this
    rw [this, sq]
  · have hk2 : 2 ≤ k := by omega
    have hd0 : d ≠ 0 := by
      intro h0
      have hsurj : Function.Surjective e := fun s => by
        by_cases hs : s = 0
        · exact ⟨0, by rw [hs, map_zero]⟩
        obtain ⟨x, -, hx⟩ := hC1 s hs
        rw [h0, zero_add, pow_one] at hx
        exact ⟨x, hx.symm⟩
      have hle := Nat.card_le_card_of_surjective e hsurj
      rw [hF, hE, hmk] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
      have : n * 2 ≤ n * k := Nat.mul_le_mul_left n hk2
      omega
    have hall : ∀ s, c.sharp s = s ^ d := fun s => by
      by_cases hs : s = 0
      · rw [hs, c.sharp_zero, zero_pow hd0]
      · exact hd s hs
    obtain ⟨f, hfadd, hf⟩ := c.exists_polar 1
    have key : ∀ s : E, (s + 1) ^ d - s ^ d - 1 = f s := fun s => by
      have := hf s
      rw [hall, hall, hall, one_pow, add_comm 1 s] at this
      rw [this]
      ring
    have hadd : ∀ x y : E, (x + y + 1) ^ d - (x + y) ^ d - 1 =
        ((x + 1) ^ d - x ^ d - 1) + ((y + 1) ^ d - y ^ d - 1) := fun x y => by
      rw [key, key, key, hfadd]
    have := Fintype.ofFinite E
    have hcardU : Nat.card Eˣ = Nat.card E - 1 := Nat.card_units E
    have hdE : d < Fintype.card E := by
      rw [← Nat.card_eq_fintype_card]
      omega
    have hBW := exponent_of_additive_polar hd0 hdE hadd
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
    obtain ⟨x, hx0, hx⟩ := hC1 g g.ne_zero
    have hpow : g ^ ((d + 1) * (2 ^ n - 1)) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul, hx, ← map_pow, Units.val_one]
      have := Fintype.ofFinite F
      rw [show 2 ^ n - 1 = Fintype.card F - 1 by rw [← Nat.card_eq_fintype_card, hF],
        FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hgeom : Nat.card Eˣ = geom (2 ^ n) k * (2 ^ n - 1) := by
      rw [geom_mul _ _ hq1, hcardU, hE, hmk, pow_mul]
    rw [hg, hgeom] at hdvd
    have hqpos : 0 < 2 ^ n - 1 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right hqpos hdvd
    have hgpos : 0 < geom (2 ^ n) k := one_le_geom (by omega)
    have hj1 : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      rw [this, mul_zero] at hj
      omega
    have hjq : j < 2 ^ n := by
      have h1 : geom (2 ^ n) k * j < geom (2 ^ n) k * (2 ^ n - 1) + 1 := by
        rw [← hj, ← hgeom]
        omega
      by_contra h
      push Not at h
      have : geom (2 ^ n) k * (2 ^ n) ≤ geom (2 ^ n) k * j := Nat.mul_le_mul_left _ h
      have h3 : geom (2 ^ n) k * (2 ^ n) = geom (2 ^ n) k * (2 ^ n - 1) + geom (2 ^ n) k := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    rcases exponent_eq hn hk2 hj1 hjq (by rw [hj, mul_comm]) hBW with
      ⟨hk', hdq⟩ | ⟨hk', hn2, hdq⟩ | ⟨hk', hdq⟩
    ·
      right; right
      have hn1 : n = 1 := eq_one_of_units_trivial e hF fun l => by
        have h := hC2 l
        rw [hdq, ← map_pow, hFq] at h
        have hl := he0 l
        rw [sq] at h
        exact (mul_eq_left₀ hl).1 h.symm
      exact ⟨hn1, by rw [hmk, hk', hn1]⟩
    ·
      exfalso
      have h1 : n = 1 := eq_one_of_units_trivial e hF fun l => by
        have h := hC2 l
        rw [hdq, pow_add, pow_one, pow_succ, pow_mul, ← map_pow, hFq] at h
        have hl := he0 l
        have : e l * (e l * e l) = 1 * (e l * e l) := by rw [one_mul, ← sq, h, sq]
        exact mul_right_cancel₀ (mul_ne_zero hl hl) this
      omega
    ·
      right; left
      exact ⟨by rw [hmk, hk', mul_comm], fun s => by rw [hall, hdq]⟩

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
