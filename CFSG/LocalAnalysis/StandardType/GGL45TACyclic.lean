module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

public section

namespace CFSG.StandardType

open Finset

theorem ggL45TA_geom_mul {p q₀ : ℕ} (hp : Odd p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (∑ i ∈ range p, (ε * q₀) ^ i) * (ε * q₀ - 1) = ε * ((q₀ : ℤ) ^ p - ε) := by
  rw [geom_sum_mul, mul_pow]
  rcases hε with rfl | rfl
  · simp
  · rw [hp.neg_one_pow]; ring

theorem ggL45TA_exists_pow_eq_of_fixed {C : Type*} [CommGroup C] [IsCyclic C] [Finite C]
    {p q₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hC : (Nat.card C : ℤ) = (q₀ : ℤ) ^ p - ε) (hpq : (p : ℤ) ∣ q₀ - ε) (z : C)
    (hz : z ^ (ε * q₀) = z) : ∃ ν : C, z = ν ^ p := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set S : ℤ := ∑ i ∈ range p, (ε * q₀) ^ i with hS
  have hgeom := ggL45TA_geom_mul (q₀ := q₀) hodd hε
  rw [← hS] at hgeom
  have hm0 : (0 : ℤ) < Nat.card C := by exact_mod_cast Nat.card_pos
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hmS : (Nat.card C : ℤ) = ε * (S * (ε * q₀ - 1)) := by
    rw [hgeom, ← mul_assoc, hεε, one_mul, hC]
  have hc1 : ε * q₀ - 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at hmS
    exact (ne_of_gt hm0) hmS
  have hpS : (p : ℤ) ∣ S := by
    have hpc : (p : ℤ) ∣ ε * q₀ - 1 := by
      have : ε * q₀ - 1 = ε * (q₀ - ε) := by rw [mul_sub, hεε]
      rw [this]; exact dvd_mul_of_dvd_right hpq ε
    have hsub : S - p = ∑ i ∈ range p, ((ε * q₀) ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hS]; simp
    have h1 : (p : ℤ) ∣ S - p := by
      rw [hsub]
      exact Finset.dvd_sum fun i _ => hpc.trans (by simpa using sub_dvd_pow_sub_pow (ε * q₀) 1 i)
    have h2 := dvd_add h1 (dvd_refl (p : ℤ))
    rwa [sub_add_cancel] at h2
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have hgen : ∀ x : C, x ∈ Subgroup.zpowers g := by
    intro x
    have : Subgroup.zpowers g = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hg]
    rw [this]; exact Subgroup.mem_top x
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen z)
  have h1 : g ^ (a * (ε * q₀ - 1)) = 1 := by
    rw [zpow_mul, zpow_sub, zpow_one, hz, mul_inv_cancel]
  have hdvd : (Nat.card C : ℤ) ∣ a * (ε * q₀ - 1) := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hg] at h
  obtain ⟨t, ht⟩ : S ∣ a := by
    obtain ⟨u, hu⟩ := hdvd
    refine ⟨ε * u, ?_⟩
    have h2 : a * (ε * q₀ - 1) = S * (ε * u) * (ε * q₀ - 1) := by
      rw [hu, hmS]; ring
    exact mul_right_cancel₀ hc1 h2
  obtain ⟨S', hS'⟩ := hpS
  refine ⟨g ^ (S' * t), ?_⟩
  rw [← zpow_natCast, ← zpow_mul, ht, hS']
  congr 1
  ring

theorem ggL45TA_pairing_eq_one {p : ℕ} (hp : p.Prime) {E M : Type*} [CommGroup E] [Group M]
    (c : E → E → M) (hl : ∀ a a' b, c (a * a') b = c a b * c a' b)
    (hr : ∀ a b b', c a (b * b') = c a b * c a b') (halt : ∀ a, c a a = 1)
    (P : Subgroup E) (hP : ∀ a ∈ P, ∀ b, c a b = 1) (hidx : P.index ∣ p) :
    ∀ a b, c a b = 1 := by
  have hl1 : ∀ b, c 1 b = 1 := fun b => by
    have h := hl 1 1 b
    rw [one_mul] at h
    exact left_eq_mul.mp h
  have hanti : ∀ a b, c a b * c b a = 1 := fun a b => by
    have h := halt (a * b)
    rw [hl, hr, hr, halt, halt, one_mul, mul_one] at h
    exact h
  have hP' : ∀ a, ∀ b ∈ P, c a b = 1 := fun a b hb => by
    have h := hanti a b
    rw [hP b hb a, mul_one] at h
    exact h
  have hpow : ∀ (a b : E) (n : ℕ), c (a ^ n) b = c a b ^ n := fun a b n => by
    induction n with
    | zero => rw [pow_zero, pow_zero, hl1]
    | succ n ih => rw [pow_succ, hl, ih, pow_succ]
  rcases (Nat.dvd_prime hp).1 hidx with h1 | hpi
  · rw [Subgroup.index_eq_one] at h1
    intro a b
    exact hP a (h1 ▸ Subgroup.mem_top a) b
  have hcard : Nat.card (E ⧸ P) = p := by rw [← Subgroup.index_eq_card, hpi]
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ : ∃ g : E, g ∉ P := by
    by_contra h
    push Not at h
    have : P = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [this, Subgroup.index_top] at hpi
    exact hp.one_lt.ne hpi
  have hgen : ∀ a : E, ∃ n : ℕ, (g ^ n)⁻¹ * a ∈ P := by
    intro a
    have hne : (QuotientGroup.mk g : E ⧸ P) ≠ 1 := by
      rwa [Ne, QuotientGroup.eq_one_iff]
    have htop : Subgroup.zpowers (QuotientGroup.mk g : E ⧸ P) = ⊤ :=
      zpowers_eq_top_of_prime_card hcard hne
    have ha : (QuotientGroup.mk a : E ⧸ P) ∈ Subgroup.zpowers (QuotientGroup.mk g : E ⧸ P) := by
      rw [htop]; exact Subgroup.mem_top _
    haveI : Finite (E ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ha)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, hn]
  have hgg : ∀ j : ℕ, c g (g ^ j) = 1 := fun j => by
    have h := hanti (g ^ j) g
    rw [hpow, halt, one_pow, one_mul] at h
    exact h
  intro a b
  obtain ⟨i, hi⟩ := hgen a
  obtain ⟨j, hj⟩ := hgen b
  obtain ⟨r, hrP, rfl⟩ : ∃ r ∈ P, a = g ^ i * r :=
    ⟨_, hi, (mul_inv_cancel_left (g ^ i) a).symm⟩
  obtain ⟨r', hr'P, rfl⟩ : ∃ r ∈ P, b = g ^ j * r :=
    ⟨_, hj, (mul_inv_cancel_left (g ^ j) b).symm⟩
  rw [hl, hr, hr, hpow g (g ^ j) i, hgg j, one_pow, hP' (g ^ i) r' hr'P, hP r hrP (g ^ j),
    hP r hrP r']
  simp only [mul_one]

end CFSG.StandardType
