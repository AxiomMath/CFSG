module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.CyclicCentralCommutatorPair

theorem unique_square_one
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (a b : H) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hane : a ≠ 1) (hbne : b ≠ 1) :
    a = b := by
  classical
  obtain ⟨g, hg⟩ := exists_zpow_surjective H
  have ha_zp : a ∈ Subgroup.zpowers g := hg a
  have hb_zp : b ∈ Subgroup.zpowers g := hg b
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff a g).mp (mem_powers_iff_mem_zpowers.mpr ha_zp)
  obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff b g).mp (mem_powers_iff_mem_zpowers.mpr hb_zp)
  let d := orderOf g
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard g) Nat.card_pos
  have key : ∀ x : ℕ, g ^ (2 * x) = 1 → g ^ x ≠ 1 → 2 * (x % d) = d := by
    intro x h2x hx
    have hdvd2x : d ∣ 2 * x := orderOf_dvd_iff_pow_eq_one.mpr h2x
    have hndx : ¬ d ∣ x := fun h => hx (orderOf_dvd_iff_pow_eq_one.mp h)
    have hxmod_pos : 0 < x % d := Nat.pos_of_ne_zero (fun h => hndx (Nat.dvd_of_mod_eq_zero h))
    have hxmod_lt : x % d < d := Nat.mod_lt x hdpos
    have hdvd2xmod : d ∣ 2 * (x % d) := by
      have h1 : 2 * (x % d) ≡ 2 * x [MOD d] := Nat.ModEq.mul_left 2 (Nat.mod_modEq x d)
      have h2 : 2 * x ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdvd2x
      exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)
    obtain ⟨t, ht⟩ := hdvd2xmod
    have ht_pos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, mul_zero] at ht
        omega
      · exact h
    have ht_lt : t < 2 := by
      have h : d * t < d * 2 := by
        rw [← ht, mul_comm d 2]
        omega
      exact (Nat.mul_lt_mul_left hdpos).mp h
    have ht_one : t = 1 := by omega
    rw [ht, ht_one, mul_one]
  have h2k : g ^ (2 * k) = 1 := by rw [Nat.mul_comm 2 k, pow_mul, hk, ha]
  have h2l : g ^ (2 * l) = 1 := by rw [Nat.mul_comm 2 l, pow_mul, hl, hb]
  have hkne : g ^ k ≠ 1 := by rw [hk]; exact hane
  have hlne : g ^ l ≠ 1 := by rw [hl]; exact hbne
  have hk_eq : 2 * (k % d) = d := key k h2k hkne
  have hl_eq : 2 * (l % d) = d := key l h2l hlne
  have hmod_eq : k % d = l % d := by omega
  calc a = g ^ k := hk.symm
    _ = g ^ (k % d) := (pow_mod_orderOf g k).symm
    _ = g ^ (l % d) := by rw [hmod_eq]
    _ = g ^ l := pow_mod_orderOf g l
    _ = b := hl

theorem commutator_square
    {G : Type*} [Group G] (x y : G) (hy : y ^ 2 = 1)
    (hcentral : Commute y ⁅x, y⁆) : ⁅x, y⁆ ^ 2 = 1 := by
  have hconj : y * ⁅x, y⁆ * y⁻¹ = ⁅x, y⁆ := by
    rw [hcentral.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc
    ⁅x, y⁆ ^ 2 = ⁅x, y⁆ * ⁅x, y⁆ := pow_two _
    _ = ⁅x, y⁆ * (y * ⁅x, y⁆ * y⁻¹) := congrArg (fun t => ⁅x, y⁆ * t) hconj.symm
    _ = ⁅x, y * y⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      simp only [mul_assoc]
    _ = 1 := by rw [← pow_two, hy, commutatorElement_one_right]

theorem pair_eq_and_commute
    {G : Type*} [Group G]
    (Q : Subgroup G) [Finite Q] [IsCyclic Q]
    (a : Q) (ha : a ^ 2 = 1) (hane : a ≠ 1)
    (x z y : G) (hy : y ^ 2 = 1)
    (hxcentral : ∀ q : Q, Commute x q.val)
    (hycentral : ∀ q : Q, Commute y q.val)
    (hxyQ : ⁅x, y⁆ ∈ Q) (hzyQ : ⁅z, y⁆ ∈ Q)
    (hxy : ¬ Commute x y) (hzy : ¬ Commute z y) :
    ⁅x, y⁆ = a.val ∧ ⁅z, y⁆ = a.val ∧ Commute (x * z) y := by
  have hne (g : G) (hg : ¬ Commute g y) : ⁅g, y⁆ ≠ 1 :=
    fun he => hg (commutatorElement_eq_one_iff_commute.mp he)
  have heq (g : G) (hgQ : ⁅g, y⁆ ∈ Q) (hg : ¬ Commute g y) : ⁅g, y⁆ = a.val := by
    let c : Q := ⟨⁅g, y⁆, hgQ⟩
    have hc2 : c ^ 2 = 1 := Subtype.ext
      (commutator_square g y hy (hycentral c))
    have hcne : c ≠ 1 := fun h => hne g hg (congrArg Subtype.val h)
    exact congrArg Subtype.val (unique_square_one c a hc2 ha hcne hane)
  have hx := heq x hxyQ hxy
  have hz := heq z hzyQ hzy
  refine ⟨hx, hz, commutatorElement_eq_one_iff_commute.mp ?_⟩
  rw [commutatorElement_mul_left_eq_conj_mul, hx, hz, (hxcentral a).eq]
  rw [mul_assoc a.val x x⁻¹, mul_inv_cancel, mul_one]
  exact congrArg Subtype.val (by simpa only [pow_two] using ha)

end FiveTransitive.CyclicCentralCommutatorPair

end CFSG
