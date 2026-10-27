module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.RonanF13

theorem aut_trivial_of_cyclic_exp3 {K : Type*} [Group K] (Z : Subgroup K) (hZ : IsCyclic ↥Z)
    (h3 : ∀ z ∈ Z, z ^ 3 = 1) (β : MulAut K) (hβZ : ∀ x, β x ∈ Z ↔ x ∈ Z)
    (hβ : Odd (orderOf β)) : ∀ z ∈ Z, β z = z := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective ↥Z
  have hg3 : (g : K) ^ (3 : ℤ) = 1 := by
    exact_mod_cast h3 (g : K) g.2
  have hgg : (g : K) * ((g : K) * (g : K)) = 1 := by
    rw [← pow_three]
    exact h3 (g : K) g.2
  have hcover : ∀ x ∈ Z, ∃ m : ℤ, (g : K) ^ m = x := by
    intro x hx
    obtain ⟨m, hm⟩ := hg ⟨x, hx⟩
    exact ⟨m, by rw [← Subgroup.coe_zpow]; exact congrArg Subtype.val hm⟩
  have hred : ∀ m : ℤ, (g : K) ^ m = (g : K) ^ (m % 3) := by
    intro m
    have hm : m = m % 3 + 3 * (m / 3) := by omega
    calc (g : K) ^ m = (g : K) ^ (m % 3 + 3 * (m / 3)) := by rw [← hm]
      _ = (g : K) ^ (m % 3) * ((g : K) ^ (3 : ℤ)) ^ (m / 3) := by rw [zpow_add, zpow_mul]
      _ = (g : K) ^ (m % 3) := by rw [hg3, one_zpow, mul_one]
  have hcases : ∀ x ∈ Z, x = 1 ∨ x = (g : K) ∨ x = (g : K) * (g : K) := by
    intro x hx
    obtain ⟨m, rfl⟩ := hcover x hx
    rw [hred m]
    rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with h | h | h
    · left; rw [h, zpow_zero]
    · right; left; rw [h, zpow_one]
    · right; right; rw [h, zpow_two]
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hall : ∀ x ∈ Z, x = 1 ∨ x = z ∨ x = z * z := by
    intro x hx
    rcases hcases z hz with h | h | h
    · exact absurd h hz1
    · rcases hcases x hx with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl (h'.trans h.symm))
      · exact Or.inr (Or.inr (by rw [h', h]))
    · have key : (g : K) * (g : K) * ((g : K) * (g : K)) = (g : K) := by
        calc (g : K) * (g : K) * ((g : K) * (g : K))
              = (g : K) * ((g : K) * ((g : K) * (g : K))) := by simp only [mul_assoc]
          _ = (g : K) * 1 := by rw [hgg]
          _ = (g : K) := mul_one _
      have hgz : (g : K) = z * z := by
        rw [h]
        exact key.symm
      rcases hcases x hx with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (h'.trans hgz))
      · exact Or.inr (Or.inl (h'.trans h.symm))
  have hz3 : z * (z * z) = 1 := by
    rw [← pow_three]
    exact h3 z hz
  have hzz4 : z * z * (z * z) = z := by
    calc z * z * (z * z) = z * (z * (z * z)) := by simp only [mul_assoc]
      _ = z * 1 := by rw [hz3]
      _ = z := mul_one z
  have hβz_mem : β z ∈ Z := (hβZ z).2 hz
  rcases hall (β z) hβz_mem with h1 | h1 | h1
  · exact absurd (β.injective (h1.trans (map_one β).symm)) hz1
  · exact h1
  · exfalso
    have hγ : (β ^ 2) z = z := by
      rw [pow_two, MulAut.mul_apply, h1, map_mul, h1]
      exact hzz4
    have hpow : ∀ j : ℕ, ((β ^ 2) ^ j) z = z := by
      intro j
      induction j with
      | zero => rw [pow_zero, MulAut.one_apply]
      | succ n ih => rw [pow_succ (β ^ 2) n, MulAut.mul_apply, hγ, ih]
    obtain ⟨s, hs⟩ := hβ
    have hβeq : β = (β ^ 2) ^ (s + 1) := by
      rw [← pow_mul]
      have h1' : β ^ (2 * s + 1) = 1 := by
        rw [← hs]
        exact pow_orderOf_eq_one β
      rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega, pow_succ, h1', one_mul]
    have hβz : β z = z := by
      have := hpow (s + 1)
      rwa [← hβeq] at this
    have h11 : z * z = z * 1 := by
      rw [mul_one]
      exact h1.symm.trans hβz
    exact hz1 (mul_left_cancel h11)

end CFSG.Quasithin.RonanF13
