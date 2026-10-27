module

public import CFSG.Quasithin.Background.RonanF13NT
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.RonanF13

theorem pow_apply_eq {K : Type*} [Group K] (α : MulAut K) {g : K} {k : ℕ}
    (hg : α g = g ^ 2 ^ k) (j : ℕ) : (α ^ j) g = g ^ (2 ^ k) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_pow, hg, ← pow_mul, pow_succ, mul_comm]

theorem twist_finish_elem {K : Type*} [Group K] (α : MulAut K) {k : ℕ} {g0 : K}
    (hα1 : α g0 = g0 ^ 2 ^ k) (hαodd : Odd (orderOf α))
    (hcomm : α (g0⁻¹ * α g0) = g0⁻¹ * α g0)
    {M c : ℕ} (hM : 1 ≤ M) (hc : c = 1 ∨ c = 3) (hc3 : c = 3 → 4 ≤ M)
    (hcN : c * orderOf g0 = 2 ^ M - 1) : α g0 = g0 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hdvd1 : orderOf g0 ∣ (2 ^ k - 1) ^ 2 := by
    have h1 := hcomm
    have h2 : g0⁻¹ * α g0 = g0 ^ m := by
      rw [hα1, hm, pow_succ']
      group
    rw [h2, map_pow, hα1, hm, ← pow_mul] at h1
    have h3 : g0 ^ (m * m) = 1 := by
      have h4 : g0 ^ ((m + 1) * m) = g0 ^ (m * m) * g0 ^ m := by
        rw [← pow_add]
        congr 1
        ring
      rw [h4] at h1
      have h5 : g0 ^ (m * m) * g0 ^ m = 1 * g0 ^ m := by rw [one_mul]; exact h1
      exact mul_right_cancel h5
    rw [orderOf_dvd_iff_pow_eq_one]
    have : 2 ^ k - 1 = m := by omega
    rw [this, sq]
    exact h3
  have hdvd2 : orderOf g0 ∣ 2 ^ (k * orderOf α) - 1 := by
    have h1 := pow_apply_eq α hα1 (orderOf α)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
    rw [orderOf_dvd_iff_pow_eq_one]
    have h2 : g0 ^ (2 ^ (k * orderOf α) - 1) * g0 = g0 ^ 2 ^ (k * orderOf α) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow)]
    have h3 : g0 ^ 2 ^ (k * orderOf α) = g0 := by
      rw [pow_mul]; exact h1.symm
    rw [h3] at h2
    have h4 : g0 ^ (2 ^ (k * orderOf α) - 1) * g0 = 1 * g0 := by rw [one_mul]; exact h2
    exact mul_right_cancel h4
  have hNT : orderOf g0 ∣ 2 ^ k - 1 :=
    nt_main (c := c) (N := orderOf g0) hM hc hc3 hcN hdvd1 hαodd hdvd2
  rw [hα1]
  have h1 : g0 ^ (2 ^ k - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hNT
  calc g0 ^ 2 ^ k = g0 ^ (2 ^ k - 1) * g0 := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow)]
    _ = g0 := by rw [h1, one_mul]

theorem twist_finish {K : Type*} [Group K] (D : Subgroup K) (α : MulAut K) {k : ℕ}
    (hcyc : IsCyclic ↥D) (hk : ∀ d ∈ D, α d = d ^ 2 ^ k)
    (hαodd : Odd (orderOf α)) (hcomm : ∀ x ∈ D, α (x⁻¹ * α x) = x⁻¹ * α x)
    {M c : ℕ} (hM : 1 ≤ M) (hc : c = 1 ∨ c = 3) (hc3 : c = 3 → 4 ≤ M)
    (hcN : c * Nat.card D = 2 ^ M - 1) : ∀ x ∈ D, α x = x := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set g0 : K := (g : K) with hg0
  have hg0D : g0 ∈ D := g.2
  have hord : orderOf g0 = Nat.card D := by
    have := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [← this]
    exact Subgroup.orderOf_coe g
  have hfix : α g0 = g0 :=
    twist_finish_elem α (hk g0 hg0D) hαodd (hcomm g0 hg0D) hM hc hc3 (by rw [hord]; exact hcN)
  intro x hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  have : x = g0 ^ j := by
    have := congrArg Subtype.val hj
    simpa using this.symm
  rw [this, map_zpow, hfix]

end CFSG.Quasithin.RonanF13
