module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Module.NatInt

public section

namespace CFSG.RankThree.PartOne.K1214

open Finset

variable {M : Type*} [AddCommGroup M]

@[expose] def PD (p k : ℕ) (α : AddMonoid.End M) : Prop :=
  ∀ v : M, ∃ w : M, α v = (p ^ k) • w

theorem PD.mono {p k l : ℕ} {α : AddMonoid.End M} (hα : PD p k α) (h : l ≤ k) : PD p l α := by
  intro v
  obtain ⟨w, hw⟩ := hα v
  refine ⟨(p ^ (k - l)) • w, ?_⟩
  rw [hw, ← mul_nsmul', ← pow_add, Nat.add_sub_cancel' h]

theorem PD.zero_left {p : ℕ} (α : AddMonoid.End M) : PD p 0 α :=
  fun v => ⟨α v, by rw [pow_zero, one_nsmul]⟩

theorem PD.add {p k : ℕ} {α β : AddMonoid.End M} (hα : PD p k α) (hβ : PD p k β) :
    PD p k (α + β) := by
  intro v
  obtain ⟨w, hw⟩ := hα v
  obtain ⟨w', hw'⟩ := hβ v
  refine ⟨w + w', ?_⟩
  show α v + β v = _
  rw [hw, hw', nsmul_add]

theorem PD.nsmul {p k : ℕ} {α : AddMonoid.End M} (hα : PD p k α) (n : ℕ) : PD p k (n • α) := by
  intro v
  obtain ⟨w, hw⟩ := hα v
  refine ⟨n • w, ?_⟩
  show n • α v = _
  rw [hw, smul_comm]

theorem PD.mul {p k l : ℕ} {α β : AddMonoid.End M} (hα : PD p k α) (hβ : PD p l β) :
    PD p (k + l) (α * β) := by
  intro v
  obtain ⟨w, hw⟩ := hβ v
  obtain ⟨w', hw'⟩ := hα w
  refine ⟨w', ?_⟩
  show α (β v) = _
  rw [hw, map_nsmul, hw', ← mul_nsmul', ← pow_add, add_comm]

theorem PD.pow {p k : ℕ} {α : AddMonoid.End M} (hα : PD p k α) (m : ℕ) :
    PD p ((m + 1) * k) (α ^ (m + 1)) := by
  induction m with
  | zero => simpa using hα
  | succ m ih =>
    have := ih.mul hα
    rw [← pow_succ] at this
    convert this using 1
    ring

theorem PD.smul_p {p k : ℕ} {α : AddMonoid.End M} (hα : PD p k α) : PD p (k + 1) (p • α) := by
  intro v
  obtain ⟨w, hw⟩ := hα v
  refine ⟨w, ?_⟩
  show p • α v = _
  rw [hw, ← mul_nsmul', ← pow_succ']

theorem PD.sum {p k : ℕ} {ι : Type*} (s : Finset ι) {α : ι → AddMonoid.End M}
    (h : ∀ i ∈ s, PD p k (α i)) : PD p k (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro v; exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem one_add_pow_eq {n : ℕ} (hn : 2 ≤ n) (δ : AddMonoid.End M) :
    (1 + δ) ^ n = 1 + n • δ + ∑ j ∈ Finset.Ico 2 (n + 1), (n.choose j) • δ ^ j := by
  have h := (Commute.one_right δ).add_pow n
  rw [add_comm] at h
  have e1 : ∀ m : ℕ, δ ^ m * ((n.choose m : ℕ) : AddMonoid.End M) = (n.choose m) • δ ^ m :=
    fun m => by rw [nsmul_eq_mul, (Nat.cast_commute _ _).eq]
  simp only [one_pow, mul_one, e1] at h
  rw [h, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Nat.choose_zero_right, one_nsmul, zero_add, Nat.choose_one_right, pow_one]
  rw [add_assoc]

theorem PD.neg {p k : ℕ} {α : AddMonoid.End M} (hα : PD p k α) : PD p k (-α) := by
  intro v
  obtain ⟨w, hw⟩ := hα v
  refine ⟨-w, ?_⟩
  show -(α v) = _
  rw [hw, smul_neg]

theorem pd_div_p {p e k : ℕ} (hH1 : ∀ v : M, p • v = 0 → ∃ y, v = (p ^ (e - 1)) • y)
    (hk : k ≤ e - 1) {α : AddMonoid.End M} (h : PD p (k + 1) (p • α)) : PD p k α := by
  intro v
  obtain ⟨w, hw⟩ := h v
  have hw' : p • α v = (p ^ (k + 1)) • w := hw
  have h1 : p • (α v - (p ^ k) • w) = 0 := by
    rw [smul_sub, hw', ← mul_nsmul', ← pow_succ', sub_self]
  obtain ⟨y, hy⟩ := hH1 _ h1
  refine ⟨w + (p ^ (e - 1 - k)) • y, ?_⟩
  rw [smul_add, ← mul_nsmul', ← pow_add, Nat.add_sub_cancel' (by omega : k ≤ e - 1), ← hy]
  abel

theorem pd_step {p e k : ℕ} (hp : p.Prime)
    (hH1 : ∀ v : M, p • v = 0 → ∃ y, v = (p ^ (e - 1)) • y) (hk : k + 1 ≤ e - 1)
    {δ : AddMonoid.End M} (hg : (1 + δ) ^ p = 1)
    (hmid : ∀ j, 2 ≤ j → j < p → PD p (k + 1) (δ ^ j)) (htop : PD p (k + 2) (δ ^ p)) :
    PD p (k + 1) δ := by
  have h2 : 2 ≤ p := hp.two_le
  have hbin := one_add_pow_eq h2 δ
  rw [hg] at hbin
  rw [Finset.sum_Ico_succ_top h2, Nat.choose_self, one_smul] at hbin
  set S : AddMonoid.End M := ∑ j ∈ Finset.Ico 2 p, (p.choose j) • δ ^ j with hS
  have hpδ : p • δ = -(S + δ ^ p) := by
    have h3 : p • δ + (S + δ ^ p) = 0 := by
      calc p • δ + (S + δ ^ p) = (1 + p • δ + (S + δ ^ p)) - 1 := by abel
        _ = 1 - 1 := by rw [← hbin]
        _ = 0 := sub_self 1
    exact eq_neg_of_add_eq_zero_left h3
  have hS' : PD p (k + 2) S := by
    refine PD.sum _ fun j hj => ?_
    obtain ⟨hj2, hjp⟩ := Finset.mem_Ico.1 hj
    obtain ⟨c', hc'⟩ := hp.dvd_choose_self (by omega : j ≠ 0) hjp
    have := ((hmid j hj2 hjp).nsmul c').smul_p
    rw [hc', mul_smul]
    exact this
  have hpd : PD p (k + 2) (p • δ) := by
    rw [hpδ]
    exact (hS'.add htop).neg
  exact pd_div_p hH1 hk hpd

theorem pd_induct {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hH1 : ∀ v : M, p • v = 0 → ∃ y, v = (p ^ (e - 1)) • y) {δ : AddMonoid.End M}
    (hg : (1 + δ) ^ p = 1) (h1 : PD p 1 δ) : ∀ k, 1 ≤ k → k ≤ e - 1 → PD p k δ := by
  intro k hk1 hke
  induction k, hk1 using Nat.le_induction with
  | base => exact h1
  | succ k hk ih =>
    have hδk : PD p k δ := ih (by omega)
    refine pd_step hp hH1 hke hg ?_ ?_
    · intro j hj2 _
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      refine (hδk.pow m).mono ?_
      nlinarith
    · obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      have := hδk.pow m
      rw [← hm] at this
      refine this.mono ?_
      rw [hm] at hp5 ⊢
      nlinarith

end CFSG.RankThree.PartOne.K1214
