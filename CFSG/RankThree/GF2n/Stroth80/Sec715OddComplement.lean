module

public import CFSG.ClassicalGroups.F2Fixed

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec715Torus

open CFSG.ClassicalGroups.F2Fixed

section OddComplement

variable {Γ M : Type*} [Group Γ] [AddCommGroup M] [DistribMulAction Γ M]

theorem sec715_pow_smul_sub_eq_comm (τ : Γ) (m : M) (i : ℕ) :
    τ ^ i • m - m = comm M τ (∑ j ∈ Finset.range i, τ ^ j • m) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, map_add, ← ih, comm_apply, ← mul_smul, ← pow_succ']
    abel

theorem sec715_smul_sum_pow_eq_self (τ : Γ) {n : ℕ} (hn : τ ^ n = 1) (m : M) :
    τ • ∑ i ∈ Finset.range n, τ ^ i • m = ∑ i ∈ Finset.range n, τ ^ i • m := by
  rw [Finset.smul_sum]
  simp_rw [← mul_smul, ← pow_succ']
  have h1 := Finset.sum_range_succ (fun i => τ ^ i • m) n
  have h2 := Finset.sum_range_succ' (fun i => τ ^ i • m) n
  rw [hn, one_smul, pow_zero, one_smul] at *
  have h3 : ∑ i ∈ Finset.range n, τ ^ (i + 1) • m + m = ∑ i ∈ Finset.range n, τ ^ i • m + m := by
    rw [← h2, h1]
  exact add_right_cancel h3

theorem sec715_sum_pow_smul_comm (τ : Γ) (n : ℕ) (m : M) :
    ∑ i ∈ Finset.range n, τ ^ i • comm M τ m = τ ^ n • m - m := by
  have h : ∀ i : ℕ, τ ^ i • comm M τ m = τ ^ (i + 1) • m - τ ^ i • m := by
    intro i
    rw [comm_apply, smul_sub, ← mul_smul, ← pow_succ]
  simp_rw [h]
  rw [Finset.sum_range_sub (fun i => τ ^ i • m) n]
  simp

theorem sec715_sum_const_eq_self (h2 : ∀ m : M, m + m = 0) {n : ℕ} (hn : Odd n) (m : M) :
    ∑ _i ∈ Finset.range n, m = m := by
  obtain ⟨k, rfl⟩ := hn
  have h : ∀ j : ℕ, (2 * j) • m = 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [mul_add, mul_one, add_nsmul, ih, two_nsmul, h2, add_zero]
  rw [Finset.sum_const, Finset.card_range, succ_nsmul, h k, zero_add]

theorem sec715_sub_sum_pow_mem_range (h2 : ∀ m : M, m + m = 0) (τ : Γ) {n : ℕ} (hn : Odd n)
    (m : M) :
    m - ∑ i ∈ Finset.range n, τ ^ i • m ∈ (comm M τ).range := by
  have h1 : m - ∑ i ∈ Finset.range n, τ ^ i • m =
      -∑ i ∈ Finset.range n, (τ ^ i • m - m) := by
    rw [Finset.sum_sub_distrib, sec715_sum_const_eq_self h2 hn m]
    abel
  rw [h1]
  refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun i _ => ?_)
  rw [sec715_pow_smul_sub_eq_comm]
  exact ⟨_, rfl⟩

theorem sec715_inf_range_comm_fixedSub (h2 : ∀ m : M, m + m = 0) (τ : Γ) {n : ℕ} (hn : τ ^ n = 1)
    (hodd : Odd n) : (comm M τ).range ⊓ fixedSub M {τ} = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨⟨m, rfl⟩, hy⟩
  rw [AddSubgroup.mem_bot]
  have h1 : ∑ i ∈ Finset.range n, τ ^ i • comm M τ m = 0 := by
    rw [sec715_sum_pow_smul_comm, hn, one_smul, sub_self]
  have hfix : ∀ i : ℕ, τ ^ i • comm M τ m = comm M τ m := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, mul_smul, hy τ rfl, ih]
  simp_rw [hfix] at h1
  rw [sec715_sum_const_eq_self h2 hodd] at h1
  exact h1

theorem sec715_isCompl_range_comm_fixedSub (h2 : ∀ m : M, m + m = 0) (τ : Γ) {n : ℕ}
    (hn : τ ^ n = 1)
    (hodd : Odd n) : IsCompl (comm M τ).range (fixedSub M {τ}) := by
  refine ⟨disjoint_iff.mpr (sec715_inf_range_comm_fixedSub h2 τ hn hodd), codisjoint_iff.mpr ?_⟩
  rw [eq_top_iff]
  intro m _
  have hf : ∑ i ∈ Finset.range n, τ ^ i • m ∈ fixedSub M {τ} := by
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact sec715_smul_sum_pow_eq_self τ hn m
  have : m = (m - ∑ i ∈ Finset.range n, τ ^ i • m) + ∑ i ∈ Finset.range n, τ ^ i • m := by abel
  rw [this]
  exact AddSubgroup.add_mem_sup (sec715_sub_sum_pow_mem_range h2 τ hodd m) hf

theorem sec715_comm_comm_swap {a b : Γ} (hab : a * b = b * a) (m : M) :
    comm M b (comm M a m) = comm M a (comm M b m) := by
  have h : b • a • m = a • b • m := by rw [← mul_smul, ← mul_smul, hab]
  simp only [comm_apply, smul_sub, h]
  abel

theorem sec715_range_comm_eq_of_commute (h2 : ∀ m : M, m + m = 0) {τ σ : Γ} {n k : ℕ}
    (hτ : τ ^ n = 1) (hn : Odd n) (hσ : σ ^ k = 1) (hk : Odd k) (hcomm : τ * σ = σ * τ)
    (hfix : fixedSub M {τ} = fixedSub M {σ}) :
    (comm M τ).range = (comm M σ).range := by
  have key : ∀ (a b : Γ) {p : ℕ}, a ^ p = 1 → Odd p → a * b = b * a →
      fixedSub M {a} = fixedSub M {b} → (comm M b).range ≤ (comm M a).range := by
    intro a b p ha hp hab hf
    rintro _ ⟨m, rfl⟩
    have hm : m ∈ (comm M a).range ⊔ fixedSub M {a} := by
      rw [(sec715_isCompl_range_comm_fixedSub h2 a ha hp).sup_eq_top]
      trivial
    obtain ⟨y, ⟨m', rfl⟩, f, hf', rfl⟩ := AddSubgroup.mem_sup.mp hm
    have hfb : f ∈ (comm M b).ker := by
      rw [ker_comm]
      exact hf ▸ hf'
    rw [map_add, AddMonoidHom.mem_ker.mp hfb, add_zero, sec715_comm_comm_swap hab]
    exact ⟨_, rfl⟩
  exact le_antisymm (key σ τ hσ hk hcomm.symm hfix.symm) (key τ σ hτ hn hcomm hfix)

end OddComplement

end CFSG.RankThree.GF2n.Stroth80.Sec715Torus
