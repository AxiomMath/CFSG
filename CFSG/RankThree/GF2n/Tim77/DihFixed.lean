module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.GF2n.Tim77

theorem dih_fixed_reflection {R : Type*} [Group R] {β γ : R} (hβ : β * β = 1) (hγ : γ * γ = 1)
    (hk : Odd (orderOf (β * γ))) (φ : MulAut R) (hφ : φ * φ = 1) (hβγ : φ β = γ) :
    ∃ ρ ∈ Subgroup.closure {β, γ}, ρ * ρ = 1 ∧ ρ * β * ρ = γ ∧ φ ρ = ρ ∧
      ∃ g ∈ Subgroup.closure {β, γ}, ρ = g * β * g⁻¹ := by
  obtain ⟨n, hn⟩ := hk
  obtain ⟨r, hr⟩ : ∃ r : R, r = β * γ := ⟨_, rfl⟩
  rw [← hr] at hn
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = (n : ℤ) + 1 := ⟨_, rfl⟩
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  have hγi : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ
  have hrk : r ^ (2 * (n : ℤ) + 1) = 1 := by
    have h : r ^ (2 * n + 1) = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one r
    have e : (2 * (n : ℤ) + 1) = ((2 * n + 1 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast, h]
  have hpow : r ^ (j * (2 * (n : ℤ) + 1)) = 1 := by
    rw [mul_comm j (2 * (n : ℤ) + 1), zpow_mul, hrk, one_zpow]
  have hrβ : β * r * β = r⁻¹ := by
    rw [hr, mul_inv_rev, hβi, hγi, ← mul_assoc β β γ, hβ, one_mul]
  have hγr : γ = β * r := by
    rw [hr, ← mul_assoc, hβ, one_mul]
  have hconj : ∀ m : ℤ, β * r ^ m * β = r ^ (-m) := by
    intro m
    have h := conj_zpow (a := β) (b := r) (i := m)
    rw [hβi, hrβ, inv_zpow] at h
    rw [zpow_neg]
    exact h.symm
  have hconjβ : ∀ m : ℤ, r ^ m * β = β * r ^ (-m) := by
    intro m
    have h := hconj (-m)
    rw [neg_neg] at h
    rw [← h]
    simp only [mul_assoc, hβ, mul_one]
  have hj2 : j + j = (2 * (n : ℤ) + 1) + 1 := by
    rw [hj]
    omega
  have hjk : r ^ j * r ^ j = r := by
    rw [← zpow_add, hj2, zpow_add, hrk, one_mul, zpow_one]
  have hexp : j * j + j * j = j + j * (2 * (n : ℤ) + 1) := by
    rw [hj]
    ring
  have hφφ : ∀ x : R, φ (φ x) = x := by
    intro x
    have h := congrArg (fun ψ : MulAut R => ψ x) hφ
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  have hφγ : φ γ = β := by
    rw [← hβγ]
    exact hφφ β
  have hφr : φ r = r⁻¹ := by
    rw [hr, map_mul, hβγ, hφγ, mul_inv_rev, hβi, hγi]
  have hmemβ : β ∈ Subgroup.closure ({β, γ} : Set R) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmemγ : γ ∈ Subgroup.closure ({β, γ} : Set R) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hmemr : r ∈ Subgroup.closure ({β, γ} : Set R) := by
    rw [hr]
    exact Subgroup.mul_mem _ hmemβ hmemγ
  have hρρ : β * r ^ j * (β * r ^ j) = 1 := by
    rw [show β * r ^ j * (β * r ^ j) = (β * r ^ j * β) * r ^ j by simp only [mul_assoc],
      hconj j, zpow_neg, inv_mul_cancel]
  have hρβρ : β * r ^ j * β * (β * r ^ j) = γ := by
    have h : β * r ^ j * β * (β * r ^ j) = β * (r ^ j * r ^ j) := by
      rw [show β * r ^ j * β * (β * r ^ j) = β * r ^ j * (β * β) * r ^ j by
        simp only [mul_assoc], hβ]
      simp only [mul_assoc, mul_one]
    rw [h, hjk, hγr]
  have h2 : r * (r ^ j)⁻¹ = r ^ j := by
    rw [mul_inv_eq_iff_eq_mul, hjk]
  have hφρ : φ (β * r ^ j) = β * r ^ j := by
    rw [map_mul, map_zpow, hβγ, hφr, inv_zpow, hγr, mul_assoc, h2]
  have hgβ : r ^ (-(j * j)) * β = β * r ^ (j * j) := by
    have h := hconjβ (-(j * j))
    rw [neg_neg] at h
    exact h
  refine ⟨β * r ^ j, Subgroup.mul_mem _ hmemβ (Subgroup.zpow_mem _ hmemr j), hρρ, hρβρ, hφρ,
    r ^ (-(j * j)), Subgroup.zpow_mem _ hmemr _, ?_⟩
  rw [hgβ, ← zpow_neg, neg_neg, mul_assoc, ← zpow_add, hexp, zpow_add, hpow, mul_one]

end CFSG.RankThree.GF2n.Tim77
