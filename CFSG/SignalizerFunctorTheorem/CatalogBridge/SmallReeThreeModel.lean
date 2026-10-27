module

public import CFSG.LieType.Ree.SmallReeThreePerm

public section

open CFSG.LieType.Ree Equiv
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def srG : Perm (Fin 56) := srSigma0 * srSigmaN

@[expose] def srW : Perm (Fin 56) := srSigma0 * srSigmaN * srSigma0⁻¹ * srSigmaN

@[expose] def srT : Perm (Fin 56) :=
  srSigma0⁻¹ * srSigmaN * srSigma0 * srSigmaN * srSigma0⁻¹ * srSigmaN * srSigma0

@[expose] def srTi (i : ℕ) : Perm (Fin 56) := srG ^ i * srT * (srG ^ i)⁻¹

theorem srG_pow_seven : srG ^ 7 = 1 := by
  unfold srG
  decide +kernel

theorem srG_ne_one : srG ≠ 1 := by
  unfold srG
  decide +kernel

theorem orderOf_srG : orderOf srG = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime srG_pow_seven srG_ne_one

theorem srW_pow_nine : srW ^ 9 = 1 := by
  unfold srW
  decide +kernel

theorem srW_pow_three_ne_one : srW ^ 3 ≠ 1 := by
  unfold srW
  decide +kernel

theorem orderOf_srW : orderOf srW = 9 := by
  have h := orderOf_eq_prime_pow (p := 3) (n := 1) (x := srW)
    (by simpa using srW_pow_three_ne_one) (by simpa using srW_pow_nine)
  simpa using h

theorem srT_sq : srT ^ 2 = 1 := by
  unfold srT
  decide +kernel

theorem srTi_zero : srTi 0 = srT := by
  simp [srTi]

theorem srTi_seven : srTi 7 = srT := by
  simp [srTi, srG_pow_seven]

theorem srTi_succ (i : ℕ) : srG * srTi i * srG⁻¹ = srTi (i + 1) := by
  simp only [srTi, pow_succ', mul_inv_rev, mul_assoc]

theorem srTi_comm : ∀ i j : Fin 7, srTi i * srTi j = srTi j * srTi i := by
  unfold srTi srT srG
  decide +kernel

theorem srG_srT_ne : srG * srT * srG⁻¹ ≠ srT := by
  unfold srG srT
  decide +kernel

theorem srTi_sq (i : ℕ) : srTi i ^ 2 = 1 := by
  rw [srTi, conj_pow, srT_sq]
  group

theorem srSigma0_mem : srSigma0 ∈ srP := Subgroup.subset_closure (by simp)

theorem srSigmaN_mem : srSigmaN ∈ srP := Subgroup.subset_closure (by simp)

theorem srG_mem : srG ∈ srP := srP.mul_mem srSigma0_mem srSigmaN_mem

theorem srW_mem : srW ∈ srP :=
  srP.mul_mem (srP.mul_mem (srP.mul_mem srSigma0_mem srSigmaN_mem) (srP.inv_mem srSigma0_mem))
    srSigmaN_mem

theorem srT_mem : srT ∈ srP := by
  have h0 := srSigma0_mem
  have hn := srSigmaN_mem
  have hi := srP.inv_mem h0
  exact srP.mul_mem (srP.mul_mem (srP.mul_mem (srP.mul_mem (srP.mul_mem (srP.mul_mem hi hn) h0) hn)
    hi) hn) h0

theorem srTi_mem (i : ℕ) : srTi i ∈ srP :=
  srP.mul_mem (srP.mul_mem (srP.pow_mem srG_mem i) srT_mem) (srP.inv_mem (srP.pow_mem srG_mem i))

theorem srTi_mod (i : ℕ) : srTi i = srTi (i % 7) := by
  simp only [srTi]
  rw [← orderOf_srG, pow_mod_orderOf]

theorem srTi_comm' (i j : ℕ) : srTi i * srTi j = srTi j * srTi i := by
  rw [srTi_mod i, srTi_mod j]
  exact srTi_comm ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩

theorem srP_data :
    ∃ (g w : srP) (A : Subgroup srP), orderOf g = 7 ∧ orderOf w = 9 ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ (∀ x ∈ A, x ^ 2 = 1) ∧
      (∀ x ∈ A, g * x * g⁻¹ ∈ A) ∧ ∃ x ∈ A, g * x * g⁻¹ ≠ x := by
  set S : Set srP := Set.range fun i : ℕ => (⟨srTi i, srTi_mem i⟩ : srP) with hS
  have hpw : S.Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact Subtype.ext (srTi_comm' i j)
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    have := Subgroup.isMulCommutative_closure hpw
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
  refine ⟨⟨srG, srG_mem⟩, ⟨srW, srW_mem⟩, Subgroup.closure S, ?_, ?_, hcomm, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk, orderOf_srG]
  · rw [Subgroup.orderOf_mk, orderOf_srW]
  · intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 2 = 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact Subtype.ext (srTi_sq i)
    · exact one_pow _
    · intro y z hy hz hy' hz'
      rw [(show Commute y z from hcomm y hy z hz).mul_pow, hy', hz', one_mul]
    · intro y hy hy'
      rw [inv_pow, hy', inv_one]
  · intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => (⟨srG, srG_mem⟩ : srP) * x * (⟨srG, srG_mem⟩ : srP)⁻¹ ∈ Subgroup.closure S)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i + 1, Subtype.ext (srTi_succ i).symm⟩
    · simp
    · intro y z _ _ hy' hz'
      have : (⟨srG, srG_mem⟩ : srP) * (y * z) * (⟨srG, srG_mem⟩ : srP)⁻¹ =
          ((⟨srG, srG_mem⟩ : srP) * y * (⟨srG, srG_mem⟩ : srP)⁻¹) *
            ((⟨srG, srG_mem⟩ : srP) * z * (⟨srG, srG_mem⟩ : srP)⁻¹) := by group
      rw [this]
      exact (Subgroup.closure S).mul_mem hy' hz'
    · intro y _ hy'
      have : (⟨srG, srG_mem⟩ : srP) * y⁻¹ * (⟨srG, srG_mem⟩ : srP)⁻¹ =
          ((⟨srG, srG_mem⟩ : srP) * y * (⟨srG, srG_mem⟩ : srP)⁻¹)⁻¹ := by group
      rw [this]
      exact (Subgroup.closure S).inv_mem hy'
  · refine ⟨⟨srT, srT_mem⟩, Subgroup.subset_closure ⟨0, Subtype.ext srTi_zero⟩, fun h => ?_⟩
    exact srG_srT_ne (congrArg Subtype.val h)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
