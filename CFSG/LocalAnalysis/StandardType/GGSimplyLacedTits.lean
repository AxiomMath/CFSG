module

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

public import Mathlib.GroupTheory.Coxeter.Basic

public section

namespace CFSG.StandardType

variable {ι : Type}

@[expose] def GGSimplyLaced (M : CoxeterMatrix ι) : Prop :=
  ∀ i j : ι, i ≠ j → M.M i j = 2 ∨ M.M i j = 3

private lemma simple_inv {M : CoxeterMatrix ι} (i : ι) : (M.simple i)⁻¹ = M.simple i :=
  inv_eq_of_mul_eq_one_right (M.toCoxeterSystem.simple_mul_simple_self i)

private def titsE [DecidableEq ι] (i : ι) : ι → ℤ :=
  Pi.single i 1

private noncomputable def titsA [Fintype ι] (M : CoxeterMatrix ι) (i : ι) :
    (ι → ℤ) →ₗ[ℤ] ℤ where
  toFun v := 2 * v i - ∑ k, if M.M i k = 3 then v k else 0
  map_add' v w := by
    have hsum : (∑ k, if M.M i k = 3 then (v + w) k else 0) =
        (∑ k, if M.M i k = 3 then v k else 0) +
          (∑ k, if M.M i k = 3 then w k else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : M.M i k = 3 <;> simp [hk, Pi.add_apply]
    rw [Pi.add_apply, mul_add, hsum]
    ring
  map_smul' c v := by
    have hsum : (∑ k, if M.M i k = 3 then c * v k else 0) =
        c * (∑ k, if M.M i k = 3 then v k else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : M.M i k = 3 <;> simp [hk]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hsum]
    ring

private lemma titsA_apply [Fintype ι] (M : CoxeterMatrix ι) (i : ι) (v : ι → ℤ) :
    titsA M i v = 2 * v i - ∑ k, if M.M i k = 3 then v k else 0 := rfl

private lemma titsA_self [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) (i : ι) :
    titsA M i (titsE i) = 2 := by
  rw [titsA_apply]
  have hsum : (∑ k, if M.M i k = 3 then titsE i k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst hk
      simp [titsE, M.diagonal]
    · simp [titsE, Pi.single_eq_of_ne hk]
  rw [hsum, titsE, Pi.single_eq_same]
  ring

private lemma titsA_of_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) {i j : ι}
    (hij : i ≠ j) (h : M.M i j = 3) : titsA M i (titsE j) = -1 := by
  rw [titsA_apply]
  have hsum : (∑ k, if M.M i k = 3 then titsE j k else 0) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [titsE, h]
    · intro k _ hkj
      simp [titsE, Pi.single_eq_of_ne hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hsum, titsE]
  rw [Pi.single_eq_of_ne hij]
  ring

private lemma titsA_of_two [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) {i j : ι}
    (hij : i ≠ j) (h : M.M i j = 2) : titsA M i (titsE j) = 0 := by
  rw [titsA_apply]
  have hsum : (∑ k, if M.M i k = 3 then titsE j k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = j
    · subst hk
      simp [titsE, h]
    · simp [titsE, Pi.single_eq_of_ne hk]
  rw [hsum, titsE]
  rw [Pi.single_eq_of_ne hij]
  ring

private lemma titsA_sub [Fintype ι] (M : CoxeterMatrix ι) (i : ι) (v w : ι → ℤ) :
    titsA M i (v - w) = titsA M i v - titsA M i w :=
  map_sub (titsA M i) v w

private lemma titsA_smul [Fintype ι] (M : CoxeterMatrix ι) (i : ι) (c : ℤ) (v : ι → ℤ) :
    titsA M i (c • v) = c * titsA M i v := by
  rw [map_smul, zsmul_eq_mul]
  simp

private noncomputable def titsRefl [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) (i : ι) :
    Module.End ℤ (ι → ℤ) :=
  LinearMap.id - (titsA M i).smulRight (titsE i)

private lemma titsRefl_apply [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) (i : ι)
    (v : ι → ℤ) : titsRefl M i v = v - titsA M i v • titsE i := by
  simp [titsRefl, LinearMap.smulRight_apply]

private lemma titsA_titsRefl [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) (i : ι)
    (v : ι → ℤ) : titsA M i (titsRefl M i v) = - titsA M i v := by
  rw [titsRefl_apply, titsA_sub, titsA_smul, titsA_self]
  ring

private lemma titsRefl_sq [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) (i : ι) :
    titsRefl M i * titsRefl M i = 1 := by
  apply LinearMap.ext
  intro v
  change titsRefl M i (titsRefl M i v) = v
  rw [titsRefl_apply M i (titsRefl M i v), titsA_titsRefl M i v]
  rw [titsRefl_apply M i v, neg_smul]
  abel

private lemma titsRefl_titsE_self [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) (i : ι) :
    titsRefl M i (titsE i) = - titsE i := by
  rw [titsRefl_apply, titsA_self]
  rw [show (2 : ℤ) • titsE i = titsE i + titsE i by rw [two_smul]]
  abel

private lemma titsRefl_titsE_of_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) :
    titsRefl M i (titsE j) = titsE i + titsE j := by
  rw [titsRefl_apply, titsA_of_three M hij h]
  rw [show (-1 : ℤ) • titsE i = - titsE i by simp]
  abel

private lemma titsRefl_add_titsE_of_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) :
    titsRefl M i (titsE i + titsE j) = titsE j := by
  have ha : titsA M i (titsE i + titsE j) = 1 := by
    rw [map_add, titsA_self, titsA_of_three M hij h]
    norm_num
  rw [titsRefl_apply, ha]
  rw [show (1 : ℤ) • titsE i = titsE i by simp]
  abel

private lemma titsRefl_neg_titsE_of_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) :
    titsRefl M j (- titsE i) = - titsE i - titsE j := by
  have hji : M.M j i = 3 := by
    rw [CoxeterMatrix.symmetric]
    exact h
  have ha : titsA M j (- titsE i) = 1 := by
    rw [map_neg, titsA_of_three M (Ne.symm hij) hji]
    norm_num
  rw [titsRefl_apply, ha]
  rw [show (1 : ℤ) • titsE j = titsE j by simp]

private lemma titsRefl_comm [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) {i j : ι}
    (hij : i ≠ j) (h : M.M i j = 2) :
    titsRefl M i * titsRefl M j = titsRefl M j * titsRefl M i := by
  have hji : M.M j i = 2 := by
    rw [CoxeterMatrix.symmetric]
    exact h
  apply LinearMap.ext
  intro v
  change titsRefl M i (titsRefl M j v) = titsRefl M j (titsRefl M i v)
  have hai : titsA M i (titsRefl M j v) = titsA M i v := by
    rw [titsRefl_apply, titsA_sub, titsA_smul, titsA_of_two M hij h]
    rw [mul_zero, sub_zero]
  have haj : titsA M j (titsRefl M i v) = titsA M j v := by
    rw [titsRefl_apply, titsA_sub, titsA_smul, titsA_of_two M (Ne.symm hij) hji]
    rw [mul_zero, sub_zero]
  calc titsRefl M i (titsRefl M j v)
      = titsRefl M j v - titsA M i (titsRefl M j v) • titsE i := titsRefl_apply M i _
    _ = (v - titsA M j v • titsE j) - titsA M i v • titsE i := by
        rw [hai, titsRefl_apply M j v]
    _ = (v - titsA M i v • titsE i) - titsA M j v • titsE j := by abel
    _ = titsRefl M j (titsRefl M i v) := by
        rw [titsRefl_apply M j (titsRefl M i v), haj, titsRefl_apply M i v]

private lemma titsRefl_mul_pow_two [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι) {i j : ι}
    (hij : i ≠ j) (h : M.M i j = 2) : (titsRefl M i * titsRefl M j) ^ 2 = 1 := by
  have hc : titsRefl M i * titsRefl M j = titsRefl M j * titsRefl M i :=
    titsRefl_comm M hij h
  have hi : titsRefl M i * titsRefl M i = 1 := titsRefl_sq M i
  have hj : titsRefl M j * titsRefl M j = 1 := titsRefl_sq M j
  calc (titsRefl M i * titsRefl M j) ^ 2
      = titsRefl M i * (titsRefl M j * titsRefl M i) * titsRefl M j := by
        rw [pow_two]
        group
    _ = titsRefl M i * (titsRefl M i * titsRefl M j) * titsRefl M j := by
        rw [← hc]
    _ = (titsRefl M i * titsRefl M i) * (titsRefl M j * titsRefl M j) := by
        group
    _ = 1 := by
        rw [hi, hj]
        simp

private lemma titsA_sub_smul_sub_smul_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) (v : ι → ℤ) (c d : ℤ) :
    titsA M i (v - c • titsE i - d • titsE j) = titsA M i v - c * 2 + d := by
  rw [titsA_sub, titsA_sub, titsA_smul, titsA_smul, titsA_self,
    titsA_of_three M hij h]
  ring

private lemma titsRefl_braid_apply_of_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) (v : ι → ℤ) :
    titsRefl M i (titsRefl M j (titsRefl M i v)) =
      v - (titsA M i v + titsA M j v) • titsE i -
        (titsA M i v + titsA M j v) • titsE j := by
  have hji : M.M j i = 3 := by
    rw [CoxeterMatrix.symmetric]
    exact h
  have haj : titsA M j (titsRefl M i v) = titsA M j v + titsA M i v := by
    rw [titsRefl_apply, titsA_sub, titsA_smul, titsA_of_three M (Ne.symm hij) hji]
    ring
  have hvec : titsRefl M j (titsRefl M i v) =
      v - titsA M i v • titsE i - (titsA M j v + titsA M i v) • titsE j := by
    rw [titsRefl_apply M j (titsRefl M i v), haj, titsRefl_apply M i v]
  have hai : titsA M i (titsRefl M j (titsRefl M i v)) = titsA M j v := by
    rw [hvec, titsA_sub_smul_sub_smul_three M hij h]
    ring
  calc titsRefl M i (titsRefl M j (titsRefl M i v))
      = titsRefl M j (titsRefl M i v) -
          titsA M i (titsRefl M j (titsRefl M i v)) • titsE i := titsRefl_apply M i _
    _ = (v - titsA M i v • titsE i - (titsA M j v + titsA M i v) • titsE j) -
          titsA M j v • titsE i := by rw [hai, hvec]
    _ = v - (titsA M i v + titsA M j v) • titsE i -
          (titsA M i v + titsA M j v) • titsE j := by
        rw [add_comm (titsA M j v) (titsA M i v), add_smul, add_smul]
        abel

private lemma titsRefl_braid_of_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) :
    titsRefl M i * titsRefl M j * titsRefl M i =
      titsRefl M j * titsRefl M i * titsRefl M j := by
  have hji : M.M j i = 3 := by
    rw [CoxeterMatrix.symmetric]
    exact h
  apply LinearMap.ext
  intro v
  change titsRefl M i (titsRefl M j (titsRefl M i v)) =
    titsRefl M j (titsRefl M i (titsRefl M j v))
  calc titsRefl M i (titsRefl M j (titsRefl M i v))
      = v - (titsA M i v + titsA M j v) • titsE i -
          (titsA M i v + titsA M j v) • titsE j :=
        titsRefl_braid_apply_of_three M hij h v
    _ = titsRefl M j (titsRefl M i (titsRefl M j v)) := by
        rw [titsRefl_braid_apply_of_three M (Ne.symm hij) hji v]
        rw [add_comm (titsA M j v) (titsA M i v)]
        abel

private lemma titsRefl_mul_pow_three [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    {i j : ι} (hij : i ≠ j) (h : M.M i j = 3) :
    (titsRefl M i * titsRefl M j) ^ 3 = 1 := by
  have hbraid : titsRefl M i * titsRefl M j * titsRefl M i =
      titsRefl M j * titsRefl M i * titsRefl M j := titsRefl_braid_of_three M hij h
  have hi : titsRefl M i * titsRefl M i = 1 := titsRefl_sq M i
  have hj : titsRefl M j * titsRefl M j = 1 := titsRefl_sq M j
  calc (titsRefl M i * titsRefl M j) ^ 3
      = (titsRefl M i * titsRefl M j * titsRefl M i) *
        (titsRefl M j * titsRefl M i * titsRefl M j) := by
        rw [pow_succ, pow_succ, pow_one]
        group
    _ = (titsRefl M j * titsRefl M i * titsRefl M j) *
        (titsRefl M j * titsRefl M i * titsRefl M j) := by
        rw [hbraid]
    _ = 1 := by
        have hstep : (titsRefl M j * titsRefl M i * titsRefl M j) *
            (titsRefl M j * titsRefl M i * titsRefl M j) =
            titsRefl M j * titsRefl M i * (titsRefl M j * titsRefl M j) *
              titsRefl M i * titsRefl M j := by
          group
        rw [hstep, hj]
        have hstep2 : titsRefl M j * titsRefl M i * 1 * titsRefl M i *
            titsRefl M j = titsRefl M j * (titsRefl M i * titsRefl M i) *
              titsRefl M j := by
          group
        rw [hstep2, hi]
        have hstep3 : titsRefl M j * 1 * titsRefl M j =
            titsRefl M j * titsRefl M j := by group
        rw [hstep3, hj]

private lemma titsRefl_isLiftable [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGSimplyLaced M) : M.IsLiftable (titsRefl M) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simpa [CoxeterMatrix.diagonal] using titsRefl_sq M i
  · rcases hM i j hij with h2 | h3
    · rw [h2]
      exact titsRefl_mul_pow_two M hij h2
    · rw [h3]
      exact titsRefl_mul_pow_three M hij h3

private noncomputable def titsRep [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGSimplyLaced M) : M.Group →* Module.End ℤ (ι → ℤ) :=
  M.toCoxeterSystem.lift ⟨titsRefl M, titsRefl_isLiftable hM⟩

private lemma titsRep_simple [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGSimplyLaced M) (i : ι) :
    titsRep hM (M.simple i) = titsRefl M i := by
  rw [titsRep]
  simpa using M.toCoxeterSystem.lift_apply_simple (M := M) (f := titsRefl M)
    (hf := titsRefl_isLiftable hM) i

theorem ggSimplyLaced_simple_comm {M : CoxeterMatrix ι} {i j : ι} (h : M.M i j = 2) :
    M.simple i * M.simple j = M.simple j * M.simple i := by
  have hsq : (M.simple i * M.simple j) ^ 2 = 1 := by
    simpa [h] using M.toCoxeterSystem.simple_mul_simple_pow i j
  have hxx : (M.simple i * M.simple j) * (M.simple i * M.simple j) = 1 := by
    simpa [pow_two] using hsq
  calc M.simple i * M.simple j
      = (M.simple i * M.simple j)⁻¹ := (inv_eq_of_mul_eq_one_right hxx).symm
    _ = (M.simple j)⁻¹ * (M.simple i)⁻¹ := by rw [mul_inv_rev]
    _ = M.simple j * M.simple i := by rw [simple_inv, simple_inv]

theorem ggSimplyLaced_braid {M : CoxeterMatrix ι} {i j : ι} (h : M.M i j = 3) :
    M.simple i * M.simple j * M.simple i = M.simple j * M.simple i * M.simple j := by
  have h3 : (M.simple i * M.simple j) ^ 3 = 1 := by
    simpa [h] using M.toCoxeterSystem.simple_mul_simple_pow i j
  have hprod : (M.simple i * M.simple j * M.simple i) *
      (M.simple j * M.simple i * M.simple j) = 1 := by
    calc (M.simple i * M.simple j * M.simple i) *
          (M.simple j * M.simple i * M.simple j)
        = (M.simple i * M.simple j) ^ 3 := by
          rw [pow_succ, pow_succ, pow_one]
          group
      _ = 1 := h3
  have hi : M.simple i * M.simple i = 1 := by
    simpa using M.toCoxeterSystem.simple_mul_simple_self i
  have hj : M.simple j * M.simple j = 1 := by
    simpa using M.toCoxeterSystem.simple_mul_simple_self j
  have hsq : (M.simple j * M.simple i * M.simple j) *
      (M.simple j * M.simple i * M.simple j) = 1 := by
    have hstep : (M.simple j * M.simple i * M.simple j) *
        (M.simple j * M.simple i * M.simple j) =
        M.simple j * M.simple i * (M.simple j * M.simple j) *
          M.simple i * M.simple j := by group
    rw [hstep, hj]
    have hstep2 : M.simple j * M.simple i * 1 * M.simple i * M.simple j =
        M.simple j * (M.simple i * M.simple i) * M.simple j := by group
    rw [hstep2, hi]
    have hstep3 : M.simple j * 1 * M.simple j = M.simple j * M.simple j := by group
    rw [hstep3, hj]
  have hinv : (M.simple j * M.simple i * M.simple j)⁻¹ =
      M.simple j * M.simple i * M.simple j :=
    inv_eq_of_mul_eq_one_right hsq
  exact (eq_inv_of_mul_eq_one_left hprod).trans hinv

theorem ggSimplyLaced_simple_injective [Finite ι] {M : CoxeterMatrix ι} (hM : GGSimplyLaced M) :
    Function.Injective M.simple := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  intro i j hij
  by_contra hne
  have hσ : titsRefl M i = titsRefl M j := by
    have h := congrArg (titsRep hM) hij
    simpa [titsRep_simple] using h
  have hcoord : (titsRefl M i (titsE i)) i = (titsRefl M j (titsE i)) i := by
    rw [hσ]
  have hleft : (titsRefl M i (titsE i)) i = -1 := by
    rw [titsRefl_apply, titsA_self]
    rw [Pi.sub_apply, Pi.smul_apply]
    rw [show (titsE i) i = 1 by simp [titsE]]
    norm_num
  have hright : (titsRefl M j (titsE i)) i = 1 := by
    rw [titsRefl_apply]
    rw [Pi.sub_apply, Pi.smul_apply]
    rw [show (titsE i) i = 1 by simp [titsE]]
    rw [show (titsE j) i = 0 by simp [titsE, Pi.single_eq_of_ne hne]]
    simp
  rw [hleft, hright] at hcoord
  norm_num at hcoord

theorem ggSimplyLaced_simple_noncomm [Finite ι] {M : CoxeterMatrix ι} (hM : GGSimplyLaced M)
    {i j : ι} (h : M.M i j = 3) : M.simple i * M.simple j ≠ M.simple j * M.simple i := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hne : i ≠ j := by
    intro heq
    subst heq
    rw [M.diagonal] at h
    norm_num at h
  have hji : M.M j i = 3 := by
    rw [CoxeterMatrix.symmetric]
    exact h
  intro hcomm
  have hσ : titsRefl M i * titsRefl M j = titsRefl M j * titsRefl M i := by
    have h := congrArg (titsRep hM) hcomm
    simpa [map_mul, titsRep_simple] using h
  have hlhs : (titsRefl M i * titsRefl M j) (titsE i) = titsE j := by
    rw [Module.End.mul_apply, titsRefl_titsE_of_three M (Ne.symm hne) hji]
    rw [add_comm (titsE j) (titsE i)]
    rw [titsRefl_add_titsE_of_three M hne h]
  have hrhs : (titsRefl M j * titsRefl M i) (titsE i) = - titsE i - titsE j := by
    rw [Module.End.mul_apply, titsRefl_titsE_self M i,
      titsRefl_neg_titsE_of_three M hne h]
  have hcoord : ((titsRefl M i * titsRefl M j) (titsE i)) i =
      ((titsRefl M j * titsRefl M i) (titsE i)) i := by
    rw [hσ]
  rw [hlhs, hrhs] at hcoord
  have h0 : (titsE j) i = 0 := by
    simp [titsE, Pi.single_eq_of_ne hne]
  have hneg : (- titsE i - titsE j) i = -1 := by
    rw [Pi.sub_apply, Pi.neg_apply]
    rw [show (titsE i) i = 1 by simp [titsE]]
    rw [h0]
    norm_num
  rw [h0, hneg] at hcoord
  norm_num at hcoord

end CFSG.StandardType

end
