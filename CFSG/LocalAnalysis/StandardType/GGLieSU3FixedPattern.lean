module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

public section

namespace CFSG.StandardType

open Matrix

private lemma ggLieSU3Fixed_diag_apply_eq {K : Type} [Field K]
    {A : Matrix (Fin 4) (Fin 4) K} (hA : A.IsDiag) (g : Matrix (Fin 4) (Fin 4) K)
    (hg : g * A = A * g) {i j : Fin 4} (hij : g i j ≠ 0) : A i i = A j j := by
  have h1 : (g * A) i j = g i j * A j j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j
      (fun k _ hkj => by rw [hA hkj, mul_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)]
  have h2 : (A * g) i j = A i i * g i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i
      (fun k _ hki => by rw [hA hki.symm, zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
  have h : g i j * A j j = A i i * g i j := by
    rw [← h1, ← h2]; exact congrArg (fun M => M i j) hg
  have hzero : g i j * (A j j - A i i) = 0 := by
    rw [mul_sub, h, mul_comm (A i i) (g i j), sub_self]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hij)).symm

private lemma ggLieSU3Fixed_block {K : Type} [Field K] {z d : GL (Fin 4) K}
    (hzd : (z : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hdd : (d : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (H : Subgroup (GL (Fin 4) K)) (hHz : ∀ g ∈ H, g * z = z * g)
    (hHd : ∀ g ∈ H, g * d = d * g) {g : GL (Fin 4) K} (hg : g ∈ H) {i j : Fin 4}
    (hij : (g : Matrix (Fin 4) (Fin 4) K) i j ≠ 0) :
    ((z : Matrix (Fin 4) (Fin 4) K) i i, (d : Matrix (Fin 4) (Fin 4) K) i i) =
      ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j) :=
  Prod.ext
    (ggLieSU3Fixed_diag_apply_eq hzd (g : Matrix (Fin 4) (Fin 4) K)
      (by simpa only [GeneralLinearGroup.coe_mul] using
        congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) (hHz g hg)) hij)
    (ggLieSU3Fixed_diag_apply_eq hdd (g : Matrix (Fin 4) (Fin 4) K)
      (by simpa only [GeneralLinearGroup.coe_mul] using
        congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) (hHd g hg)) hij)

private lemma ggLieSU3Fixed_diag_cube {K : Type} [Field K] {z : GL (Fin 4) K}
    (hzd : (z : Matrix (Fin 4) (Fin 4) K).IsDiag) (hz3 : z ^ 3 = 1) (i : Fin 4) :
    (z : Matrix (Fin 4) (Fin 4) K) i i ^ 3 = 1 := by
  have hZ3 : (z : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz3]; rfl
  let dd : Fin 4 → K := fun j => (z : Matrix (Fin 4) (Fin 4) K) j j
  have hdiag : (z : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal dd :=
    ((Matrix.isDiag_iff_diagonal_diag _).mp hzd).symm
  have hpow : (z : Matrix (Fin 4) (Fin 4) K) ^ 3 = Matrix.diagonal (dd ^ 3) := by
    conv_lhs => rw [hdiag]
    rw [Matrix.diagonal_pow]
  calc (z : Matrix (Fin 4) (Fin 4) K) i i ^ 3
      = (dd ^ 3) i := rfl
    _ = (Matrix.diagonal (dd ^ 3)) i i := by rw [Matrix.diagonal_apply, if_pos rfl]
    _ = ((z : Matrix (Fin 4) (Fin 4) K) ^ 3) i i := by rw [hpow]
    _ = (1 : Matrix (Fin 4) (Fin 4) K) i i := by rw [hZ3]
    _ = 1 := by rw [Matrix.one_apply, if_pos rfl]

private lemma ggLieSU3Fixed_rho_eq_one {K : Type} [Field K] {H : Subgroup (GL (Fin 4) K)}
    (hH : ⁅H, H⁆ = H) {ρ : GL (Fin 4) K → K} (hρ1 : ρ 1 = 1)
    (hρmul : ∀ a b, a ∈ H → b ∈ H → ρ (a * b) = ρ a * ρ b)
    {x : GL (Fin 4) K} (hx : x ∈ ⁅H, H⁆) : ρ x = 1 := by
  letI : Bracket (GL (Fin 4) K) (GL (Fin 4) K) := commutatorElement
  have hcl : Subgroup.closure {g : GL (Fin 4) K | ∃ g₁ ∈ H, ∃ g₂ ∈ H, ⁅g₁, g₂⁆ = g} = H := by
    rw [show Subgroup.closure {g : GL (Fin 4) K | ∃ g₁ ∈ H, ∃ g₂ ∈ H, ⁅g₁, g₂⁆ = g} = ⁅H, H⁆ from
      (Subgroup.commutator_def H H).symm]
    exact hH
  have key : ∀ {y : GL (Fin 4) K},
      y ∈ Subgroup.closure {g : GL (Fin 4) K | ∃ g₁ ∈ H, ∃ g₂ ∈ H, ⁅g₁, g₂⁆ = g} → ρ y = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => ρ y = 1) ?gen ?one ?mul ?inv hy
    · intro a haS
      obtain ⟨p, hp, q, hq, hcomm⟩ := haS
      rw [← hcomm, commutatorElement_def]
      rw [show p * q * p⁻¹ * q⁻¹ = (p * q) * (p⁻¹ * q⁻¹) by noncomm_ring]
      have hp1 : ρ p * ρ p⁻¹ = 1 := by
        rw [← hρmul p p⁻¹ hp (H.inv_mem hp), mul_inv_cancel, hρ1]
      have hq1 : ρ q * ρ q⁻¹ = 1 := by
        rw [← hρmul q q⁻¹ hq (H.inv_mem hq), mul_inv_cancel, hρ1]
      calc ρ ((p * q) * (p⁻¹ * q⁻¹))
          = ρ (p * q) * ρ (p⁻¹ * q⁻¹) :=
              hρmul (p * q) (p⁻¹ * q⁻¹) (H.mul_mem hp hq)
                (H.mul_mem (H.inv_mem hp) (H.inv_mem hq))
        _ = (ρ p * ρ q) * (ρ p⁻¹ * ρ q⁻¹) := by
              rw [hρmul p q hp hq, hρmul p⁻¹ q⁻¹ (H.inv_mem hp) (H.inv_mem hq)]
        _ = (ρ p * ρ p⁻¹) * (ρ q * ρ q⁻¹) := by ring
        _ = 1 := by rw [hp1, hq1, one_mul]
    · exact hρ1
    · intro a b ha hb hpa hpb
      rw [hρmul a b (hcl ▸ ha) (hcl ▸ hb), hpa, hpb, one_mul]
    · intro a ha hpa
      have haH : a ∈ H := hcl ▸ ha
      have h1 : ρ a * ρ a⁻¹ = 1 := by
        rw [← hρmul a a⁻¹ haH (H.inv_mem haH), mul_inv_cancel, hρ1]
      simpa [hpa] using h1
  rw [Subgroup.commutator_def] at hx
  exact key hx

private lemma ggLieSU3Fixed_class_pow {K : Type} [Field K] [DecidableEq K] {z d : GL (Fin 4) K}
    (hzd : (z : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hdd : (d : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (H : Subgroup (GL (Fin 4) K)) (hH : ⁅H, H⁆ = H) (hzH : z ∈ H)
    (hHz : ∀ g ∈ H, g * z = z * g) (hHd : ∀ g ∈ H, g * d = d * g) (i0 : Fin 4) :
    (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ^
        (Finset.univ.filter (fun j => ((z : Matrix (Fin 4) (Fin 4) K) j j,
          (d : Matrix (Fin 4) (Fin 4) K) j j) =
          ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0))).card = 1 := by
  classical
  let U : Finset (Fin 4) := Finset.univ.filter (fun j =>
    ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j) =
      ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0))
  let e : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal (fun j => if j ∈ U then (1 : K) else 0)
  let ρ : GL (Fin 4) K → K := fun g =>
    Matrix.det ((g : Matrix (Fin 4) (Fin 4) K) * e + (1 - e))
  change (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ^ U.card = 1
  have hmemU : ∀ j : Fin 4, j ∈ U ↔
      ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j) =
        ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0) := by
    intro j
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hee : e * e = e := by
    rw [show e = Matrix.diagonal (fun j => if j ∈ U then (1 : K) else 0) from rfl]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hj : j ∈ U <;> simp [hj]
  have h1ee : e * (1 - e) = 0 := by rw [mul_sub, hee, mul_one, sub_self]
  have he1e : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have h1e1e : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have heH : ∀ g ∈ H, (g : Matrix (Fin 4) (Fin 4) K) * e =
      e * (g : Matrix (Fin 4) (Fin 4) K) := by
    intro g hg
    rw [show e = Matrix.diagonal (fun j => if j ∈ U then (1 : K) else 0) from rfl]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hiU : i ∈ U
    · by_cases hjU : j ∈ U
      · simp only [hiU, hjU, if_true]
        exact mul_comm _ _
      · have hp : ¬ (((z : Matrix (Fin 4) (Fin 4) K) i i, (d : Matrix (Fin 4) (Fin 4) K) i i) =
            ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j)) := by
          intro h
          exact hjU ((hmemU j).mpr (h.symm.trans ((hmemU i).mp hiU)))
        have hgij : (g : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
          by_contra hne
          exact hp (ggLieSU3Fixed_block hzd hdd H hHz hHd hg hne)
        simp [hiU, hjU, hgij]
    · by_cases hjU : j ∈ U
      · have hp : ¬ (((z : Matrix (Fin 4) (Fin 4) K) i i, (d : Matrix (Fin 4) (Fin 4) K) i i) =
            ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j)) := by
          intro h
          exact hiU ((hmemU i).mpr (h.trans ((hmemU j).mp hjU)))
        have hgij : (g : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
          by_contra hne
          exact hp (ggLieSU3Fixed_block hzd hdd H hHz hHd hg hne)
        simp [hiU, hjU, hgij]
      · simp [hiU, hjU]
  have hρ1 : ρ 1 = 1 := by
    change Matrix.det ((1 : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) = 1
    rw [one_mul]
    have h : e + (1 - e) = 1 := by abel
    rw [h, Matrix.det_one]
  have hρmul : ∀ a b, a ∈ H → b ∈ H → ρ (a * b) = ρ a * ρ b := by
    intro a b ha hb
    have heB : e * (b : Matrix (Fin 4) (Fin 4) K) =
        (b : Matrix (Fin 4) (Fin 4) K) * e := (heH b hb).symm
    have hAeBe : ((a : Matrix (Fin 4) (Fin 4) K) * e) *
        ((b : Matrix (Fin 4) (Fin 4) K) * e) =
        (a : Matrix (Fin 4) (Fin 4) K) * (b : Matrix (Fin 4) (Fin 4) K) * e := by
      calc ((a : Matrix (Fin 4) (Fin 4) K) * e) * ((b : Matrix (Fin 4) (Fin 4) K) * e)
          = (a : Matrix (Fin 4) (Fin 4) K) *
              (e * ((b : Matrix (Fin 4) (Fin 4) K) * e)) := by noncomm_ring
        _ = (a : Matrix (Fin 4) (Fin 4) K) *
              ((e * (b : Matrix (Fin 4) (Fin 4) K)) * e) := by noncomm_ring
        _ = (a : Matrix (Fin 4) (Fin 4) K) *
              (((b : Matrix (Fin 4) (Fin 4) K) * e) * e) := by rw [heB]
        _ = (a : Matrix (Fin 4) (Fin 4) K) *
              ((b : Matrix (Fin 4) (Fin 4) K) * (e * e)) := by noncomm_ring
        _ = (a : Matrix (Fin 4) (Fin 4) K) * ((b : Matrix (Fin 4) (Fin 4) K) * e) := by rw [hee]
        _ = (a : Matrix (Fin 4) (Fin 4) K) * (b : Matrix (Fin 4) (Fin 4) K) * e := by noncomm_ring
    have hAeF : ((a : Matrix (Fin 4) (Fin 4) K) * e) * (1 - e) = 0 := by
      rw [mul_assoc, h1ee, mul_zero]
    have hFB : (1 - e) * (b : Matrix (Fin 4) (Fin 4) K) =
        (b : Matrix (Fin 4) (Fin 4) K) * (1 - e) := by
      rw [sub_mul, one_mul, heB, mul_sub, mul_one]
    have hFBe : (1 - e) * ((b : Matrix (Fin 4) (Fin 4) K) * e) = 0 := by
      rw [← mul_assoc, hFB, mul_assoc, he1e, mul_zero]
    have hprod_eq : ((a : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) *
        ((b : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) =
        (a : Matrix (Fin 4) (Fin 4) K) * (b : Matrix (Fin 4) (Fin 4) K) * e + (1 - e) := by
      calc ((a : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) *
            ((b : Matrix (Fin 4) (Fin 4) K) * e + (1 - e))
          = ((a : Matrix (Fin 4) (Fin 4) K) * e) * ((b : Matrix (Fin 4) (Fin 4) K) * e) +
              ((a : Matrix (Fin 4) (Fin 4) K) * e) * (1 - e) +
              ((1 - e) * ((b : Matrix (Fin 4) (Fin 4) K) * e) + (1 - e) * (1 - e)) := by
                noncomm_ring
        _ = (a : Matrix (Fin 4) (Fin 4) K) * (b : Matrix (Fin 4) (Fin 4) K) * e +
              0 + (0 + (1 - e)) := by rw [hAeBe, hAeF, hFBe, h1e1e]
        _ = (a : Matrix (Fin 4) (Fin 4) K) * (b : Matrix (Fin 4) (Fin 4) K) * e + (1 - e) := by
              abel
    change Matrix.det ((((a * b : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) =
      Matrix.det ((a : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) *
        Matrix.det ((b : Matrix (Fin 4) (Fin 4) K) * e + (1 - e))
    rw [GeneralLinearGroup.coe_mul, ← Matrix.det_mul, hprod_eq]
  have hmat : (z : Matrix (Fin 4) (Fin 4) K) * e + (1 - e) =
      Matrix.diagonal (fun i => if i ∈ U then (z : Matrix (Fin 4) (Fin 4) K) i i else 1) := by
    rw [show e = Matrix.diagonal (fun j => if j ∈ U then (1 : K) else 0) from rfl]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.one_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hiU : i ∈ U <;> simp [hiU]
    · have hzij : (z : Matrix (Fin 4) (Fin 4) K) i j = 0 := hzd hij
      simp [hij, hzij]
  have hdet : ρ z = (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ^ U.card := by
    change Matrix.det ((z : Matrix (Fin 4) (Fin 4) K) * e + (1 - e)) =
      (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ^ U.card
    rw [hmat, Matrix.det_diagonal]
    rw [Finset.prod_ite_mem Finset.univ U (fun i => (z : Matrix (Fin 4) (Fin 4) K) i i)]
    rw [Finset.univ_inter]
    rw [Finset.prod_eq_pow_card (fun a ha => congrArg Prod.fst ((hmemU a).mp ha))]
  have hρz : ρ z = 1 :=
    ggLieSU3Fixed_rho_eq_one hH hρ1 hρmul (by rw [hH]; exact hzH)
  rw [← hdet, hρz]

private lemma ggLieSU3Fixed_class_card {K : Type} [Field K] [DecidableEq K] {z d : GL (Fin 4) K}
    (hzd : (z : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hdd : (d : Matrix (Fin 4) (Fin 4) K).IsDiag) (hz3 : z ^ 3 = 1)
    (H : Subgroup (GL (Fin 4) K)) (hH : ⁅H, H⁆ = H) (hzH : z ∈ H)
    (hHz : ∀ g ∈ H, g * z = z * g) (hHd : ∀ g ∈ H, g * d = d * g)
    (i0 : Fin 4) (hi0 : (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ≠ 1) :
    (Finset.univ.filter (fun j => ((z : Matrix (Fin 4) (Fin 4) K) j j,
      (d : Matrix (Fin 4) (Fin 4) K) j j) =
      ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0))).card = 3 := by
  classical
  let U : Finset (Fin 4) := Finset.univ.filter (fun j =>
    ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j) =
      ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0))
  change U.card = 3
  have hpow : (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ^ U.card = 1 :=
    ggLieSU3Fixed_class_pow hzd hdd H hH hzH hHz hHd i0
  have h3 : (z : Matrix (Fin 4) (Fin 4) K) i0 i0 ^ 3 = 1 :=
    ggLieSU3Fixed_diag_cube hzd hz3 i0
  have hord : orderOf ((z : Matrix (Fin 4) (Fin 4) K) i0 i0) = 3 :=
    orderOf_eq_prime h3 hi0
  have hdvd : 3 ∣ U.card := by
    have h := orderOf_dvd_of_pow_eq_one hpow
    rwa [hord] at h
  have hcard_le : U.card ≤ 4 := by
    have h := Finset.card_le_univ U
    rwa [Fintype.card_fin] at h
  have hcard_pos : 0 < U.card := by
    rw [Finset.card_pos]
    exact ⟨i0, by simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hle : 3 ≤ U.card := Nat.le_of_dvd hcard_pos hdvd
  have hc : U.card = 3 ∨ U.card = 4 := by omega
  rcases hc with hc | hc
  · exact hc
  · rw [hc] at hdvd; norm_num at hdvd

theorem ggLieSU3Fixed_diag_pattern {K : Type} [Field K] {z d : GL (Fin 4) K}
    (hzd : (z : Matrix (Fin 4) (Fin 4) K).IsDiag) (hdd : (d : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hz3 : z ^ 3 = 1) (H : Subgroup (GL (Fin 4) K)) (hH : ⁅H, H⁆ = H) (hzH : z ∈ H)
    (hHz : ∀ g ∈ H, g * z = z * g) (hHd : ∀ g ∈ H, g * d = d * g) :
    z = 1 ∨ ∃ (k : Fin 4) (β α : K), β ≠ 1 ∧ (z : Matrix (Fin 4) (Fin 4) K) k k = 1 ∧
      ∀ i, i ≠ k → (z : Matrix (Fin 4) (Fin 4) K) i i = β ∧
        (d : Matrix (Fin 4) (Fin 4) K) i i = α := by
  classical
  by_cases hall : ∀ i, (z : Matrix (Fin 4) (Fin 4) K) i i = 1
  · left
    apply Units.ext
    change (z : Matrix (Fin 4) (Fin 4) K) = (1 : Matrix (Fin 4) (Fin 4) K)
    rw [show (z : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal (fun i => (z : Matrix (Fin 4) (Fin 4) K) i i) from
      ((Matrix.isDiag_iff_diagonal_diag _).mp hzd).symm]
    simp only [hall, Matrix.diagonal_one]
  · right
    push Not at hall
    obtain ⟨i0, hi0⟩ := hall
    let U : Finset (Fin 4) := Finset.univ.filter (fun j =>
      ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j) =
        ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0))
    have hU : U.card = 3 :=
      ggLieSU3Fixed_class_card hzd hdd hz3 H hH hzH hHz hHd i0 hi0
    let C : Finset (Fin 4) := Finset.univ \ U
    have hCcard : C.card = 1 := by
      change (Finset.univ \ U).card = 1
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hU]
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hCcard
    have hknotU : k ∉ U := by
      intro hkU
      have hkmem : k ∈ C := by rw [hk]; simp
      have hknot : k ∉ C := by
        intro hkC
        rw [Finset.mem_sdiff] at hkC
        exact hkC.2 hkU
      exact hknot hkmem
    refine ⟨k, (z : Matrix (Fin 4) (Fin 4) K) i0 i0,
      (d : Matrix (Fin 4) (Fin 4) K) i0 i0, hi0, ?_, ?_⟩
    · by_contra hk1
      let W : Finset (Fin 4) := Finset.univ.filter (fun j =>
        ((z : Matrix (Fin 4) (Fin 4) K) j j, (d : Matrix (Fin 4) (Fin 4) K) j j) =
          ((z : Matrix (Fin 4) (Fin 4) K) k k, (d : Matrix (Fin 4) (Fin 4) K) k k))
      have hW : W.card = 3 :=
        ggLieSU3Fixed_class_card hzd hdd hz3 H hH hzH hHz hHd k hk1
      have hdisj : Disjoint U W := by
        rw [Finset.disjoint_left]
        intro a haU haW
        have hpairU : ((z : Matrix (Fin 4) (Fin 4) K) a a,
            (d : Matrix (Fin 4) (Fin 4) K) a a) =
            ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0) := by
          simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using haU
        have hpairW : ((z : Matrix (Fin 4) (Fin 4) K) a a,
            (d : Matrix (Fin 4) (Fin 4) K) a a) =
            ((z : Matrix (Fin 4) (Fin 4) K) k k, (d : Matrix (Fin 4) (Fin 4) K) k k) := by
          simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and] using haW
        have hkU : ((z : Matrix (Fin 4) (Fin 4) K) k k, (d : Matrix (Fin 4) (Fin 4) K) k k) =
            ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0) :=
          hpairW.symm.trans hpairU
        exact hknotU (by
          simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hkU)
      have hbig : (U ∪ W).card = 6 := by
        rw [Finset.card_union_of_disjoint hdisj, hU, hW]
      have hle : (U ∪ W).card ≤ 4 := by
        have h := Finset.card_le_univ (U ∪ W)
        rwa [Fintype.card_fin] at h
      omega
    · intro i hi
      have hiU : i ∈ U := by
        by_contra hni
        have hiC : i ∈ C := by
          rw [Finset.mem_sdiff]
          exact ⟨Finset.mem_univ i, hni⟩
        rw [hk] at hiC
        simp only [Finset.mem_singleton] at hiC
        exact hi hiC
      have hpair : ((z : Matrix (Fin 4) (Fin 4) K) i i, (d : Matrix (Fin 4) (Fin 4) K) i i) =
          ((z : Matrix (Fin 4) (Fin 4) K) i0 i0, (d : Matrix (Fin 4) (Fin 4) K) i0 i0) := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hiU
      exact Prod.ext_iff.mp hpair

end CFSG.StandardType
