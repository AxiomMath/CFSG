module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.Quasithin.F7Two

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem symm_of_graph_lift (h2 : (2 : K) ≠ 0) (A B : Matrix (Fin 3) (Fin 3) K)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (α : SpecialLinearGroup (Fin 3) K → SpecialLinearGroup (Fin 3) K)
    (hαm : ∀ x, ((α x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      A * (((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ * B)
    (hαα : ∀ x, α (α x) = x) : Aᵀ = A := by
  have hxinv : ∀ x : SpecialLinearGroup (Fin 3) K,
      (x : Matrix (Fin 3) (Fin 3) K) * ((x⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := fun x =>
    congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      (mul_inv_cancel x)
  have hinvx : ∀ x : SpecialLinearGroup (Fin 3) K,
      ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (x : Matrix (Fin 3) (Fin 3) K) = 1 := fun x =>
    congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      (inv_mul_cancel x)
  have e1 : ∀ x : SpecialLinearGroup (Fin 3) K,
      ((((α x)⁻¹ : SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        A * (x : Matrix (Fin 3) (Fin 3) K)ᵀ * B := by
    intro x
    have h1 : ((α x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (A * (x : Matrix (Fin 3) (Fin 3) K)ᵀ * B) = 1 := by
      rw [hαm]
      calc A * (((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ * B *
          (A * (x : Matrix (Fin 3) (Fin 3) K)ᵀ * B)
          = A * (((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ * (B * A) *
            (x : Matrix (Fin 3) (Fin 3) K)ᵀ * B := by simp only [Matrix.mul_assoc]
        _ = A * ((x : Matrix (Fin 3) (Fin 3) K) *
            ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ * B := by
          rw [hBA, Matrix.mul_one, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hxinv, Matrix.transpose_one, Matrix.mul_one, hAB]
    calc ((((α x)⁻¹ : SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
        = ((((α x)⁻¹ : SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
          (((α x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (A * (x : Matrix (Fin 3) (Fin 3) K)ᵀ * B)) := by rw [h1, Matrix.mul_one]
      _ = A * (x : Matrix (Fin 3) (Fin 3) K)ᵀ * B := by
        rw [← Matrix.mul_assoc, hinvx (α x), Matrix.one_mul]
  have e2 : ∀ x : SpecialLinearGroup (Fin 3) K,
      A * Bᵀ * (x : Matrix (Fin 3) (Fin 3) K) * (Aᵀ * B) = x := by
    intro x
    have h : ((α (α x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (x : Matrix (Fin 3) (Fin 3) K) := congrArg
      (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) (hαα x)
    rw [hαm, e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h
    calc A * Bᵀ * (x : Matrix (Fin 3) (Fin 3) K) * (Aᵀ * B)
        = A * (Bᵀ * ((x : Matrix (Fin 3) (Fin 3) K) * Aᵀ)) * B := by simp only [Matrix.mul_assoc]
      _ = x := h
  have hCinv' : (Aᵀ * B) * (A * Bᵀ) = 1 := by
    calc Aᵀ * B * (A * Bᵀ) = Aᵀ * (B * A) * Bᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.mul_one, ← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  have hcomm : ∀ x : SpecialLinearGroup (Fin 3) K, (A * Bᵀ) * (x : Matrix (Fin 3) (Fin 3) K) =
      (x : Matrix (Fin 3) (Fin 3) K) * (A * Bᵀ) := by
    intro x
    calc (A * Bᵀ) * (x : Matrix (Fin 3) (Fin 3) K)
        = (A * Bᵀ) * (x : Matrix (Fin 3) (Fin 3) K) * ((Aᵀ * B) * (A * Bᵀ)) := by
          rw [hCinv', Matrix.mul_one]
      _ = ((A * Bᵀ) * (x : Matrix (Fin 3) (Fin 3) K) * (Aᵀ * B)) * (A * Bᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 3) (Fin 3) K) * (A * Bᵀ) := by rw [e2]
  obtain ⟨c, hc⟩ : A * Bᵀ ∈ Set.range (Matrix.scalar (Fin 3) (α := K)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    exact (hcomm ⟨t.toMatrix, t.det⟩).symm
  have hc' : A * Bᵀ = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hA1 : A = c • Aᵀ := by
    calc A = A * (Bᵀ * Aᵀ) := by
          rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one, Matrix.mul_one]
      _ = (A * Bᵀ) * Aᵀ := by rw [Matrix.mul_assoc]
      _ = c • Aᵀ := by rw [hc', Matrix.smul_mul, Matrix.one_mul]
  have hA2 : Aᵀ = c • A := by
    have h := congrArg Matrix.transpose hA1
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at h
  have hdetA : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have hcc : c * c = 1 := by
    have hA0 : ∃ i j, A i j ≠ 0 := by
      by_contra h
      push Not at h
      apply hdetA
      have : A = 0 := Matrix.ext h
      rw [this]
      simp
    obtain ⟨i, j, hij⟩ := hA0
    have h3 : A i j = (c * c) * A i j := by
      have h4 : A = (c * c) • A := by rw [mul_smul, ← hA2, ← hA1]
      calc A i j = ((c * c) • A) i j := by rw [← h4]
        _ = (c * c) * A i j := by simp
    have h5 : (c * c - 1) * A i j = 0 := by linear_combination -h3
    have := (mul_eq_zero.mp h5).resolve_right hij
    linear_combination this
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · rw [h1, one_smul] at hA2
    exact hA2
  · exfalso
    have h6 : A.det = -A.det := by
      have h7 := congrArg Matrix.det hA2
      rw [Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, h1] at h7
      linear_combination h7
    apply hdetA
    have h8 : (2 : K) * A.det = 0 := by linear_combination h6
    exact (mul_eq_zero.mp h8).resolve_left h2

@[expose] def AntiSupp (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  M 0 0 = 0 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 0

theorem mul_mul_transpose_apply (M A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (M * A * Mᵀ) i j = M i ⬝ᵥ (A *ᵥ M j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem exists_sl_antidiag_of_isotropic (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 3) (Fin 3) K)
    (hsymm : Aᵀ = A) (hdet : A.det ≠ 0)
    (hiso : ∃ v : Fin 3 → K, v ≠ 0 ∧ v ⬝ᵥ (A *ᵥ v) = 0) :
    ∃ Q : SpecialLinearGroup (Fin 3) K,
      AntiSupp ((Q : Matrix (Fin 3) (Fin 3) K) * A * (Q : Matrix (Fin 3) (Fin 3) K)ᵀ) := by
  set β : (Fin 3 → K) → (Fin 3 → K) → K := fun u w => u ⬝ᵥ (A *ᵥ w) with hβ
  have hsym : ∀ u w, β u w = β w u := by
    intro u w
    simp only [hβ]
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  obtain ⟨v, hv0, hvv⟩ := hiso
  have hAv : A *ᵥ v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
  obtain ⟨k, hk⟩ : ∃ k, (A *ᵥ v) k ≠ 0 := by
    by_contra h
    push Not at h
    exact hAv (funext h)
  set x : K := (A *ᵥ v) k with hx
  set y : Fin 3 → K := Pi.single k 1 with hy
  have hβyv : β y v = x := by simp [hβ, hy, single_dotProduct, hx]
  have hβvy : β v y = x := by rw [hsym]; exact hβyv
  set t : K := β y y / (2 * x) with ht
  set w : Fin 3 → K := y - t • v with hw
  have hβvw : β v w = x := by
    have : β v w = β v y - t * β v v := by
      simp [hβ, hw, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]
    rw [this, hβvy]
    have : β v v = 0 := hvv
    rw [this, mul_zero, sub_zero]
  have hβwv : β w v = x := by rw [hsym]; exact hβvw
  have hβww : β w w = 0 := by
    have : β w w = β y y - 2 * t * β v y + t * t * β v v := by
      simp only [hβ, hw, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      have := hsym v y
      simp only [hβ] at this
      rw [this]
      ring
    rw [this, hβvy]
    have : β v v = 0 := hvv
    rw [this, ht]
    field_simp
    ring
  have hx0 : x ≠ 0 := hk
  set u : Fin 3 → K := crossProduct (A *ᵥ v) (A *ᵥ w) with hu
  have hβuv : β u v = 0 := by
    simp only [hβ, hu]
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  have hβuw : β u w = 0 := by
    simp only [hβ, hu]
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  have hβvu : β v u = 0 := by rw [hsym]; exact hβuv
  have hβwu : β w u = 0 := by rw [hsym]; exact hβuw
  have hdetQ : (Matrix.of ![v, u, w]).det = x * x := by
    have h1 : (Matrix.of ![v, u, w]).det = v ⬝ᵥ (crossProduct u) w :=
      (triple_product_eq_det v u w).symm
    rw [h1, hu, cross_cross_eq_smul_sub_smul]
    have e1 : (A *ᵥ v) ⬝ᵥ w = x := by rw [dotProduct_comm]; exact hβwv
    have e2 : (A *ᵥ w) ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hβww
    rw [e1, e2, zero_smul, sub_zero, dotProduct_smul, smul_eq_mul]
    have : v ⬝ᵥ (A *ᵥ w) = x := hβvw
    rw [this]
  set u' : Fin 3 → K := (x * x)⁻¹ • u with hu'
  have hx2 : x * x ≠ 0 := mul_ne_zero hx0 hx0
  have hdetQ' : (Matrix.of ![v, u', w]).det = 1 := by
    have h1 : (Matrix.of ![v, u', w]).det = v ⬝ᵥ (crossProduct u') w :=
      (triple_product_eq_det v u' w).symm
    have h2' : v ⬝ᵥ (crossProduct u) w = x * x := by
      rw [triple_product_eq_det]
      exact hdetQ
    rw [h1, hu', map_smul, LinearMap.smul_apply, dotProduct_smul, smul_eq_mul, h2']
    field_simp
  refine ⟨⟨Matrix.of ![v, u', w], hdetQ'⟩, ?_⟩
  show AntiSupp (Matrix.of ![v, u', w] * A * (Matrix.of ![v, u', w])ᵀ)
  have p1 : v ⬝ᵥ (A *ᵥ v) = 0 := hvv
  have p2 : v ⬝ᵥ (A *ᵥ u') = 0 := by
    rw [hu', Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    have : v ⬝ᵥ (A *ᵥ u) = 0 := hβvu
    rw [this, mul_zero]
  have p3 : u' ⬝ᵥ (A *ᵥ v) = 0 := by
    rw [hu', smul_dotProduct, smul_eq_mul]
    have : u ⬝ᵥ (A *ᵥ v) = 0 := hβuv
    rw [this, mul_zero]
  have p4 : u' ⬝ᵥ (A *ᵥ w) = 0 := by
    rw [hu', smul_dotProduct, smul_eq_mul]
    have : u ⬝ᵥ (A *ᵥ w) = 0 := hβuw
    rw [this, mul_zero]
  have p5 : w ⬝ᵥ (A *ᵥ u') = 0 := by
    rw [hu', Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    have : w ⬝ᵥ (A *ᵥ u) = 0 := hβwu
    rw [this, mul_zero]
  have p6 : w ⬝ᵥ (A *ᵥ w) = 0 := hβww
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mul_mul_transpose_apply] <;> simpa [Matrix.of_apply]

theorem exists_isotropic_zmod {p : ℕ} [Fact p.Prime] (A : Matrix (Fin 3) (Fin 3) (ZMod p)) :
    ∃ v : Fin 3 → ZMod p, v ≠ 0 ∧ v ⬝ᵥ (A *ᵥ v) = 0 := by
  classical
  set f : MvPolynomial (Fin 3) (ZMod p) :=
    ∑ i, ∑ j, MvPolynomial.C (A i j) * (MvPolynomial.X i * MvPolynomial.X j) with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    have h2 : f.totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 : (MvPolynomial.X i : MvPolynomial (Fin 3) (ZMod p)).totalDegree = 1 :=
        MvPolynomial.totalDegree_X i
      have h1' : (MvPolynomial.X j : MvPolynomial (Fin 3) (ZMod p)).totalDegree = 1 :=
        MvPolynomial.totalDegree_X j
      omega
    omega
  have hdvd := char_dvd_card_solutions p hdeg
  have hev : ∀ x : Fin 3 → ZMod p, MvPolynomial.eval x f = x ⬝ᵥ (A *ᵥ x) := by
    intro x
    simp only [hf, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct,
      Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  by_contra hcon
  push Not at hcon
  have hone : Fintype.card {x : Fin 3 → ZMod p // MvPolynomial.eval x f = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by rw [hev]; simp⟩, fun y => ?_⟩
    by_contra hy
    have hy0 : y.1 ≠ 0 := fun h => hy (Subtype.ext h)
    exact hcon y.1 hy0 (by rw [← hev]; exact y.2)
  rw [hone] at hdvd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hdvd)

end CFSG.Quasithin.F7Two
