module

public import CFSG.Quasithin.Background.F7TwoInvL3Unip
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem diagonal_conj_mem_unitriangular {d e : Fin 3 → K} (hde : ∀ i, d i * e i = 1)
    {u v : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (hv : (v : Matrix (Fin 3) (Fin 3) K) = diagonal d * (u : Matrix (Fin 3) (Fin 3) K) *
      diagonal e) : v ∈ unitriangular 3 K := by
  rw [mem_unitriangular] at hu ⊢
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [hv, Matrix.mul_diagonal, Matrix.diagonal_mul, hu.1 i j hji]
    ring
  · rw [hv, Matrix.mul_diagonal, Matrix.diagonal_mul, hu.2 i, mul_one, hde]

theorem diagonal_conj_mem_lowerUnitriangular {d e : Fin 3 → K} (hde : ∀ i, d i * e i = 1)
    {u v : SpecialLinearGroup (Fin 3) K} (hu : u ∈ lowerUnitriangular 3 K)
    (hv : (v : Matrix (Fin 3) (Fin 3) K) = diagonal d * (u : Matrix (Fin 3) (Fin 3) K) *
      diagonal e) : v ∈ lowerUnitriangular 3 K := by
  rw [mem_lowerUnitriangular] at hu ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hv, Matrix.mul_diagonal, Matrix.diagonal_mul, hu.1 i j hij]
    ring
  · rw [hv, Matrix.mul_diagonal, Matrix.diagonal_mul, hu.2 i, mul_one, hde]

theorem sq_scalar_of_inner_lift (A B : Matrix (Fin 3) (Fin 3) K) (hAB : A * B = 1)
    (hBA : B * A = 1)
    (h : ∀ x : SpecialLinearGroup (Fin 3) K,
      A * (A * (x : Matrix (Fin 3) (Fin 3) K) * B) * B = x) :
    ∃ c : K, A * A = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hAABB : A * A * (B * B) = 1 := by
    calc A * A * (B * B) = A * (A * B) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, hAB]
  have hBBAA : B * B * (A * A) = 1 := by
    calc B * B * (A * A) = B * (B * A) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.mul_one, hBA]
  have hcomm : ∀ x : SpecialLinearGroup (Fin 3) K,
      (A * A) * (x : Matrix (Fin 3) (Fin 3) K) = (x : Matrix (Fin 3) (Fin 3) K) * (A * A) := by
    intro x
    have e1 : A * A * (x : Matrix (Fin 3) (Fin 3) K) * (B * B) = x := by
      calc A * A * (x : Matrix (Fin 3) (Fin 3) K) * (B * B)
          = A * (A * (x : Matrix (Fin 3) (Fin 3) K) * B) * B := by simp only [Matrix.mul_assoc]
        _ = x := h x
    calc (A * A) * (x : Matrix (Fin 3) (Fin 3) K)
        = (A * A) * (x : Matrix (Fin 3) (Fin 3) K) * (B * B * (A * A)) := by
          rw [hBBAA, Matrix.mul_one]
      _ = (A * A * (x : Matrix (Fin 3) (Fin 3) K) * (B * B)) * (A * A) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 3) (Fin 3) K) * (A * A) := by rw [e1]
  obtain ⟨c, hc⟩ : A * A ∈ Set.range (Matrix.scalar (Fin 3) (α := K)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    exact (hcomm ⟨t.toMatrix, t.det⟩).symm
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]⟩

theorem exists_sl_diag_of_sq_scalar (h2 : (2 : K) ≠ 0) (A B : Matrix (Fin 3) (Fin 3) K)
    (hAB : A * B = 1) {c : K}
    (hc : A * A = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (P : SpecialLinearGroup (Fin 3) K) (d : Fin 3 → K), (∀ i, d i ≠ 0) ∧
      ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (P : Matrix _ _ K) =
        diagonal d ∧
      ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B * (P : Matrix _ _ K) =
        diagonal (fun i => (d i)⁻¹) := by
  have hdetA : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have hc0 : c ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, h0] at h
    exact hdetA (mul_self_eq_zero.mp (by simpa using h))
  set μ : K := A.det / c with hμ
  have hμ2 : μ * μ = c := by
    have h := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h
    rw [hμ]
    field_simp
    linear_combination h
  have hμ0 : μ ≠ 0 := fun h0 => hc0 (by rw [← hμ2, h0, zero_mul])
  set D : Matrix (Fin 3) (Fin 3) K := μ⁻¹ • A with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, smul_smul]
    have : μ⁻¹ * μ⁻¹ * c = 1 := by
      rw [← hμ2]
      field_simp
    rw [this, one_smul]
  obtain ⟨a, -, P, hP⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_sl_conj_diagonal h2
    (by norm_num : 0 < 3) hDD
  set ε : Fin 3 → K := fun j => if j.val < a then (-1 : K) else 1 with hε
  have hε0 : ∀ j, ε j ≠ 0 := fun j => by
    simp only [hε]
    split_ifs <;> simp
  have hPinv : ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
    exact congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      (inv_mul_cancel P)
  have hAd : A = μ • D := by
    rw [hD, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hconjA : ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
      (P : Matrix _ _ K) = diagonal (fun j => μ * ε j) := by
    rw [hAd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hPinv,
      Matrix.one_mul]
    ext i j
    simp [Matrix.diagonal_apply]
  refine ⟨P, fun j => μ * ε j, fun j => mul_ne_zero hμ0 (hε0 j), hconjA, ?_⟩
  have hBd : ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B *
      (P : Matrix _ _ K) = diagonal (fun j => (μ * ε j)⁻¹) := by
    have hPP : (P : Matrix (Fin 3) (Fin 3) K) *
        ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      exact congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
        (mul_inv_cancel P)
    have h1 : diagonal (fun j => μ * ε j) *
        (((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B *
          (P : Matrix _ _ K)) = 1 := by
      rw [← hconjA]
      calc ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
            (P : Matrix _ _ K) *
          (((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B *
            (P : Matrix _ _ K))
          = ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (A * ((P : Matrix _ _ K) *
              ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * B) *
            (P : Matrix _ _ K) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hPP, Matrix.mul_one, hAB, Matrix.mul_one, hPinv]
    ext i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.diagonal_mul] at this
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, ite_true] at this ⊢
      exact eq_inv_of_mul_eq_one_right this
    · simp only [Matrix.one_apply_ne hij, hij, ite_false] at this ⊢
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hμ0 (hε0 i))
  exact hBd

theorem invAutGen_of_inner_lift [Finite K] (h2 : (2 : K) ≠ 0) (hodd : Odd (Nat.card K))
    {X : Type*} [Group X] [Finite X] (hs : IsSimpleGroup X) (hnonab : ∃ x y : X, x * y ≠ y * x)
    (θ : SpecialLinearGroup (Fin 3) K →* X) (hθ : Function.Surjective θ) {φ : MulAut X}
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (α : SpecialLinearGroup (Fin 3) K → SpecialLinearGroup (Fin 3) K)
    (hα : ∀ x, φ (θ x) = θ (α x)) (A B : Matrix (Fin 3) (Fin 3) K) (hAB : A * B = 1)
    (hαm : ∀ x, ((α x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      A * (x : Matrix (Fin 3) (Fin 3) K) * B)
    (hsq : ∃ c : K, A * A = c • (1 : Matrix (Fin 3) (Fin 3) K)) : InvAutGen X φ := by
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨P, d, hd0, hPA, hPB⟩ := exists_sl_diag_of_sq_scalar h2 A B hAB hc
  set ψ : MulAut X := MulAut.conj (θ P⁻¹) with hψ
  have hφ'2 : (ψ * φ * ψ⁻¹) * (ψ * φ * ψ⁻¹) = 1 := by
    calc (ψ * φ * ψ⁻¹) * (ψ * φ * ψ⁻¹) = ψ * (φ * φ) * ψ⁻¹ := by group
      _ = 1 := by rw [hφ2]; group
  have hφ'1 : ψ * φ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hφ1
    calc φ = ψ⁻¹ * (ψ * φ * ψ⁻¹) * ψ := by group
      _ = 1 := by rw [h]; group
  refine (InvAutGen.conj_iff ψ φ).mpr ?_
  have hθP : (θ P⁻¹)⁻¹ = θ P := by rw [← map_inv, inv_inv]
  have hψ1 : ∀ y : SpecialLinearGroup (Fin 3) K, ψ (θ y) = θ (P⁻¹ * y * P) := by
    intro y
    rw [hψ, MulAut.conj_apply, hθP, map_mul, map_mul]
  have hψ2 : ∀ y : SpecialLinearGroup (Fin 3) K, ψ⁻¹ (θ y) = θ (P * y * P⁻¹) := by
    intro y
    have h : ψ⁻¹ = ψ.symm := rfl
    rw [h, hψ, MulAut.conj_symm_apply, hθP, map_mul, map_mul]
  have hv : ∀ u : SpecialLinearGroup (Fin 3) K,
      ((P⁻¹ * α (P * u * P⁻¹) * P : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal d * (u : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => (d i)⁻¹) := by
    intro u
    rw [← hPA, ← hPB]
    show ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((α (P * u * P⁻¹) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (P : Matrix (Fin 3) (Fin 3) K) = _
    rw [hαm]
    show _ * (A * ((P : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) *
      ((P⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * B) * _ = _
    simp only [Matrix.mul_assoc]
  have hde : ∀ i, d i * (d i)⁻¹ = 1 := fun i => mul_inv_cancel₀ (hd0 i)
  refine invAutGen_of_unitriangular_invariant hodd hs hnonab θ hθ hφ'2 hφ'1
    (fun x => P⁻¹ * α (P * x * P⁻¹) * P) (fun x => ?_)
    (fun u hu => diagonal_conj_mem_unitriangular hde hu (hv u))
    (fun u hu => diagonal_conj_mem_lowerUnitriangular hde hu (hv u))
  rw [MulAut.mul_apply, MulAut.mul_apply, hψ2, hα, hψ1]

end CFSG.Quasithin.F7Two
