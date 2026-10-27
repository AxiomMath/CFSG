module

public import CFSG.Quasithin.H13.L32AL2t

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

@[expose] def utS (p : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, p; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_utS (p : F) : ((utS p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, p; 0, 1] := rfl

theorem utS_mul (p q : F) : utS p * utS q = utS (p + q) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [utS, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem utS_zero : utS (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utS]

theorem utS_inv (p : F) : (utS p)⁻¹ = utS (-p) := by
  rw [inv_eq_iff_mul_eq_one, utS_mul, add_neg_cancel, utS_zero]

theorem utS_injective : Function.Injective (utS (F := F)) := by
  intro p q h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [utS] using this

@[expose] def sZero : Subgroup (MulAut (VM F)) where
  carrier := {x | ∃ p q : F, x = rho (utS p, utS q)}
  mul_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨p', q', rfl⟩
    exact ⟨p + p', q + q', by rw [← map_mul, Prod.mk_mul_mk, utS_mul, utS_mul]⟩
  one_mem' := ⟨0, 0, by rw [utS_zero, ← Prod.one_eq_mk, map_one]⟩
  inv_mem' := by
    rintro _ ⟨p, q, rfl⟩
    exact ⟨-p, -q, by rw [← map_inv, Prod.inv_mk, utS_inv, utS_inv]⟩

theorem sZero_le_range : sZero ≤ (rho (K := F)).range := by
  rintro _ ⟨p, q, rfl⟩
  exact ⟨_, rfl⟩

theorem card_sZero [Finite F] [CharP F 2] : Nat.card (sZero (F := F)) = Nat.card F ^ 2 := by
  have hbij : Function.Bijective (fun pq : F × F =>
      (⟨rho (utS pq.1, utS pq.2), pq.1, pq.2, rfl⟩ : sZero (F := F))) := by
    constructor
    · intro a b h
      have h1 := rho_injective (congrArg Subtype.val h)
      exact Prod.ext (utS_injective (congrArg Prod.fst h1)) (utS_injective (congrArg Prod.snd h1))
    · rintro ⟨_, p, q, rfl⟩
      exact ⟨(p, q), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, pow_two]

@[expose] def matE : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, 0]

theorem eq_smul_e11_of_fix {p q : F} (hp : p ≠ 0) (hq : q ≠ 0) {X : Matrix (Fin 2) (Fin 2) F}
    (h1 : rho (utS p, (1 : SpecialLinearGroup (Fin 2) F)) (Multiplicative.ofAdd X) =
      Multiplicative.ofAdd X)
    (h2 : rho ((1 : SpecialLinearGroup (Fin 2) F), utS q) (Multiplicative.ofAdd X) =
      Multiplicative.ofAdd X) :
    X = X 0 0 • matE := by
  have e1 := congrArg Multiplicative.toAdd h1
  have e2 := congrArg Multiplicative.toAdd h2
  rw [rho_apply, toAdd_lr, toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_utS, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one, Matrix.mul_one] at e1
  rw [rho_apply, toAdd_lr, toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_utS, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mul] at e2
  have x10 : X 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hp] using congrFun (congrFun e1 0) 0
  have x11 : X 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hp] using congrFun (congrFun e1 0) 1
  have x01 : X 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hq] using congrFun (congrFun e2 0) 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matE, x10, x11, x01]

theorem mul_matJ_mul_transpose [CharP F 2] (g : Matrix (Fin 2) (Fin 2) F) :
    g * matJ * gᵀ = g.det • matJ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  · linear_combination (g 0 0 * g 0 1) * h2
  · ring_nf
    linear_combination (g 0 1 * g 1 0) * h2
  · ring_nf
    linear_combination (g 0 1 * g 1 0) * h2
  · linear_combination (g 1 0 * g 1 1) * h2

theorem matJ_mul_self : (matJ : Matrix (Fin 2) (Fin 2) F) * matJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_matJ_eq_iff [CharP F 2] {P H : Matrix (Fin 2) (Fin 2) F} (hP : P.det = 1) :
    P * matJ * Hᵀ = matJ ↔ H = P := by
  have hJ := mul_matJ_mul_transpose P
  rw [hP, one_smul] at hJ
  constructor
  · intro h
    have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (by rw [hP]; exact isUnit_one)
    have e : matJ * P⁻¹ * (P * matJ * Hᵀ) = matJ * P⁻¹ * (P * matJ * Pᵀ) := by rw [h, hJ]
    simp only [← Matrix.mul_assoc] at e
    rw [Matrix.mul_assoc matJ P⁻¹ P, hinv, Matrix.mul_one, matJ_mul_self, Matrix.one_mul,
      Matrix.one_mul] at e
    have := congrArg Matrix.transpose e
    rwa [Matrix.transpose_transpose, Matrix.transpose_transpose] at this
  · rintro rfl
    exact hJ

theorem fix_aJ_iff [CharP F 2] (A : GL (Fin 2) F) {c : F} (hc : c ≠ 0)
    (g h : SpecialLinearGroup (Fin 2) F) :
    rho (g, h) (Multiplicative.ofAdd (c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ))) =
        Multiplicative.ofAdd (c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ)) ↔
      (h : Matrix (Fin 2) (Fin 2) F) = ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) := by
  set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hM
  set N : Matrix (Fin 2) (Fin 2) F := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (N * (g : Matrix (Fin 2) (Fin 2) F) * M).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul, hNM, Matrix.det_one]
  rw [← mul_matJ_eq_iff hdet]
  constructor
  · intro e
    have e1 := congrArg Multiplicative.toAdd e
    rw [rho_apply, toAdd_lr, toAdd_ofAdd] at e1
    change (g : Matrix (Fin 2) (Fin 2) F) * (c • (M * matJ)) * (h : Matrix (Fin 2) (Fin 2) F)ᵀ =
      c • (M * matJ) at e1
    rw [Matrix.mul_smul, Matrix.smul_mul] at e1
    have e2 := smul_right_injective _ hc e1
    calc N * (g : Matrix (Fin 2) (Fin 2) F) * M * matJ * (h : Matrix (Fin 2) (Fin 2) F)ᵀ
        = N * ((g : Matrix (Fin 2) (Fin 2) F) * (M * matJ) * (h : Matrix (Fin 2) (Fin 2) F)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = matJ := by rw [e2, ← Matrix.mul_assoc, hNM, Matrix.one_mul]
  · intro e
    apply Multiplicative.toAdd.injective
    rw [rho_apply, toAdd_lr, toAdd_ofAdd]
    change (g : Matrix (Fin 2) (Fin 2) F) * (c • (M * matJ)) * (h : Matrix (Fin 2) (Fin 2) F)ᵀ =
      c • (M * matJ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc (g : Matrix (Fin 2) (Fin 2) F) * (M * matJ) * (h : Matrix (Fin 2) (Fin 2) F)ᵀ
        = M * (N * (g : Matrix (Fin 2) (Fin 2) F) * M * matJ *
            (h : Matrix (Fin 2) (Fin 2) F)ᵀ) := by
          simp only [← Matrix.mul_assoc]
          rw [hMN, Matrix.one_mul]
      _ = M * matJ := by rw [e]

theorem exists_smul_of_lr_eq_one {P Q : GL (Fin 2) F} (h : lr P Q = 1) :
    ∃ c : F, (P : Matrix (Fin 2) (Fin 2) F) = c • 1 ∧
      (P : Matrix (Fin 2) (Fin 2) F) * (Q : Matrix (Fin 2) (Fin 2) F)ᵀ = 1 := by
  have key : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (P : Matrix (Fin 2) (Fin 2) F) * X * (Q : Matrix (Fin 2) (Fin 2) F)ᵀ = X := by
    intro X
    have := congrArg (fun f : MulAut (VM F) => Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa [toAdd_lr] using this
  have hPQ : (P : Matrix (Fin 2) (Fin 2) F) * (Q : Matrix (Fin 2) (Fin 2) F)ᵀ = 1 := by
    simpa using key 1
  have hQP : (Q : Matrix (Fin 2) (Fin 2) F)ᵀ * (P : Matrix (Fin 2) (Fin 2) F) = 1 :=
    mul_eq_one_comm.mp hPQ
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) F, Commute X (P : Matrix (Fin 2) (Fin 2) F) := by
    intro X
    have h1 := key X
    calc X * (P : Matrix (Fin 2) (Fin 2) F)
        = (P : Matrix (Fin 2) (Fin 2) F) * X * (Q : Matrix (Fin 2) (Fin 2) F)ᵀ *
          (P : Matrix (Fin 2) (Fin 2) F) := by rw [h1]
      _ = (P : Matrix (Fin 2) (Fin 2) F) * X := by
          rw [Matrix.mul_assoc ((P : Matrix (Fin 2) (Fin 2) F) * X), hQP, Matrix.mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal], hPQ⟩

theorem lr_mem_normalizer (A B : GL (Fin 2) F) :
    lr A B ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) := by
  have key : ∀ (A B : GL (Fin 2) F)
      (γ : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F),
      lr A B * rho γ * (lr A B)⁻¹ ∈ (rho (K := F)).range := by
    intro A B γ
    have hd : ∀ (C : GL (Fin 2) F) (g : SpecialLinearGroup (Fin 2) F),
        ((C * Matrix.SpecialLinearGroup.toGL g * C⁻¹ : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).det = 1 := by
      intro C g
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
        ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
      exact g.2
    refine ⟨(⟨_, hd A γ.1⟩, ⟨_, hd B γ.2⟩), ?_⟩
    rw [rho_apply, rho_apply, lr_inv, lr_mul, lr_mul]
    congr 1 <;> exact Units.ext rfl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨γ, rfl⟩
    exact key A B γ
  · rintro ⟨γ, hγ⟩
    have h1 := key A⁻¹ B⁻¹ γ
    rw [hγ, ← lr_inv, inv_inv] at h1
    simpa [mul_assoc] using h1

end CFSG.Quasithin.H13.L32A.L2
