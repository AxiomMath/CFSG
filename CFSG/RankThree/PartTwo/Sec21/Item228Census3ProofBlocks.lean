module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofCube
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

open Matrix
open scoped commutatorElement

variable {K : Type} [Field K]

section Gram

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def gramGroup (Q : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K)ᵀ * Q * g = Q}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at *
    calc (b : Matrix ι ι K)ᵀ * (a : Matrix ι ι K)ᵀ * Q * ((a : Matrix ι ι K) * b) =
        (b : Matrix ι ι K)ᵀ * ((a : Matrix ι ι K)ᵀ * Q * a) * b := by noncomm_ring
      _ = Q := by rw [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have h1 : (a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((a⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * Q * ((a⁻¹ : GL ι K) : Matrix ι ι K) =
        ((a⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((a : Matrix ι ι K)ᵀ * Q * a) *
          ((a⁻¹ : GL ι K) : Matrix ι ι K) := by rw [ha]
      _ = ((a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * Q *
          ((a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K)) := by
          rw [Matrix.transpose_mul]; noncomm_ring
      _ = Q := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_gramGroup {Q : Matrix ι ι K} {g : GL ι K} :
    g ∈ gramGroup Q ↔ (g : Matrix ι ι K)ᵀ * Q * g = Q :=
  Iff.rfl

theorem mem_gramGroup_conj_iff {Q Q' : Matrix ι ι K} {P : GL ι K}
    (hP : (P : Matrix ι ι K)ᵀ * Q * P = Q') (g : GL ι K) :
    g ∈ gramGroup Q ↔ P⁻¹ * g * P⁻¹⁻¹ ∈ gramGroup Q' := by
  set Pm := (P : Matrix ι ι K)
  set Pi := ((P⁻¹ : GL ι K) : Matrix ι ι K)
  set gm := (g : Matrix ι ι K)
  have h1 : Pm * Pi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1' : Pi * Pm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, h1', Matrix.transpose_one]
  have h2' : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have key : ((P⁻¹ * g * P⁻¹⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * Q' *
      ((P⁻¹ * g * P⁻¹⁻¹ : GL ι K) : Matrix ι ι K) = Pmᵀ * (gmᵀ * Q * gm) * Pm := by
    rw [inv_inv, Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← hP]
    calc Pmᵀ * (gmᵀ * Piᵀ) * (Pmᵀ * Q * Pm) * (Pi * gm * Pm) =
        Pmᵀ * gmᵀ * (Piᵀ * Pmᵀ) * Q * (Pm * Pi) * gm * Pm := by noncomm_ring
      _ = Pmᵀ * (gmᵀ * Q * gm) * Pm := by rw [h2', h1]; noncomm_ring
  rw [mem_gramGroup, mem_gramGroup, key, ← hP]
  constructor
  · intro h
    rw [h]
  · intro h
    calc gmᵀ * Q * gm = (Piᵀ * Pmᵀ) * (gmᵀ * Q * gm) * (Pm * Pi) := by
          rw [h2', h1, Matrix.one_mul, Matrix.mul_one]
      _ = Piᵀ * (Pmᵀ * (gmᵀ * Q * gm) * Pm) * Pi := by noncomm_ring
      _ = Piᵀ * (Pmᵀ * Q * Pm) * Pi := by rw [h]
      _ = (Piᵀ * Pmᵀ) * Q * (Pm * Pi) := by noncomm_ring
      _ = Q := by rw [h2', h1, Matrix.one_mul, Matrix.mul_one]

end Gram

section BlockMul

variable {n : Type} [Fintype n]

theorem toBlocks₁₁_mul (X Y : Matrix (n ⊕ n) (n ⊕ n) K) :
    (X * Y).toBlocks₁₁ = X.toBlocks₁₁ * Y.toBlocks₁₁ + X.toBlocks₁₂ * Y.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]

theorem toBlocks₁₂_mul (X Y : Matrix (n ⊕ n) (n ⊕ n) K) :
    (X * Y).toBlocks₁₂ = X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₁₂]

theorem toBlocks₂₁_mul (X Y : Matrix (n ⊕ n) (n ⊕ n) K) :
    (X * Y).toBlocks₂₁ = X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]

theorem toBlocks₂₂_mul (X Y : Matrix (n ⊕ n) (n ⊕ n) K) :
    (X * Y).toBlocks₂₂ = X.toBlocks₂₁ * Y.toBlocks₁₂ + X.toBlocks₂₂ * Y.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂]

omit [Fintype n] in
theorem toBlocks_one [DecidableEq n] :
    (1 : Matrix (n ⊕ n) (n ⊕ n) K).toBlocks₁₁ = 1 ∧ (1 : Matrix (n ⊕ n) (n ⊕ n) K).toBlocks₁₂ = 0 ∧
      (1 : Matrix (n ⊕ n) (n ⊕ n) K).toBlocks₂₁ = 0 ∧
        (1 : Matrix (n ⊕ n) (n ⊕ n) K).toBlocks₂₂ = 1 := by
  rw [← fromBlocks_one]
  exact ⟨toBlocks_fromBlocks₁₁ .., toBlocks_fromBlocks₁₂ .., toBlocks_fromBlocks₂₁ ..,
    toBlocks_fromBlocks₂₂ ..⟩

end BlockMul

theorem eq_zero_of_mul_left_eq {M N : Matrix (Fin 2) (Fin 2) K} (h3 : (3 : K) ≠ 0)
    (hM : M * M + M + 1 = 0) (hN : M * N = N) : N = 0 := by
  have : (3 : K) • N = 0 := by
    calc (3 : K) • N = (M * M + M + 1) * N := by
          rw [add_mul, add_mul, Matrix.mul_assoc, hN, hN, Matrix.one_mul]; module
      _ = 0 := by rw [hM, Matrix.zero_mul]
  rwa [smul_eq_zero, or_iff_right h3] at this

theorem eq_zero_of_mul_right_eq {M N : Matrix (Fin 2) (Fin 2) K} (h3 : (3 : K) ≠ 0)
    (hM : M * M + M + 1 = 0) (hN : N * M = N) : N = 0 := by
  have : (3 : K) • N = 0 := by
    calc (3 : K) • N = N * (M * M + M + 1) := by
          rw [mul_add, mul_add, ← Matrix.mul_assoc, hN, hN, Matrix.mul_one]; module
      _ = 0 := by rw [hM, Matrix.mul_zero]
  rwa [smul_eq_zero, or_iff_right h3] at this

theorem blocks_of_commute_diagM {M : Matrix (Fin 2) (Fin 2) K} (h3 : (3 : K) ≠ 0)
    (hM : M * M + M + 1 = 0) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX : X * fromBlocks M 0 0 1 = fromBlocks M 0 0 1 * X) :
    X.toBlocks₁₂ = 0 ∧ X.toBlocks₂₁ = 0 ∧ X.toBlocks₁₁ * M = M * X.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks X, fromBlocks_multiply, fromBlocks_multiply] at hX
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at hX
  obtain ⟨e11, e12, e21, -⟩ := Matrix.fromBlocks_inj.mp hX
  exact ⟨eq_zero_of_mul_left_eq h3 hM e12.symm, eq_zero_of_mul_right_eq h3 hM e21, e11⟩

theorem nonscalar_of_sq_add (h3 : (3 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0) :
    M 0 1 ≠ 0 ∨ M 1 0 ≠ 0 ∨ M 0 0 - M 1 1 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h01, h10, h00⟩ := hcon
  have e := congrFun (congrFun hM 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10] at e
  rw [Matrix.det_fin_two, h01, h10, show M 1 1 = M 0 0 by linear_combination -h00] at hdet
  apply h3
  linear_combination (2 - M 0 0) * e + (M 0 0 - 1) * hdet

theorem commutator_eq_diag_one {G : Subgroup (GL (Fin 2 ⊕ Fin 2) K)} (h3 : (3 : K) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {D : GL (Fin 2 ⊕ Fin 2) K}
    (hD : (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks M 0 0 1)
    {g h : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ G) (hh : h ∈ G) (hgD : g * D = D * g)
    (hhD : h * D = D * h) :
    g * h * g⁻¹ * h⁻¹ ∈ G ∧
      ((g * h * g⁻¹ * h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 1 0 0 ((g * h * g⁻¹ * h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ := by
  set Cg := G ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 2 ⊕ Fin 2) K)) with hCg
  have hpat : ∀ x ∈ Cg, ((x : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ = 0 ∧
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ = 0 ∧
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ * M =
        M * ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ := by
    intro x hx
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    apply blocks_of_commute_diagM h3 hM
    rw [← hD, ← Units.val_mul, ← Units.val_mul, hc]
  have hgC : g ∈ Cg := ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgD⟩
  have hhC : h ∈ Cg := ⟨hh, Subgroup.mem_centralizer_singleton_iff.mpr hhD⟩
  let χ : Cg →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun x => ((x : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁
      map_one' := toBlocks_one.1
      map_mul' := fun x y => by
        obtain ⟨hx12, -, -⟩ := hpat x x.2
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [toBlocks₁₁_mul, hx12, Matrix.zero_mul, add_zero] }
  have hcomm : ∀ x y : Cg, χ x * χ y = χ y * χ x := fun x y =>
    commute_of_commute_nonscalar (nonscalar_of_sq_add h3 hdet hM) (hpat x x.2).2.2
      (hpat y y.2).2.2
  have hχ : χ.toHomUnits ⁅(⟨g, hgC⟩ : Cg), ⟨h, hhC⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Units.ext (hcomm _ _)
  have hk : g * h * g⁻¹ * h⁻¹ ∈ Cg :=
    Cg.mul_mem (Cg.mul_mem (Cg.mul_mem hgC hhC) (Cg.inv_mem hgC)) (Cg.inv_mem hhC)
  refine ⟨hk.1, ?_⟩
  have h11 : ((g * h * g⁻¹ * h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ = 1 := by
    have := congrArg Units.val hχ
    rw [commutatorElement_def] at this
    exact this
  obtain ⟨h12, h21, -⟩ := hpat _ hk
  conv_lhs => rw [← fromBlocks_toBlocks ((g * h * g⁻¹ * h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), h11, h12, h21]

theorem blocks_mem_cubeAlg {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX : X * fromBlocks (cubeMat K) 0 0 (cubeMat K) =
      fromBlocks (cubeMat K) 0 0 (cubeMat K) * X) :
    X.toBlocks₁₁ ∈ cubeAlg K ∧ X.toBlocks₁₂ ∈ cubeAlg K ∧ X.toBlocks₂₁ ∈ cubeAlg K ∧
      X.toBlocks₂₂ ∈ cubeAlg K := by
  rw [← fromBlocks_toBlocks X, fromBlocks_multiply, fromBlocks_multiply] at hX
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hX
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hX
  exact ⟨mem_cubeAlg.mpr e11, mem_cubeAlg.mpr e12, mem_cubeAlg.mpr e21, mem_cubeAlg.mpr e22⟩

@[expose] def detC (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  X.toBlocks₁₁ * X.toBlocks₂₂ - X.toBlocks₁₂ * X.toBlocks₂₁

theorem detC_mul {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX : X.toBlocks₁₁ ∈ cubeAlg K ∧ X.toBlocks₁₂ ∈ cubeAlg K ∧ X.toBlocks₂₁ ∈ cubeAlg K ∧
      X.toBlocks₂₂ ∈ cubeAlg K)
    (hY : Y.toBlocks₁₁ ∈ cubeAlg K ∧ Y.toBlocks₁₂ ∈ cubeAlg K ∧ Y.toBlocks₂₁ ∈ cubeAlg K ∧
      Y.toBlocks₂₂ ∈ cubeAlg K) :
    detC (X * Y) = detC X * detC Y := by
  have hXY : X * Y = fromBlocks (X.toBlocks₁₁ * Y.toBlocks₁₁ + X.toBlocks₁₂ * Y.toBlocks₂₁)
      (X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂)
      (X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁)
      (X.toBlocks₂₁ * Y.toBlocks₁₂ + X.toBlocks₂₂ * Y.toBlocks₂₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y]
    rw [fromBlocks_multiply]
  rw [detC, hXY, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, detC, detC]
  obtain ⟨a1, a2, a3, a4⟩ := hX
  obtain ⟨b1, b2, b3, b4⟩ := hY
  let x1 : cubeAlg K := ⟨_, a1⟩
  let x2 : cubeAlg K := ⟨_, a2⟩
  let x3 : cubeAlg K := ⟨_, a3⟩
  let x4 : cubeAlg K := ⟨_, a4⟩
  let y1 : cubeAlg K := ⟨_, b1⟩
  let y2 : cubeAlg K := ⟨_, b2⟩
  let y3 : cubeAlg K := ⟨_, b3⟩
  let y4 : cubeAlg K := ⟨_, b4⟩
  have key : (x1 * y1 + x2 * y3) * (x3 * y2 + x4 * y4) - (x1 * y2 + x2 * y4) * (x3 * y1 + x4 * y3) =
      (x1 * x4 - x2 * x3) * (y1 * y4 - y2 * y3) := by ring
  have := congrArg Subtype.val key
  simpa [x1, x2, x3, x4, y1, y2, y3, y4] using this

end CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
