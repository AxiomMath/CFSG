module

public import CFSG.HardMathSupport.U4FF.ClassLocSound
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Swap
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.HardMathSupport.U4FF CFSG.LocalAnalysis.WeakClosure81
open Matrix
open scoped MatrixGroups Matrix

@[expose] def beta0 (R : Type*) [Zero R] [One R] : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun I J => if (I : ℕ) + J = 5 then 1 else 0

theorem mul_beta0 {R : Type*} [CommRing R] (A : Matrix (Fin 6) (Fin 6) R) :
    A * beta0 R = A.submatrix id Fin.rev := by
  ext i j
  fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.submatrix_apply, beta0, Fin.sum_univ_six]

private lemma deriv2_beta0_lin : ∀ (i j : Fin 4), i ≠ j →
    deriv2 i j * beta0 (ZMod 2) + beta0 (ZMod 2) * (deriv2 i j)ᵀ = 0 := by
  decide +kernel

private lemma deriv2_beta0_quad : ∀ (i j : Fin 4), i ≠ j →
    deriv2 i j * beta0 (ZMod 2) * (deriv2 i j)ᵀ = 0 := by
  decide +kernel

private lemma beta0_map {k : Type*} [Field k] [CharP k 2] (f : ZMod 2 →+* k) :
    (beta0 (ZMod 2)).map f = beta0 k := by
  ext I J
  simp [beta0]

private lemma deriv2_map_lin {k : Type*} [Field k] [CharP k 2] (i j : Fin 4) (hij : i ≠ j) :
    ((deriv2 i j).map (f2 k)) * beta0 k +
      beta0 k * (((deriv2 i j).map (f2 k)))ᵀ = 0 := by
  have htrans : (f2 k).mapMatrix ((deriv2 i j)ᵀ) = ((f2 k).mapMatrix (deriv2 i j))ᵀ := by
    ext a b
    simp [RingHom.mapMatrix_apply]
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) (ZMod 2) => (f2 k).mapMatrix M)
    (deriv2_beta0_lin i j hij)
  simp only [map_zero, map_add, map_mul, htrans, RingHom.mapMatrix_apply] at h
  rwa [beta0_map (f2 k)] at h

private lemma deriv2_map_quad {k : Type*} [Field k] [CharP k 2] (i j : Fin 4) (hij : i ≠ j) :
    ((deriv2 i j).map (f2 k)) * beta0 k * (((deriv2 i j).map (f2 k)))ᵀ = 0 := by
  have htrans : (f2 k).mapMatrix ((deriv2 i j)ᵀ) = ((f2 k).mapMatrix (deriv2 i j))ᵀ := by
    ext a b
    simp [RingHom.mapMatrix_apply]
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) (ZMod 2) => (f2 k).mapMatrix M)
    (deriv2_beta0_quad i j hij)
  simp only [map_zero, map_mul, htrans, RingHom.mapMatrix_apply] at h
  rwa [beta0_map (f2 k)] at h

private lemma form_of_deriv {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (β D : Matrix n n R) (h1 : D * β + β * Dᵀ = 0) (h2 : D * β * Dᵀ = 0) :
    (1 + D) * β * (1 + D)ᵀ = β := by
  have e : (1 + D) * β * (1 + D)ᵀ = β + (D * β + β * Dᵀ) + D * β * Dᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
    noncomm_ring
  rw [e, h1, h2, add_zero, add_zero]

private lemma smul_form {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (β D : Matrix n n R) (a : R) (h1 : D * β + β * Dᵀ = 0) (h2 : D * β * Dᵀ = 0) :
    (1 + a • D) * β * (1 + a • D)ᵀ = β := by
  have h1' : (a • D) * β + β * (a • D)ᵀ = 0 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1,
      smul_zero]
  have h2' : (a • D) * β * (a • D)ᵀ = 0 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      h2, smul_zero]
  exact form_of_deriv β (a • D) h1' h2'

private lemma compound2_transvection_form {k : Type*} [Field k] [CharP k 2] (i j : Fin 4)
    (hij : i ≠ j) (a : k) :
    compound2 (1 + Matrix.single i j a) * beta0 k *
      (compound2 (1 + Matrix.single i j a))ᵀ = beta0 k := by
  rw [compound2_transvection i j hij a]
  exact smul_form (beta0 k) ((deriv2 i j).map (f2 k)) a
    (deriv2_map_lin i j hij) (deriv2_map_quad i j hij)

private def FormPres {k : Type*} [Field k] [CharP k 2] (g : SL(4, k)) : Prop :=
  compound2 (g : Matrix (Fin 4) (Fin 4) k) * beta0 k *
    (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ = beta0 k

theorem compound2_mul_beta0_mul_transpose {k : Type*} [Field k] [CharP k 2] (g : SL(4, k)) :
    compound2 (g : Matrix (Fin 4) (Fin 4) k) * beta0 k *
      (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ = beta0 k := by
  have hPone : FormPres (1 : SL(4, k)) := by
    simp [FormPres, compound2_one]
  have hPmul : ∀ x y : SL(4, k), FormPres x → FormPres y → FormPres (x * y) := by
    intro x y hx hy
    simp only [FormPres] at hx hy ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, compound2_mul, Matrix.transpose_mul]
    calc (compound2 (x : Matrix (Fin 4) (Fin 4) k) *
            compound2 (y : Matrix (Fin 4) (Fin 4) k)) * beta0 k *
            ((compound2 (y : Matrix (Fin 4) (Fin 4) k))ᵀ *
              (compound2 (x : Matrix (Fin 4) (Fin 4) k))ᵀ)
        = compound2 (x : Matrix (Fin 4) (Fin 4) k) *
            (compound2 (y : Matrix (Fin 4) (Fin 4) k) * beta0 k *
              (compound2 (y : Matrix (Fin 4) (Fin 4) k))ᵀ) *
            (compound2 (x : Matrix (Fin 4) (Fin 4) k))ᵀ := by noncomm_ring
      _ = compound2 (x : Matrix (Fin 4) (Fin 4) k) * beta0 k *
            (compound2 (x : Matrix (Fin 4) (Fin 4) k))ᵀ := by rw [hy]
      _ = beta0 k := hx
  have hPgen : ∀ t : Matrix.TransvectionStruct (Fin 4) k,
      FormPres t.toSpecialLinearGroup ∧ FormPres (t.toSpecialLinearGroup)⁻¹ := by
    intro t
    constructor
    · rw [FormPres, Matrix.TransvectionStruct.toSpecialLinearGroup_def,
        Matrix.SpecialLinearGroup.transvection_coe]
      exact compound2_transvection_form t.i t.j t.hij t.c
    · rw [FormPres, Matrix.TransvectionStruct.toSpecialLinearGroup_def,
        Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_coe]
      exact compound2_transvection_form t.i t.j t.hij (-t.c)
  have hgen : g ∈ Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 4) k → SL(4, k))) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    trivial
  have key : FormPres g ∧ FormPres g⁻¹ := by
    refine Subgroup.closure_induction (p := fun g _ => FormPres g ∧ FormPres g⁻¹)
      ?_ ?_ ?_ ?_ hgen
    · rintro _ ⟨t, rfl⟩
      exact hPgen t
    · exact ⟨hPone, by simpa using hPone⟩
    · intro x y _ _ hx hy
      exact ⟨hPmul x y hx.1 hy.1, by
        rw [_root_.mul_inv_rev]
        exact hPmul y⁻¹ x⁻¹ hy.2 hx.2⟩
    · intro x _ hx
      exact ⟨hx.2, by simpa using hx.1⟩
  exact key.1

@[expose] def wedgeDer {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 6) (Fin 6) R :=
  compound2 (X + 1) - compound2 X - 1

theorem wedgeDer_add {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    wedgeDer (X + Y) = wedgeDer X + wedgeDer Y := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [wedgeDer, compound2, pair6, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] <;> ring

theorem wedgeDer_smul {R : Type*} [CommRing R] (s : R) (X : Matrix (Fin 4) (Fin 4) R) :
    wedgeDer (s • X) = s • wedgeDer X := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [wedgeDer, compound2, pair6, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] <;> ring

theorem wedgeDer_one {R : Type*} [CommRing R] [CharP R 2] :
    wedgeDer (1 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [wedgeDer, compound2, pair6, Matrix.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem wedgeDer_conj {R : Type*} [CommRing R] (g g' X : Matrix (Fin 4) (Fin 4) R)
    (hgg' : g * g' = 1) :
    wedgeDer (g * X * g') = compound2 g * wedgeDer X * compound2 g' := by
  have h1 : g * X * g' + 1 = g * (X + 1) * g' := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg']
  have hc : compound2 g * compound2 g' = 1 := by
    rw [← compound2_mul, hgg', compound2_one]
  unfold wedgeDer
  rw [h1, compound2_mul, compound2_mul, compound2_mul, compound2_mul]
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    show compound2 g * 1 * compound2 g' = 1 by rw [Matrix.mul_one, hc]]

theorem wedgeDer_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (X : Matrix (Fin 4) (Fin 4) R) : wedgeDer (X.map f) = (wedgeDer X).map f := by
  have h1 : X.map f + 1 = (X + 1).map f := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f)]
  unfold wedgeDer
  rw [h1, Matrix.map_sub f (map_sub f), Matrix.map_sub f (map_sub f),
    Matrix.map_one f (map_zero f) (map_one f), compound2_map f (X + 1), compound2_map f X]

@[expose] def psiM {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 6) (Fin 6) R :=
  (wedgeDer X).submatrix id Fin.rev

private lemma psiM_add {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    psiM (X + Y) = psiM X + psiM Y := by
  unfold psiM
  rw [wedgeDer_add]
  ext i j
  rfl

private lemma psiM_smul {R : Type*} [CommRing R] (s : R) (X : Matrix (Fin 4) (Fin 4) R) :
    psiM (s • X) = s • psiM X := by
  unfold psiM
  rw [wedgeDer_smul]
  ext i j
  rfl

private lemma wedgeDer_zero {R : Type*} [CommRing R] :
    wedgeDer (0 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [wedgeDer, compound2, pair6, Matrix.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ]

private lemma psiM_zero {R : Type*} [CommRing R] :
    psiM (0 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  simp [psiM, wedgeDer_zero]

private lemma psiM_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (X : Matrix (Fin 4) (Fin 4) R) : psiM (X.map f) = (psiM X).map f := by
  unfold psiM
  rw [wedgeDer_map]
  ext i j
  rfl

private lemma psiM_sum {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (F : ι → Matrix (Fin 4) (Fin 4) R) :
    psiM (∑ i ∈ s, F i) = ∑ i ∈ s, psiM (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [psiM_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, psiM_add, ih]

private lemma wedgeDer_sub {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    wedgeDer (X - Y) = wedgeDer X - wedgeDer Y := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [wedgeDer, compound2, pair6, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] <;> ring

private lemma psiM_sub {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    psiM (X - Y) = psiM X - psiM Y := by
  unfold psiM
  rw [wedgeDer_sub]
  ext i j
  rfl

private lemma psiM_one {R : Type*} [CommRing R] [CharP R 2] :
    psiM (1 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  simp [psiM, wedgeDer_one]

theorem psiM_conj {k : Type*} [Field k] [CharP k 2] (g : SL(4, k))
    (X : Matrix (Fin 4) (Fin 4) k) :
    psiM ((g : Matrix (Fin 4) (Fin 4) k) * X * ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)) =
      compound2 (g : Matrix (Fin 4) (Fin 4) k) * psiM X *
        (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by
  have hgg' : (g : Matrix (Fin 4) (Fin 4) k) *
      ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hCinv : compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
      compound2 (g : Matrix (Fin 4) (Fin 4) k) = 1 := by
    rw [← compound2_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, compound2_one]
  have hCg : compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) * beta0 k =
      beta0 k * (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by
    have h2 : compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
        (compound2 (g : Matrix (Fin 4) (Fin 4) k) * beta0 k *
          (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ) = beta0 k *
          (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by
      calc compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
            (compound2 (g : Matrix (Fin 4) (Fin 4) k) * beta0 k *
              (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ)
          = (compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
              compound2 (g : Matrix (Fin 4) (Fin 4) k)) * beta0 k *
              (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by noncomm_ring
        _ = beta0 k * (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by
            rw [hCinv, Matrix.one_mul]
    have h1 : compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
        (compound2 (g : Matrix (Fin 4) (Fin 4) k) * beta0 k *
          (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ) =
        compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) * beta0 k := by
      rw [compound2_mul_beta0_mul_transpose g]
    rw [h1] at h2
    exact h2
  unfold psiM
  rw [← mul_beta0, ← mul_beta0]
  rw [wedgeDer_conj (g : Matrix (Fin 4) (Fin 4) k)
    ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) X hgg']
  calc (compound2 (g : Matrix (Fin 4) (Fin 4) k) * wedgeDer X *
        compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)) * beta0 k
      = compound2 (g : Matrix (Fin 4) (Fin 4) k) * wedgeDer X *
          (compound2 ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) * beta0 k) := by
        noncomm_ring
    _ = compound2 (g : Matrix (Fin 4) (Fin 4) k) * wedgeDer X *
          (beta0 k * (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ) := by rw [hCg]
    _ = compound2 (g : Matrix (Fin 4) (Fin 4) k) * (wedgeDer X * beta0 k) *
          (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by noncomm_ring

@[expose] def nsMat {R : Type*} (w : FinU4AmbIdx → R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun a b => w ⟨(a : ℕ) + 4 * (b : ℕ), by
    have h : ambDim (fsOf true false true) = 16 := by decide +kernel
    have := a.isLt
    have := b.isLt
    omega⟩

private def ambInv (p : Fin 4 × Fin 4) : FinU4AmbIdx :=
  ⟨(p.1 : ℕ) + 4 * (p.2 : ℕ), by
    have h : ambDim (fsOf true false true) = 16 := by decide +kernel
    rw [h]
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    omega⟩

private lemma finU4Fst_ambInv (a b : Fin 4) : finU4Fst (ambInv (a, b)) = a := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private lemma finU4Snd_ambInv (a b : Fin 4) : finU4Snd (ambInv (a, b)) = b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private def ambPairEquiv : FinU4AmbIdx ≃ Fin 4 × Fin 4 where
  toFun x := (finU4Fst x, finU4Snd x)
  invFun := ambInv
  left_inv := by
    intro x
    revert x
    decide +kernel
  right_inv := by
    intro p
    revert p
    decide +kernel

private lemma nsMat_apply {R : Type*} (w : FinU4AmbIdx → R) (p q : Fin 4) :
    nsMat w p q = w (ambInv (p, q)) := rfl

theorem nsMat_ambRepF_mulVec {k : Type*} [Field k] (g : SL(4, k)) (w : FinU4AmbIdx → k) :
    nsMat (ambRepF k (fsOf true false true) g *ᵥ w) =
      (g : Matrix (Fin 4) (Fin 4) k) * nsMat w * ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) := by
  ext a b
  have hL : nsMat (ambRepF k (fsOf true false true) g *ᵥ w) a b =
      ∑ p : Fin 4, ∑ q : Fin 4, (g : Matrix (Fin 4) (Fin 4) k) a p *
        ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) q b * w (ambInv (p, q)) := by
    simp only [nsMat, Matrix.of_apply]
    calc (∑ j : FinU4AmbIdx,
          ambRepF k (fsOf true false true) g (ambInv (a, b)) j * w j)
        = ∑ p : Fin 4 × Fin 4, (g : Matrix (Fin 4) (Fin 4) k) a p.1 *
            ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) p.2 b * w (ambInv p) := by
          refine Fintype.sum_equiv ambPairEquiv _ _ ?_
          intro x
          rw [ambRepF_apply_natDual]
          rw [finU4Fst_ambInv a b, finU4Snd_ambInv a b]
          rw [show ambPairEquiv x = (finU4Fst x, finU4Snd x) from rfl]
          rw [show ambInv (finU4Fst x, finU4Snd x) = x from ambPairEquiv.left_inv x]
      _ = ∑ p : Fin 4, ∑ q : Fin 4, (g : Matrix (Fin 4) (Fin 4) k) a p *
            ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) q b * w (ambInv (p, q)) := by
          rw [Fintype.sum_prod_type]
  have hR : ((g : Matrix (Fin 4) (Fin 4) k) * nsMat w *
      ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)) a b =
      ∑ p : Fin 4, ∑ q : Fin 4, (g : Matrix (Fin 4) (Fin 4) k) a p *
        ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) q b * w (ambInv (p, q)) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, nsMat_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hL, hR]

private lemma nsMat_add {R : Type*} [Add R] (u v : FinU4AmbIdx → R) :
    nsMat (u + v) = nsMat u + nsMat v := rfl

private lemma nsMat_sub {R : Type*} [Sub R] (u v : FinU4AmbIdx → R) :
    nsMat (u - v) = nsMat u - nsMat v := rfl

private lemma nsMat_smul {R : Type*} [SMul R R] (s : R) (u : FinU4AmbIdx → R) :
    nsMat (s • u) = s • nsMat u := rfl

private lemma nsMat_zF2 :
    nsMat (R := ZMod 2) (fun x => bitF (locData true false true).z (x : ℕ)) = 1 := by
  decide +kernel

theorem nsMat_zk (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2] :
    nsMat ((locSpec true false true h).zk k) = 1 := by
  have hzk : (locSpec true false true h).zk k =
      fun x : Fin (ambDim (fsOf true false true)) =>
        f2 k (bitF (locData true false true).z (x : ℕ)) := rfl
  rw [hzk]
  change (nsMat (fun x => bitF (locData true false true).z (x : ℕ))).map (f2 k) = 1
  rw [nsMat_zF2, Matrix.map_one (f2 k) (map_zero (f2 k)) (map_one (f2 k))]

@[expose] noncomputable def theta101 (h : LocValid1 true false true) (k : Type*) [Field k]
    [CharP k 2] (v : Fin (locM true false true) → k) : Matrix (Fin 6) (Fin 6) k :=
  psiM (nsMat ((locSpec true false true h).Bk k *ᵥ v))

theorem theta101_add (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (v w : Fin (locM true false true) → k) :
    theta101 h k (v + w) = theta101 h k v + theta101 h k w := by
  unfold theta101
  rw [Matrix.mulVec_add, nsMat_add, psiM_add]

theorem theta101_smul (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (s : k) (v : Fin (locM true false true) → k) :
    theta101 h k (s • v) = s • theta101 h k v := by
  unfold theta101
  rw [Matrix.mulVec_smul, nsMat_smul, psiM_smul]

theorem theta101_locMat (h : LocValid1 true false true) {k : Type*} [Field k] [CharP k 2]
    (g : SL(4, k)) (v : Fin (locM true false true) → k) :
    theta101 h k ((locSpec true false true h).locMat k g *ᵥ v) =
      compound2 (g : Matrix (Fin 4) (Fin 4) k) * theta101 h k v *
        (compound2 (g : Matrix (Fin 4) (Fin 4) k))ᵀ := by
  unfold theta101
  set w : Fin (locSpec true false true h).m → k :=
    (locSpec true false true h).zetak k ᵥ* (ambRepF k (fsOf true false true) g *
      (locSpec true false true h).Bk k) with hw
  have hamb := LocSpec.amb_B (locSpec true false true h) k g
  have hB : (locSpec true false true h).Bk k * (locSpec true false true h).locMat k g =
      ambRepF k (fsOf true false true) g * (locSpec true false true h).Bk k -
        vecMulVec ((locSpec true false true h).zk k) w := by
    rw [hw, eq_sub_iff_add_eq]
    exact hamb.symm
  have hop : MulOpposite.op (w ⬝ᵥ v) • (locSpec true false true h).zk k =
      (w ⬝ᵥ v) • (locSpec true false true h).zk k := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, op_smul_eq_mul, smul_eq_mul, mul_comm]
  have hvec : (locSpec true false true h).Bk k *ᵥ
      ((locSpec true false true h).locMat k g *ᵥ v) =
      ambRepF k (fsOf true false true) g *ᵥ ((locSpec true false true h).Bk k *ᵥ v) -
        (w ⬝ᵥ v) • (locSpec true false true h).zk k := by
    rw [Matrix.mulVec_mulVec]
    rw [hB]
    rw [Matrix.sub_mulVec]
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.vecMulVec_mulVec]
    rw [hop]
  have hns : nsMat ((locSpec true false true h).Bk k *ᵥ
      ((locSpec true false true h).locMat k g *ᵥ v)) =
      (g : Matrix (Fin 4) (Fin 4) k) * nsMat ((locSpec true false true h).Bk k *ᵥ v) *
        ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) -
        (w ⬝ᵥ v) • (1 : Matrix (Fin 4) (Fin 4) k) := by
    rw [hvec]
    rw [nsMat_sub]
    rw [nsMat_ambRepF_mulVec]
    rw [nsMat_smul]
    rw [nsMat_zk]
  rw [hns]
  rw [psiM_sub]
  rw [psiM_smul]
  rw [psiM_one]
  simp only [smul_zero, sub_zero]
  exact psiM_conj g (nsMat ((locSpec true false true h).Bk k *ᵥ v))

@[expose] def thPos : Fin 14 → Fin 6 × Fin 6 :=
  ![(1, 3), (0, 3), (0, 1), (2, 4), (0, 5), (0, 4), (0, 2), (2, 5), (1, 5), (1, 4), (1, 2),
    (4, 5), (3, 5), (3, 4)]

@[expose] def thetaF2 (c : Fin 14) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  psiM (nsMat fun x => (locData true false true).bcols.toMat (ambDim (fsOf true false true)) 14 x c)

private lemma thetaF2_test : thetaF2 4 0 5 = 1 ∧ thetaF2 4 2 3 = 1 ∧ thetaF2 9 1 4 = 1 := by
  decide +kernel

private lemma thetaF2_transpose : ∀ c : Fin 14, (thetaF2 c)ᵀ = thetaF2 c := by
  decide +kernel

private lemma thetaF2_thPos : ∀ c j : Fin 14,
    thetaF2 c (thPos j).1 (thPos j).2 = if c = j then 1 else 0 := by
  decide +kernel

private lemma thetaF2_diag : ∀ c : Fin 14, ∀ i : Fin 6, thetaF2 c i i = 0 := by
  decide +kernel

private lemma thetaF2_f0 : ∀ c : Fin 14, thetaF2 c 0 5 + thetaF2 c 1 4 + thetaF2 c 2 3 = 0 := by
  decide +kernel

private lemma theta101_eq_sum (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (v : Fin (locM true false true) → k) :
    theta101 h k v = ∑ c : Fin 14, v c • (thetaF2 c).map (f2 k) := by
  unfold theta101
  let B : Matrix (Fin (ambDim (fsOf true false true))) (Fin 14) (ZMod 2) :=
    (locData true false true).bcols.toMat (ambDim (fsOf true false true)) 14
  have hB : (locSpec true false true h).Bk k *ᵥ v =
      ∑ c : Fin 14, v c • (fun x => f2 k (B x c)) := by
    ext x
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [show (locSpec true false true h).Bk k x c = f2 k (B x c) from rfl]
    ring
  rw [hB]
  have hns : nsMat (∑ c : Fin 14, v c • (fun x => f2 k (B x c))) =
      ∑ c : Fin 14, v c • nsMat (fun x => f2 k (B x c)) := by
    ext a b
    simp only [nsMat, Matrix.of_apply, Finset.sum_apply, Matrix.sum_apply,
      Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hns]
  rw [psiM_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [psiM_smul]
  rw [show nsMat (fun x => f2 k (B x c)) = (nsMat (fun x => B x c)).map (f2 k) from rfl]
  rw [psiM_map]
  rfl

theorem theta101_transpose (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (v : Fin (locM true false true) → k) : (theta101 h k v)ᵀ = theta101 h k v := by
  rw [theta101_eq_sum]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro c _
  have h := congrFun (congrFun (thetaF2_transpose c) j) i
  simp only [Matrix.transpose_apply] at h
  rw [h]

theorem theta101_diag (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (v : Fin (locM true false true) → k) (i : Fin 6) : theta101 h k v i i = 0 := by
  rw [theta101_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [thetaF2_diag c i]
  simp

theorem theta101_f0 (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (v : Fin (locM true false true) → k) :
    theta101 h k v 0 5 + theta101 h k v 1 4 + theta101 h k v 2 3 = 0 := by
  rw [theta101_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h : f2 k (thetaF2 c 0 5) + f2 k (thetaF2 c 1 4) + f2 k (thetaF2 c 2 3) = 0 := by
    rw [← map_add, ← map_add, thetaF2_f0 c, map_zero]
  rw [← smul_add, ← smul_add, h, smul_zero]

theorem theta101_thPos (h : LocValid1 true false true) (k : Type*) [Field k] [CharP k 2]
    (v : Fin (locM true false true) → k) (j : Fin 14) :
    theta101 h k v (thPos j).1 (thPos j).2 = v j := by
  rw [theta101_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro c _ hcj
    rw [thetaF2_thPos c j, if_neg hcj]
    simp
  · intro hj
    exact absurd (Finset.mem_univ j) hj
  · rw [thetaF2_thPos j j, if_pos rfl]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
