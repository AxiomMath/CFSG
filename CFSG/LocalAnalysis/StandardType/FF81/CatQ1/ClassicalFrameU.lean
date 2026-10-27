module

public import CFSG.Mathlib.LinearAlgebra.Matrix.BlockFrame
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinFrame
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.HardMathSupport.Lang.Proving.CubeClassField

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f n : ℕ} {F : Type*} [Field F]

private theorem cq1_adj_mul {m n p : ℕ} (h : UnitaryFieldData ℓ f F)
    (M : Matrix (Fin m) (Fin n) F) (N : Matrix (Fin n) (Fin p) F) :
    ((M * N).map h.bar)ᵀ = (N.map h.bar)ᵀ * (M.map h.bar)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cq1_adj_adj (h : UnitaryFieldData ℓ f F) {m p : ℕ}
    (M : Matrix (Fin m) (Fin p) F) :
    (((M.map h.bar)ᵀ).map h.bar)ᵀ = M := by
  ext i j
  simp [Matrix.transpose_apply, Matrix.map_apply, h.bar_bar]

private theorem cq1_adj_sub (h : UnitaryFieldData ℓ f F) (M N : Matrix (Fin n) (Fin n) F) :
    ((M - N).map h.bar)ᵀ = (M.map h.bar)ᵀ - (N.map h.bar)ᵀ := by
  rw [Matrix.map_sub h.bar (fun a b => map_sub h.bar a b), Matrix.transpose_sub]

private theorem cq1_adj_eq_of_adj_mul_eq (h : UnitaryFieldData ℓ f F) {m p : ℕ}
    {B : Matrix (Fin m) (Fin m) F} {U : Matrix (Fin m) (Fin p) F}
    {D : Matrix (Fin p) (Fin p) F} (hBU : (B.map h.bar)ᵀ * U = U * D) :
    (U.map h.bar)ᵀ * B = (D.map h.bar)ᵀ * (U.map h.bar)ᵀ := by
  have h1 := congrArg (fun M => (M.map h.bar)ᵀ) hBU
  rwa [cq1_adj_mul h, cq1_adj_adj h, cq1_adj_mul h] at h1

private noncomputable def cq1_pair (h : UnitaryFieldData ℓ f F) {n : ℕ}
    (x y : Fin n → F) : F :=
  ∑ i, h.bar (x i) * y i

private theorem cq1_pair_add_left (h : UnitaryFieldData ℓ f F) (x y z : Fin n → F) :
    cq1_pair h (x + y) z = cq1_pair h x z + cq1_pair h y z := by
  simp [cq1_pair, add_mul, Finset.sum_add_distrib]

private theorem cq1_pair_add_right (h : UnitaryFieldData ℓ f F) (x y z : Fin n → F) :
    cq1_pair h x (y + z) = cq1_pair h x y + cq1_pair h x z := by
  simp [cq1_pair, mul_add, Finset.sum_add_distrib]

private theorem cq1_pair_smul_left (h : UnitaryFieldData ℓ f F) (x y : Fin n → F) (c : F) :
    cq1_pair h (c • x) y = h.bar c * cq1_pair h x y := by
  simp [cq1_pair, Finset.mul_sum, mul_assoc]

private theorem cq1_pair_smul_right (h : UnitaryFieldData ℓ f F) (x y : Fin n → F) (c : F) :
    cq1_pair h x (c • y) = c * cq1_pair h x y := by
  simp [cq1_pair, Finset.mul_sum, mul_left_comm]

private theorem cq1_pair_comm (h : UnitaryFieldData ℓ f F) (x y : Fin n → F) :
    cq1_pair h y x = h.bar (cq1_pair h x y) := by
  simp [cq1_pair, map_sum, h.bar_bar, mul_comm]

private theorem cq1_pair_adj (h : UnitaryFieldData ℓ f F)
    (M : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) :
    cq1_pair h (M *ᵥ x) y = cq1_pair h x ((M.map h.bar)ᵀ *ᵥ y) := by
  have e1 : (fun i => h.bar ((M *ᵥ x) i)) = (M.map h.bar) *ᵥ (fun i => h.bar (x i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_mul])
  calc cq1_pair h (M *ᵥ x) y
      = (fun i => h.bar ((M *ᵥ x) i)) ⬝ᵥ y := by simp [cq1_pair, dotProduct]
    _ = ((M.map h.bar) *ᵥ (fun i => h.bar (x i))) ⬝ᵥ y := by rw [e1]
    _ = ((fun i => h.bar (x i)) ᵥ* (M.map h.bar)ᵀ) ⬝ᵥ y := by
          rw [Matrix.vecMul_transpose]
    _ = (fun i => h.bar (x i)) ⬝ᵥ ((M.map h.bar)ᵀ *ᵥ y) := by
          rw [Matrix.dotProduct_mulVec]
    _ = cq1_pair h x ((M.map h.bar)ᵀ *ᵥ y) := by simp [cq1_pair, dotProduct]

private theorem cq1_aeval_mulVec_mem (B : Matrix (Fin n) (Fin n) F)
    (S : Submodule F (Fin n → F)) (hS : ∀ x ∈ S, B *ᵥ x ∈ S) (q : Polynomial F) :
    ∀ x ∈ S, (Polynomial.aeval B q) *ᵥ x ∈ S := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro x hx
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    exact S.smul_mem _ hx
  | add p q hp hq =>
    intro x hx
    rw [map_add, Matrix.add_mulVec]
    exact S.add_mem (hp x hx) (hq x hx)
  | monomial m a ih =>
    intro x hx
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, ← Matrix.mulVec_mulVec]
    exact ih _ (hS x hx)

private theorem cq1_exists_poly_inv (B : Matrix (Fin n) (Fin n) F) {l : F}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) F)) (hl : ∀ x : F, x ^ 3 ≠ l)
    (c : Fin 3 → F) (hc : c ≠ 0) :
    ∃ b : Polynomial F, Polynomial.aeval B b *
      (c 0 • (1 : Matrix (Fin n) (Fin n) F) + c 1 • B + c 2 • B ^ 2) = 1 := by
  classical
  have hirr := CFSG.HardMathSupport.Lang.Proving.irreducible_X_pow_three_sub_C hl
  set g : Polynomial F :=
    Polynomial.C (c 2) * Polynomial.X ^ 2 + Polynomial.C (c 1) * Polynomial.X +
      Polynomial.C (c 0) with hg
  have hcoef : ∀ k, g.coeff k = if k = 0 then c 0 else if k = 1 then c 1 else if k = 2 then c 2
      else 0 := by
    intro k
    simp only [hg, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    rcases k with _ | _ | _ | k <;> simp
  have hg0 : g ≠ 0 := by
    intro h0
    apply hc
    ext i
    have := hcoef i
    rw [h0, Polynomial.coeff_zero] at this
    fin_cases i <;> simpa using this.symm
  have hdeg : g.natDegree < 3 := by
    have : g.natDegree ≤ 2 := Polynomial.natDegree_quadratic_le
    omega
  have hndvd : ¬ (Polynomial.X ^ 3 - Polynomial.C l : Polynomial F) ∣ g := fun hd => by
    have := Polynomial.natDegree_le_of_dvd hd hg0
    rw [Polynomial.natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
  have hp0 : Polynomial.aeval B (Polynomial.X ^ 3 - Polynomial.C l : Polynomial F) = 0 := by
    simp [hB3, Algebra.algebraMap_eq_smul_one]
  have hgB : Polynomial.aeval B g =
      c 0 • (1 : Matrix (Fin n) (Fin n) F) + c 1 • B + c 2 • B ^ 2 := by
    simp [hg, Algebra.algebraMap_eq_smul_one]
    abel
  have h1 := congrArg (Polynomial.aeval B) hab
  rw [map_add, map_mul, map_mul, hp0, mul_zero, zero_add, map_one] at h1
  rw [hgB] at h1
  exact ⟨b, h1⟩

private theorem cq1_cubicCompanion_cube (c : F) :
    cubicCompanion c ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCompanion, pow_succ, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]

private theorem cq1_cubicCompanion_mul_inv_sq (c : F) (hc : c ≠ 0) :
    cubicCompanion c * (c⁻¹ • cubicCompanion c ^ 2) = 1 := by
  rw [Matrix.mul_smul, ← pow_succ', cq1_cubicCompanion_cube, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

private theorem cq1_orbitDual_core (h : UnitaryFieldData ℓ f F) {p : ℕ}
    {B : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin p) F}
    {C D G : Matrix (Fin p) (Fin p) F}
    (hBU : (B.map h.bar)ᵀ * U = U * D)
    (hCG : (C.map h.bar)ᵀ * G * C = G)
    (hDadjCadj : (D.map h.bar)ᵀ * (C.map h.bar)ᵀ = 1) (hdet : IsUnit G.det) :
    (G⁻¹ * (U.map h.bar)ᵀ) * B = C * (G⁻¹ * (U.map h.bar)ᵀ) := by
  have hUB : (U.map h.bar)ᵀ * B = (D.map h.bar)ᵀ * (U.map h.bar)ᵀ :=
    cq1_adj_eq_of_adj_mul_eq h hBU
  have hDG : (D.map h.bar)ᵀ * G = G * C := by
    calc (D.map h.bar)ᵀ * G = (D.map h.bar)ᵀ * ((C.map h.bar)ᵀ * G * C) := by rw [hCG]
      _ = ((D.map h.bar)ᵀ * (C.map h.bar)ᵀ) * G * C := by
            simp only [Matrix.mul_assoc]
      _ = G * C := by rw [hDadjCadj, Matrix.one_mul]
  have hGD : G⁻¹ * (D.map h.bar)ᵀ = C * G⁻¹ := by
    calc G⁻¹ * (D.map h.bar)ᵀ
        = G⁻¹ * (D.map h.bar)ᵀ * (G * G⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = G⁻¹ * ((D.map h.bar)ᵀ * G) * G⁻¹ := by simp only [Matrix.mul_assoc]
      _ = G⁻¹ * (G * C) * G⁻¹ := by rw [hDG]
      _ = C * G⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  calc (G⁻¹ * (U.map h.bar)ᵀ) * B = G⁻¹ * ((U.map h.bar)ᵀ * B) := Matrix.mul_assoc _ _ _
    _ = G⁻¹ * ((D.map h.bar)ᵀ * (U.map h.bar)ᵀ) := by rw [hUB]
    _ = (G⁻¹ * (D.map h.bar)ᵀ) * (U.map h.bar)ᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = (C * G⁻¹) * (U.map h.bar)ᵀ := by rw [hGD]
    _ = C * (G⁻¹ * (U.map h.bar)ᵀ) := Matrix.mul_assoc _ _ _

private theorem cq1_cubicCompanion_gram (h : UnitaryFieldData ℓ f F)
    {U : Matrix (Fin n) (Fin 3) F} {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB : (B.map h.bar)ᵀ * B = 1) (hBU : B * U = U * cubicCompanion c) :
    ((cubicCompanion c).map h.bar)ᵀ * ((U.map h.bar)ᵀ * U) * cubicCompanion c =
      (U.map h.bar)ᵀ * U := by
  calc ((cubicCompanion c).map h.bar)ᵀ * ((U.map h.bar)ᵀ * U) * cubicCompanion c
      = ((U * cubicCompanion c).map h.bar)ᵀ * (U * cubicCompanion c) := by
          rw [cq1_adj_mul h U (cubicCompanion c)]
          simp only [Matrix.mul_assoc]
    _ = ((B * U).map h.bar)ᵀ * (B * U) := by rw [hBU]
    _ = (U.map h.bar)ᵀ * ((B.map h.bar)ᵀ * B) * U := by
          rw [cq1_adj_mul h B U]
          simp only [Matrix.mul_assoc]
    _ = (U.map h.bar)ᵀ * U := by rw [hB]; simp

private theorem cq1_gram_adj (h : UnitaryFieldData ℓ f F) {p : ℕ}
    (U : Matrix (Fin n) (Fin p) F) :
    ((((U.map h.bar)ᵀ * U).map h.bar)ᵀ) = (U.map h.bar)ᵀ * U := by
  rw [cq1_adj_mul h, cq1_adj_adj h]

private theorem cq1_hermitian_core (h : UnitaryFieldData ℓ f F) {p : ℕ}
    {U : Matrix (Fin n) (Fin p) F} {G : Matrix (Fin p) (Fin p) F}
    (hGadj : (G.map h.bar)ᵀ = G) (hdet : IsUnit G.det) :
    ((U * (G⁻¹ * (U.map h.bar)ᵀ)).map h.bar)ᵀ = U * (G⁻¹ * (U.map h.bar)ᵀ) := by
  have hGinv : ((G⁻¹).map h.bar)ᵀ = G⁻¹ := by
    have h1 : ((G⁻¹).map h.bar)ᵀ * G = 1 := by
      calc ((G⁻¹).map h.bar)ᵀ * G = ((G⁻¹).map h.bar)ᵀ * (G.map h.bar)ᵀ := by rw [hGadj]
        _ = ((G * G⁻¹).map h.bar)ᵀ := (cq1_adj_mul h G G⁻¹).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdet]; simp
    exact (Matrix.inv_eq_left_inv h1).symm
  calc ((U * (G⁻¹ * (U.map h.bar)ᵀ)).map h.bar)ᵀ
      = ((G⁻¹ * (U.map h.bar)ᵀ).map h.bar)ᵀ * (U.map h.bar)ᵀ := cq1_adj_mul h U _
    _ = (((U.map h.bar)ᵀ).map h.bar)ᵀ * ((G⁻¹).map h.bar)ᵀ * (U.map h.bar)ᵀ := by
          rw [cq1_adj_mul h G⁻¹]
    _ = (U * G⁻¹) * (U.map h.bar)ᵀ := by rw [cq1_adj_adj h, hGinv]
    _ = U * (G⁻¹ * (U.map h.bar)ᵀ) := Matrix.mul_assoc _ _ _

private theorem cq1_orbitT_stable (h : UnitaryFieldData ℓ f F)
    {B : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin 3) F} {c : F}
    (hBU : (B.map h.bar)ᵀ * U = U * (c⁻¹ • cubicCompanion c ^ 2))
    (hBUC : B * U = U * cubicCompanion c) :
    ∀ x ∈ LinearMap.ker (Matrix.mulVecLin ((U.map h.bar)ᵀ)) ⊓
        LinearMap.range (Matrix.mulVecLin U),
      B *ᵥ x ∈ LinearMap.ker (Matrix.mulVecLin ((U.map h.bar)ᵀ)) ⊓
        LinearMap.range (Matrix.mulVecLin U) := by
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx1
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have hUB := cq1_adj_eq_of_adj_mul_eq h hBU
    calc (U.map h.bar)ᵀ *ᵥ (B *ᵥ x) = ((U.map h.bar)ᵀ * B) *ᵥ x :=
          Matrix.mulVec_mulVec _ _ _
      _ = (((c⁻¹ • cubicCompanion c ^ 2).map h.bar)ᵀ * (U.map h.bar)ᵀ) *ᵥ x := by
            rw [hUB]
      _ = ((c⁻¹ • cubicCompanion c ^ 2).map h.bar)ᵀ *ᵥ ((U.map h.bar)ᵀ *ᵥ x) :=
            (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hx1, Matrix.mulVec_zero]
  · obtain ⟨z, hz⟩ := hx2
    rw [Matrix.mulVecLin_apply] at hz
    refine ⟨cubicCompanion c *ᵥ z, ?_⟩
    rw [Matrix.mulVecLin_apply, ← hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBUC]

private theorem cq1_pB_mulVec (B : Matrix (Fin n) (Fin n) F) {u : Fin n → F}
    {y : Fin 3 → F} :
    (y 0 • 1 + y 1 • B + y 2 • B ^ 2) *ᵥ u = orbitMatrix B u *ᵥ y := by
  have hL : (y 0 • 1 + y 1 • B + y 2 • B ^ 2) *ᵥ u =
      y 0 • u + y 1 • (B *ᵥ u) + y 2 • ((B ^ 2) *ᵥ u) := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hR : orbitMatrix B u *ᵥ y =
      y 0 • u + y 1 • (B *ᵥ u) + y 2 • ((B ^ 2) *ᵥ u) := by
    ext k
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [orbitMatrix, Matrix.of_apply, Fin.sum_univ_three, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, Matrix.one_mulVec, Pi.add_apply,
      Pi.smul_apply]
    ring
  rw [hL, hR]

theorem conjTranspose_mul_orbitMatrix {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) {B : Matrix (Fin n) (Fin n) F} (hB : (B.map h.bar)ᵀ * B = 1)
    {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hc : c ≠ 0) (u : Fin n → F) :
    (B.map h.bar)ᵀ * orbitMatrix B u = orbitMatrix B u * (c⁻¹ • cubicCompanion c ^ 2) := by
  have hBB : B * (c⁻¹ • B ^ 2) = 1 := by
    rw [Matrix.mul_smul, ← pow_succ', hB3, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hadj : (B.map h.bar)ᵀ = c⁻¹ • B ^ 2 := by
    calc (B.map h.bar)ᵀ = (B.map h.bar)ᵀ * 1 := (mul_one _).symm
      _ = (B.map h.bar)ᵀ * (B * (c⁻¹ • B ^ 2)) := by rw [hBB]
      _ = ((B.map h.bar)ᵀ * B) * (c⁻¹ • B ^ 2) := by rw [Matrix.mul_assoc]
      _ = 1 * (c⁻¹ • B ^ 2) := by rw [hB]
      _ = c⁻¹ • B ^ 2 := by rw [one_mul]
  have hpow : B ^ 2 * orbitMatrix B u = orbitMatrix B u * cubicCompanion c ^ 2 := by
    have h1 := mul_orbitMatrix hB3 u
    calc B ^ 2 * orbitMatrix B u = (B * B) * orbitMatrix B u := by rw [pow_two]
      _ = B * (B * orbitMatrix B u) := by rw [Matrix.mul_assoc]
      _ = B * (orbitMatrix B u * cubicCompanion c) := by rw [h1]
      _ = (B * orbitMatrix B u) * cubicCompanion c := by rw [Matrix.mul_assoc]
      _ = (orbitMatrix B u * cubicCompanion c) * cubicCompanion c := by rw [h1]
      _ = orbitMatrix B u * (cubicCompanion c * cubicCompanion c) := by rw [Matrix.mul_assoc]
      _ = orbitMatrix B u * cubicCompanion c ^ 2 := by rw [pow_two]
  rw [hadj, Matrix.smul_mul, hpow, Matrix.mul_smul]

private theorem cq1_gram_orbit_ker (h : UnitaryFieldData ℓ f F)
    {B : Matrix (Fin n) (Fin n) F} (hB : (B.map h.bar)ᵀ * B = 1) {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hc : ∀ x : F, x ^ 3 ≠ c)
    {u : Fin n → F} {y : Fin 3 → F} (hy : y ≠ 0)
    (hyG : (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u) *ᵥ y = 0) :
    ((orbitMatrix B u).map h.bar)ᵀ *ᵥ u = 0 := by
  classical
  have hc0 : c ≠ 0 := by rintro rfl; exact hc 0 (by simp)
  let U : Matrix (Fin n) (Fin 3) F := orbitMatrix B u
  let pB : Matrix (Fin n) (Fin n) F := y 0 • 1 + y 1 • B + y 2 • B ^ 2
  have hpB : pB *ᵥ u = U *ᵥ y := by
    have h1 : pB = y 0 • 1 + y 1 • B + y 2 • B ^ 2 := rfl
    rw [h1, cq1_pB_mulVec B]
  let w : Fin n → F := U *ᵥ y
  have hw : w = pB *ᵥ u := hpB.symm
  obtain ⟨r, hr⟩ := cq1_exists_poly_inv B hB3 hc y hy
  have hu_eq : u = (Polynomial.aeval B r) *ᵥ w := by
    calc u = (1 : Matrix (Fin n) (Fin n) F) *ᵥ u := (Matrix.one_mulVec u).symm
      _ = ((Polynomial.aeval B r) * pB) *ᵥ u := by rw [hr]
      _ = (Polynomial.aeval B r) *ᵥ (pB *ᵥ u) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = (Polynomial.aeval B r) *ᵥ w := by rw [← hw]
  let T : Submodule F (Fin n → F) :=
    LinearMap.ker (Matrix.mulVecLin ((U.map h.bar)ᵀ)) ⊓
      LinearMap.range (Matrix.mulVecLin U)
  have hTmem : ∀ x : Fin n → F,
      x ∈ T ↔ (U.map h.bar)ᵀ *ᵥ x = 0 ∧ ∃ z : Fin 3 → F, U *ᵥ z = x := by
    intro x
    simp only [T, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range,
      Matrix.mulVecLin_apply]
  have hTstable : ∀ x ∈ T, B *ᵥ x ∈ T :=
    cq1_orbitT_stable h (conjTranspose_mul_orbitMatrix h hB hB3 hc0 u) (mul_orbitMatrix hB3 u)
  have hwT : w ∈ T := by
    rw [hTmem]
    refine ⟨?_, ⟨y, rfl⟩⟩
    have : (U.map h.bar)ᵀ *ᵥ w = (((U.map h.bar)ᵀ * U) *ᵥ y) := by
      rw [Matrix.mulVec_mulVec]
    rw [this]
    exact hyG
  have huT : u ∈ T := by
    have hmem := cq1_aeval_mulVec_mem B T hTstable r w hwT
    rwa [← hu_eq] at hmem
  exact ((hTmem u).mp huT).1

theorem isUnit_det_gram_orbitMatrix {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) {B : Matrix (Fin n) (Fin n) F} (hB : (B.map h.bar)ᵀ * B = 1)
    {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hc : ∀ x : F, x ^ 3 ≠ c)
    {u : Fin n → F} (hu : ∑ k, h.bar (u k) * u k ≠ 0) :
    IsUnit (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u).det := by
  classical
  by_contra hdet
  have hdet0 : (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u).det = 0 := by
    by_contra hnot
    exact hdet (isUnit_iff_ne_zero.mpr hnot)
  obtain ⟨y, hy, hyG⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  have hu_ker := cq1_gram_orbit_ker h hB hB3 hc hy hyG
  have hcomp : (((orbitMatrix B u).map h.bar)ᵀ *ᵥ u) 0 = cq1_pair h u u := by
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.transpose_apply, Matrix.map_apply, orbitMatrix, Matrix.of_apply,
      Fin.val_zero, pow_zero, Matrix.one_mulVec, cq1_pair]
  have h0 : cq1_pair h u u = 0 := by
    rw [← hcomp]
    exact congrFun hu_ker 0
  exact hu h0

private theorem cq1_pair_eq_zero_of_diag (h : UnitaryFieldData ℓ f F)
    {Q : Matrix (Fin n) (Fin n) F} (hQ : (Q.map h.bar)ᵀ = Q)
    (hcon : ∀ x : Fin n → F, cq1_pair h x (Q *ᵥ x) = 0) :
    ∀ x y : Fin n → F, cq1_pair h x (Q *ᵥ y) = 0 := by
  obtain ⟨lam, hlam⟩ := h.exists_bar_ne
  have hHQ : ∀ x y : Fin n → F,
      cq1_pair h y (Q *ᵥ x) = h.bar (cq1_pair h x (Q *ᵥ y)) := by
    intro x y
    have h1 : cq1_pair h (Q *ᵥ x) y = cq1_pair h x (Q *ᵥ y) := by
      rw [cq1_pair_adj h Q x y, hQ]
    calc cq1_pair h y (Q *ᵥ x) = h.bar (cq1_pair h (Q *ᵥ x) y) := cq1_pair_comm h (Q *ᵥ x) y
      _ = h.bar (cq1_pair h x (Q *ᵥ y)) := by rw [h1]
  have h_add : ∀ z w : Fin n → F, cq1_pair h z (Q *ᵥ w) + cq1_pair h w (Q *ᵥ z) = 0 := by
    intro z w
    have h1 : cq1_pair h (z + w) (Q *ᵥ (z + w)) = 0 := hcon (z + w)
    simp only [Matrix.mulVec_add, cq1_pair_add_right, cq1_pair_add_left] at h1
    have hz0 : cq1_pair h z (Q *ᵥ z) = 0 := hcon z
    have hw0 : cq1_pair h w (Q *ᵥ w) = 0 := hcon w
    rw [hz0, hw0] at h1
    simpa [add_comm] using h1
  have hbar : ∀ x y : Fin n → F,
      h.bar (cq1_pair h x (Q *ᵥ y)) = - cq1_pair h x (Q *ᵥ y) := by
    intro x y
    have h1 := h_add x y
    rw [hHQ x y] at h1
    rw [← add_eq_zero_iff_eq_neg]
    simpa [add_comm] using h1
  intro x y
  have h1 := h_add x (lam • y)
  rw [Matrix.mulVec_smul, cq1_pair_smul_right, cq1_pair_smul_left, hHQ x y, hbar x y] at h1
  have heq : lam * cq1_pair h x (Q *ᵥ y) = h.bar lam * cq1_pair h x (Q *ᵥ y) := by
    rw [mul_neg, ← sub_eq_add_neg] at h1
    exact sub_eq_zero.mp h1
  have h2 : (lam - h.bar lam) * cq1_pair h x (Q *ᵥ y) = 0 := by
    rw [sub_mul, heq, sub_self]
  have hneq : lam - h.bar lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam)
  exact (mul_eq_zero.mp h2).resolve_left hneq

theorem exists_sum_bar_mul_ne_zero_of_isHermitian {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) {Q : Matrix (Fin n) (Fin n) F} (hQ : (Q.map h.bar)ᵀ = Q)
    (hQ0 : Q ≠ 0) : ∃ x : Fin n → F, ∑ k, h.bar (x k) * (Q *ᵥ x) k ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have key := cq1_pair_eq_zero_of_diag h hQ hcon
  apply hQ0
  ext i j
  have hkey := key (Pi.single i (1 : F)) (Pi.single j (1 : F))
  rw [Matrix.mulVec_single_one] at hkey
  have h1 : cq1_pair h (Pi.single i (1 : F)) (Q.col j) = Q i j := by
    rw [cq1_pair]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.col_apply, Pi.single]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h1] at hkey
  simpa using hkey

@[expose] noncomputable def orbitDual {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (B : Matrix (Fin n) (Fin n) F) (u : Fin n → F) :
    Matrix (Fin 3) (Fin n) F :=
  (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u)⁻¹ * ((orbitMatrix B u).map h.bar)ᵀ

@[expose] noncomputable def orbitComplement {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (B : Matrix (Fin n) (Fin n) F) (u : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  1 - orbitMatrix B u * orbitDual h B u

theorem orbitDual_mul_orbitMatrix {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (B : Matrix (Fin n) (Fin n) F) {u : Fin n → F}
    (hdet : IsUnit (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u).det) :
    orbitDual h B u * orbitMatrix B u = 1 := by
  rw [orbitDual, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

theorem orbitDual_mul_self {ℓ f n : ℕ} {F : Type*} [Field F] (h : UnitaryFieldData ℓ f F)
    {B : Matrix (Fin n) (Fin n) F} (hB : (B.map h.bar)ᵀ * B = 1) {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hc : ∀ x : F, x ^ 3 ≠ c)
    {u : Fin n → F} (hdet : IsUnit (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u).det) :
    orbitDual h B u * B = cubicCompanion c * orbitDual h B u := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc 0 (by simp)
  have hBU : (B.map h.bar)ᵀ * orbitMatrix B u =
      orbitMatrix B u * (c⁻¹ • cubicCompanion c ^ 2) :=
    conjTranspose_mul_orbitMatrix h hB hB3 hc0 u
  have hCG : ((cubicCompanion c).map h.bar)ᵀ *
      (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u) * cubicCompanion c =
      ((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u :=
    cq1_cubicCompanion_gram h hB (mul_orbitMatrix hB3 u)
  have hDadjCadj : (((c⁻¹ • cubicCompanion c ^ 2).map h.bar)ᵀ) *
      ((cubicCompanion c).map h.bar)ᵀ = 1 := by
    calc (((c⁻¹ • cubicCompanion c ^ 2).map h.bar)ᵀ) * ((cubicCompanion c).map h.bar)ᵀ
        = ((cubicCompanion c * (c⁻¹ • cubicCompanion c ^ 2)).map h.bar)ᵀ :=
          (cq1_adj_mul h (cubicCompanion c) (c⁻¹ • cubicCompanion c ^ 2)).symm
      _ = 1 := by rw [cq1_cubicCompanion_mul_inv_sq c hc0]; simp
  have hcore := cq1_orbitDual_core h
    (G := ((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u)
    (U := orbitMatrix B u) (C := cubicCompanion c) (D := c⁻¹ • cubicCompanion c ^ 2)
    hBU hCG hDadjCadj hdet
  simpa only [orbitDual] using hcore

theorem isHermitian_orbitMatrix_mul_orbitDual {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (B : Matrix (Fin n) (Fin n) F) {u : Fin n → F}
    (hdet : IsUnit (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u).det) :
    ((orbitMatrix B u * orbitDual h B u).map h.bar)ᵀ = orbitMatrix B u * orbitDual h B u := by
  rw [orbitDual]
  exact cq1_hermitian_core h (cq1_gram_adj h (orbitMatrix B u)) hdet

private theorem cq1_orbitComplement_core (h : UnitaryFieldData ℓ f F)
    {U : Matrix (Fin n) (Fin 3) F} {V : Matrix (Fin 3) (Fin n) F}
    {B : Matrix (Fin n) (Fin n) F} {C : Matrix (Fin 3) (Fin 3) F}
    (hVU : V * U = 1) (hBU : B * U = U * C) (hVB : V * B = C * V)
    (hP : ((U * V).map h.bar)ᵀ = U * V) (hn : 3 < n) :
    (((1 - U * V).map h.bar)ᵀ = 1 - U * V) ∧
      ((1 - U * V) * (1 - U * V) = 1 - U * V) ∧
      (B * (1 - U * V) = (1 - U * V) * B) ∧
      ((1 - U * V) * U = 0) ∧
      (V * (1 - U * V) = 0) ∧ (1 - U * V) ≠ 0 := by
  have hPP : (U * V) * (U * V) = U * V := by
    calc (U * V) * (U * V) = U * (V * (U * V)) := Matrix.mul_assoc U V (U * V)
      _ = U * ((V * U) * V) := by rw [← Matrix.mul_assoc V U V]
      _ = U * ((1 : Matrix (Fin 3) (Fin 3) F) * V) := by rw [hVU]
      _ = U * V := by rw [Matrix.one_mul]
  have hBUV : B * (U * V) = (U * V) * B := by
    calc B * (U * V) = (B * U) * V := (Matrix.mul_assoc _ _ _).symm
      _ = (U * C) * V := by rw [hBU]
      _ = U * (C * V) := Matrix.mul_assoc _ _ _
      _ = U * (V * B) := by rw [hVB]
      _ = (U * V) * B := (Matrix.mul_assoc _ _ _).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cq1_adj_sub h, Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar), hP]
    ext i j
    simp [Matrix.one_apply]
  · rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
    rw [hPP]
    abel
  · rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hBUV]
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hVU, Matrix.mul_one, sub_self]
  · rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hVU, Matrix.one_mul, sub_self]
  · intro h0
    have hUV1 : (1 : Matrix (Fin n) (Fin n) F) = U * V := sub_eq_zero.mp h0
    have h1 : (1 : Matrix (Fin n) (Fin n) F).rank ≤ 3 := by
      rw [hUV1]
      calc (U * V).rank ≤ U.rank := Matrix.rank_mul_le_left U V
        _ ≤ 3 := Matrix.rank_le_width U
    rw [Matrix.rank_one, Fintype.card_fin] at h1
    omega

theorem orbitComplement_facts {ℓ f n : ℕ} {F : Type*} [Field F] (h : UnitaryFieldData ℓ f F)
    (hn : 3 < n) {B : Matrix (Fin n) (Fin n) F} (hB : (B.map h.bar)ᵀ * B = 1) {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (hc : ∀ x : F, x ^ 3 ≠ c)
    {u : Fin n → F} (hdet : IsUnit (((orbitMatrix B u).map h.bar)ᵀ * orbitMatrix B u).det) :
    ((orbitComplement h B u).map h.bar)ᵀ = orbitComplement h B u ∧
      orbitComplement h B u * orbitComplement h B u = orbitComplement h B u ∧
      B * orbitComplement h B u = orbitComplement h B u * B ∧
      orbitComplement h B u * orbitMatrix B u = 0 ∧
      orbitDual h B u * orbitComplement h B u = 0 ∧ orbitComplement h B u ≠ 0 := by
  rw [orbitComplement]
  exact cq1_orbitComplement_core h (orbitDual_mul_orbitMatrix h B hdet)
    (mul_orbitMatrix hB3 u) (orbitDual_mul_self h hB hB3 hc hdet)
    (isHermitian_orbitMatrix_mul_orbitDual h B hdet) hn

private theorem cq1_pow_mul_of_commute {B Q : Matrix (Fin n) (Fin n) F}
    (hcomm : B * Q = Q * B) : ∀ m : ℕ, B ^ m * Q = Q * B ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      calc B ^ (m + 1) * Q = (B * B ^ m) * Q := by rw [pow_succ']
        _ = B * (B ^ m * Q) := Matrix.mul_assoc _ _ _
        _ = B * (Q * B ^ m) := by rw [ih]
        _ = (B * Q) * B ^ m := (Matrix.mul_assoc _ _ _).symm
        _ = (Q * B) * B ^ m := by rw [hcomm]
        _ = Q * (B * B ^ m) := Matrix.mul_assoc _ _ _
        _ = Q * B ^ (m + 1) := by rw [pow_succ']

private theorem cq1_orbitMatrix_mulVec_of_commute {B Q : Matrix (Fin n) (Fin n) F}
    (hcomm : B * Q = Q * B) (x : Fin n → F) :
    orbitMatrix B (Q *ᵥ x) = Q * orbitMatrix B x := by
  have hpow := cq1_pow_mul_of_commute hcomm
  ext k i
  change ((B ^ (i : ℕ)) *ᵥ (Q *ᵥ x)) k = (Q * orbitMatrix B x) k i
  rw [Matrix.mulVec_mulVec]
  rw [show (Q * orbitMatrix B x) k i = (Q *ᵥ ((B ^ (i : ℕ)) *ᵥ x)) k by
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, orbitMatrix, Matrix.of_apply]]
  rw [Matrix.mulVec_mulVec, hpow i]

private theorem cq1_norm_single_ne_zero (h : UnitaryFieldData ℓ f F) (i : Fin n) :
    ∑ k, h.bar ((Pi.single i (1 : F) : Fin n → F) k) * (Pi.single i (1 : F) : Fin n → F) k ≠
      0 := by
  have h1 : cq1_pair h (Pi.single i (1 : F)) (Pi.single i (1 : F)) = 1 := by
    rw [cq1_pair]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [show ∑ k, h.bar ((Pi.single i (1 : F) : Fin n → F) k) *
        (Pi.single i (1 : F) : Fin n → F) k
        = cq1_pair h (Pi.single i (1 : F)) (Pi.single i (1 : F)) from rfl, h1]
  exact one_ne_zero

private theorem cq1_norm_complement_ne_zero (h : UnitaryFieldData ℓ f F)
    {Q : Matrix (Fin n) (Fin n) F} (hQ : (Q.map h.bar)ᵀ = Q) (hQ2 : Q * Q = Q)
    {x : Fin n → F} (hx : ∑ k, h.bar (x k) * (Q *ᵥ x) k ≠ 0) :
    ∑ k, h.bar ((Q *ᵥ x) k) * (Q *ᵥ x) k ≠ 0 := by
  have h1 : cq1_pair h (Q *ᵥ x) (Q *ᵥ x) = cq1_pair h x (Q *ᵥ x) := by
    rw [cq1_pair_adj h Q x (Q *ᵥ x), hQ]
    rw [Matrix.mulVec_mulVec, hQ2]
  rw [show ∑ k, h.bar ((Q *ᵥ x) k) * (Q *ᵥ x) k = cq1_pair h (Q *ᵥ x) (Q *ᵥ x)
        from rfl, h1]
  exact hx

theorem exists_blockFrame_of_unitary_nonCube {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 6 ≤ n) {B : Matrix (Fin n) (Fin n) F}
    (hB : (B.map h.bar)ᵀ * B = 1) {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ (U₁ U₂ : Matrix (Fin n) (Fin 3) F) (V₁ V₂ : Matrix (Fin 3) (Fin n) F),
      BlockFrame B (cubicCompanion c) U₁ U₂ V₁ V₂ ∧
        ((U₁ * V₁).map h.bar)ᵀ = U₁ * V₁ ∧ ((U₂ * V₂).map h.bar)ᵀ = U₂ * V₂ := by
  classical
  have hn3 : 3 < n := by omega
  have hn0 : 0 < n := by omega
  let u₁ : Fin n → F := Pi.single ⟨0, hn0⟩ (1 : F)
  have hu₁ : ∑ k, h.bar (u₁ k) * u₁ k ≠ 0 :=
    cq1_norm_single_ne_zero h ⟨0, hn0⟩
  have hdet₁ : IsUnit (((orbitMatrix B u₁).map h.bar)ᵀ * orbitMatrix B u₁).det :=
    isUnit_det_gram_orbitMatrix h hB hB3 hc hu₁
  let Q : Matrix (Fin n) (Fin n) F := orbitComplement h B u₁
  obtain ⟨hQherm0, hQidem0, hQB0, hQU₁0, hV₁Q0, hQne0⟩ :=
    orbitComplement_facts h hn3 hB hB3 hc hdet₁
  have hQherm : (Q.map h.bar)ᵀ = Q := hQherm0
  have hQidem : Q * Q = Q := hQidem0
  have hQB : B * Q = Q * B := hQB0
  have hQU₁ : Q * orbitMatrix B u₁ = 0 := hQU₁0
  have hV₁Q : orbitDual h B u₁ * Q = 0 := hV₁Q0
  have hQne : Q ≠ 0 := hQne0
  obtain ⟨x, hx⟩ := exists_sum_bar_mul_ne_zero_of_isHermitian h hQherm hQne
  let u₂ : Fin n → F := Q *ᵥ x
  have hu₂ : ∑ k, h.bar (u₂ k) * u₂ k ≠ 0 := cq1_norm_complement_ne_zero h hQherm hQidem hx
  have hdet₂ : IsUnit (((orbitMatrix B u₂).map h.bar)ᵀ * orbitMatrix B u₂).det :=
    isUnit_det_gram_orbitMatrix h hB hB3 hc hu₂
  let W : Matrix (Fin n) (Fin 3) F := orbitMatrix B x
  have hU₂ : orbitMatrix B u₂ = Q * W := by
    change orbitMatrix B (Q *ᵥ x) = Q * orbitMatrix B x
    exact cq1_orbitMatrix_mulVec_of_commute hQB x
  have hU₂adj : ((orbitMatrix B u₂).map h.bar)ᵀ = (W.map h.bar)ᵀ * Q := by
    rw [hU₂, cq1_adj_mul h Q W, hQherm]
  have hV₁U₂ : orbitDual h B u₁ * orbitMatrix B u₂ = 0 := by
    rw [hU₂, ← Matrix.mul_assoc, hV₁Q, Matrix.zero_mul]
  have hV₂U₁ : orbitDual h B u₂ * orbitMatrix B u₁ = 0 := by
    rw [orbitDual, hU₂adj, ← Matrix.mul_assoc, Matrix.mul_assoc, hQU₁, Matrix.mul_zero]
  refine ⟨orbitMatrix B u₁, orbitMatrix B u₂, orbitDual h B u₁, orbitDual h B u₂,
    ?_, ?_, ?_⟩
  · exact ⟨orbitDual_mul_orbitMatrix h B hdet₁, orbitDual_mul_orbitMatrix h B hdet₂,
      hV₁U₂, hV₂U₁, mul_orbitMatrix hB3 u₁, mul_orbitMatrix hB3 u₂,
      orbitDual_mul_self h hB hB3 hc hdet₁, orbitDual_mul_self h hB hB3 hc hdet₂⟩
  · exact isHermitian_orbitMatrix_mul_orbitDual h B hdet₁
  · exact isHermitian_orbitMatrix_mul_orbitDual h B hdet₂

theorem exists_isOrthogonalFrame_of_unitary_nonCube {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 6 ≤ n) {B : Matrix (Fin n) (Fin n) F}
    (hB : (B.map h.bar)ᵀ * B = 1) {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ P₁ P₂ S : Matrix (Fin n) (Fin n) F, IsOrthogonalFrame B P₁ P₂ S ∧
      (P₁.map h.bar)ᵀ = P₁ ∧ (P₂.map h.bar)ᵀ = P₂ := by
  obtain ⟨U₁, U₂, V₁, V₂, hF, h₁, h₂⟩ := exists_blockFrame_of_unitary_nonCube h hn hB hB3 hc
  exact ⟨_, _, _, hF.isOrthogonalFrame, h₁, h₂⟩

end CFSG.StandardType.FF81.CatQ1
