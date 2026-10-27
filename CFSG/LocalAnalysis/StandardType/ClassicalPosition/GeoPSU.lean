module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoDualPair

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private def gPSU_h {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) : F :=
  dotProduct (Matrix.vecMul (fun i => σ (x i)) G) y

private lemma gPSU_h_add_left {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (x x' y : Fin n → F) :
    gPSU_h σ G (x + x') y = gPSU_h σ G x y + gPSU_h σ G x' y := by
  have hv : (fun i => σ ((x + x') i)) =
      (fun i => σ (x i)) + (fun i => σ (x' i)) := by
    funext i
    simp
  simp only [gPSU_h, hv, Matrix.add_vecMul, add_dotProduct]

private lemma gPSU_h_add_right {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (x y y' : Fin n → F) :
    gPSU_h σ G x (y + y') = gPSU_h σ G x y + gPSU_h σ G x y' := by
  simp only [gPSU_h, dotProduct_add]

private lemma gPSU_h_smul_left {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (a : F) (x y : Fin n → F) :
    gPSU_h σ G (a • x) y = σ a * gPSU_h σ G x y := by
  have hv : (fun i => σ ((a • x) i)) = σ a • (fun i => σ (x i)) := by
    funext i
    simp
  simp only [gPSU_h, hv, Matrix.smul_vecMul, smul_dotProduct, smul_eq_mul]

private lemma gPSU_h_smul_right {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (a : F) (x y : Fin n → F) :
    gPSU_h σ G x (a • y) = a * gPSU_h σ G x y := by
  simp only [gPSU_h, dotProduct_smul, smul_eq_mul]

private lemma gPSU_h_antidiag_apply {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (x y : Fin n → F) :
    gPSU_h σ (Unitary.antidiag n) x y =
      ∑ i, σ (x i) * y (Fin.rev i) := by
  simp only [gPSU_h, Matrix.vecMul, dotProduct, Unitary.antidiag, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private lemma gPSU_h_herm {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) (x y : Fin n → F) :
    gPSU_h σ (Unitary.antidiag n) y x = σ (gPSU_h σ (Unitary.antidiag n) x y) := by
  let e : Fin n ≃ Fin n :=
    ⟨Fin.rev, Fin.rev, fun i => by simp, fun i => by simp⟩
  calc gPSU_h σ (Unitary.antidiag n) y x
      = ∑ i, σ (y i) * x (Fin.rev i) := gPSU_h_antidiag_apply σ y x
    _ = ∑ i, σ (y (e i)) * x (Fin.rev (e i)) := by
          rw [← Equiv.sum_comp e (fun i => σ (y i) * x (Fin.rev i))]
    _ = ∑ i, x i * σ (y (Fin.rev i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [e]
          rw [Fin.rev_rev, mul_comm]
    _ = σ (∑ i, σ (x i) * y (Fin.rev i)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_mul, hσ, mul_comm]
    _ = σ (gPSU_h σ (Unitary.antidiag n) x y) := by
          rw [gPSU_h_antidiag_apply]

private lemma gPSU_isometry_of_mem {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) {S : Set (GL (Fin n) F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G *
      (s : Matrix (Fin n) (Fin n) F) = G) {s : GL (Fin n) F} (hs : s ∈ S)
    (x y : Fin n → F) :
    gPSU_h σ G (Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) x)
      (Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) y) = gPSU_h σ G x y := by
  have hm : (fun i => σ (Matrix.mulVec (s : Matrix (Fin n) (Fin n) F) x i)) =
      Matrix.mulVec ((s : Matrix (Fin n) (Fin n) F).map σ) (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ (s : Matrix (Fin n) (Fin n) F) x i
  simp only [gPSU_h, hm]
  rw [Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hSU s hs, Matrix.dotProduct_mulVec]

private lemma gPSU_h_adjoint {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G a : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det) (x y : Fin n → F) :
    gPSU_h σ G (Matrix.mulVec a x) y =
      gPSU_h σ G x (Matrix.mulVec (formAdj σ G a) y) := by
  have hm : (fun i => σ (Matrix.mulVec a x i)) =
      Matrix.mulVec (a.map σ) (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ a x i
  have hmat : Matrix.transpose (a.map σ) * G = G * formAdj σ G a := by
    calc Matrix.transpose (a.map σ) * G = 1 * (Matrix.transpose (a.map σ) * G) :=
          (Matrix.one_mul _).symm
      _ = (G * G⁻¹) * (Matrix.transpose (a.map σ) * G) := by
            rw [Matrix.mul_nonsing_inv G hG]
      _ = G * (G⁻¹ * Matrix.transpose (a.map σ) * G) := by simp only [Matrix.mul_assoc]
      _ = G * formAdj σ G a := rfl
  have hR : dotProduct (Matrix.vecMul (fun i => σ (x i)) G)
      (Matrix.mulVec (formAdj σ G a) y) =
      dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec (formAdj σ G a) y)) := by
    rw [← Matrix.dotProduct_mulVec]
  simp only [gPSU_h, hm]
  rw [Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec, hR, Matrix.mulVec_mulVec, ← hmat]

private lemma gPSU_conjTr_mul_eq_of_forall {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (S M : Matrix (Fin n) (Fin n) F)
    (h : ∀ u v : Fin n → F, dotProduct (fun i => σ (Matrix.mulVec M u i))
      (Matrix.mulVec S (Matrix.mulVec M v)) =
      dotProduct (fun i => σ (u i)) (Matrix.mulVec S v)) :
    Matrix.transpose (M.map σ) * S * M = S := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have e : (fun k => σ ((Pi.single i (1 : F) : Fin n → F) k)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  have hL : dotProduct (fun k => σ (Matrix.mulVec M (Pi.single i 1) k))
      (Matrix.mulVec S (Matrix.mulVec M (Pi.single j 1))) =
      (Matrix.transpose (M.map σ) * S * M) i j := by
    rw [Matrix.mulVec_single_one M i, Matrix.mulVec_single_one M j, Matrix.mul_assoc,
      Matrix.mul_apply]
    simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Matrix.col]
  rw [hL, e, single_dotProduct, one_mul, Matrix.mulVec_single_one] at h1
  exact h1

end CFSG.StandardType.ClassicalPosition
