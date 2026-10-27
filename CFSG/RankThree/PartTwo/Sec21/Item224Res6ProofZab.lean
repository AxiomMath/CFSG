module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUModel

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K) {n : ℕ}

variable (f) in
@[expose] noncomputable def zMat (ω : K) (c d : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  (1 + ω ^ 2 • vecMulVec c (unitaryInvolution K 2 f ∘ d)) *
    (1 + ω • vecMulVec d (unitaryInvolution K 2 f ∘ c))

theorem dilMat_mulVec (a : K) (x y v : Fin n → K) :
    (1 + a • vecMulVec x (unitaryInvolution K 2 f ∘ y)) *ᵥ v = v + (a * (uF h n).β y v) • x := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  rfl

theorem zMat_mulVec (ω : K) {c d : Fin n → K} (hdd : (uF h n).β d d = 0) (v : Fin n → K) :
    zMat f ω c d *ᵥ v = v + (ω ^ 2 * (uF h n).β d v) • c + (ω * (uF h n).β c v) • d := by
  rw [zMat, ← Matrix.mulVec_mulVec, dilMat_mulVec h, dilMat_mulVec h, (uF h n).add_right,
    (uF h n).smul_right, hdd, mul_zero, add_zero]
  abel

theorem uF_swap_one {c d : Fin n → K} (hcd : (uF h n).β c d = 1) : (uF h n).β d c = 1 := by
  rw [uF_symm, hcd, map_one]

theorem zMat_det {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {c d : Fin n → K}
    (hcd : (uF h n).β c d = 1) : (zMat f ω c d).det = 1 := by
  have hdc := uF_swap_one h hcd
  have e1 : ∀ (a : K) (x y : Fin n → K),
      (1 + a • vecMulVec x (unitaryInvolution K 2 f ∘ y)).det = 1 + a * (uF h n).β y x := by
    intro a x y
    rw [← Matrix.vecMulVec_smul, Matrix.vecMulVec_eq (Fin 1),
      Matrix.det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, smul_eq_mul]
    rfl
  rw [zMat, Matrix.det_mul, e1, e1, hdc, hcd]
  linear_combination ω * hω

theorem zMat_isometry {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hσω : (uF h n).σ ω = ω)
    {c d : Fin n → K} (hcc : (uF h n).β c c = 0) (hdd : (uF h n).β d d = 0)
    (hcd : (uF h n).β c d = 1) (u v : Fin n → K) :
    (uF h n).β (zMat f ω c d *ᵥ u) (zMat f ω c d *ᵥ v) = (uF h n).β u v := by
  have hdc := uF_swap_one h hcd
  have hdu : (uF h n).σ ((uF h n).β d u) = (uF h n).β u d := (uF_symm h d u).symm
  have hcu : (uF h n).σ ((uF h n).β c u) = (uF h n).β u c := (uF_symm h c u).symm
  rw [zMat_mulVec h ω hdd, zMat_mulVec h ω hdd]
  simp only [(uF h n).add_left, (uF h n).add_right, (uF h n).smul_left, (uF h n).smul_right,
    map_mul, map_pow, hσω, hdu, hcu, hcc, hdd, hcd, hdc]
  linear_combination ((uF h n).β u c * (uF h n).β d v + (uF h n).β u d * (uF h n).β c v) * ω * hω

theorem zMat_pow_three {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {c d : Fin n → K}
    (hcc : (uF h n).β c c = 0) (hdd : (uF h n).β d d = 0) (hcd : (uF h n).β c d = 1) :
    zMat f ω c d ^ 3 = 1 := by
  have hdc := uF_swap_one h hcd
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : ∀ w, zMat f ω c d *ᵥ w =
      w + (ω ^ 2 * (uF h n).β d w) • c + (ω * (uF h n).β c w) • d := zMat_mulVec h ω hdd
  have hd : ∀ w, (uF h n).β d (zMat f ω c d *ᵥ w) = ω * (uF h n).β d w := by
    intro w
    rw [e, (uF h n).add_right, (uF h n).add_right, (uF h n).smul_right,
      (uF h n).smul_right, hdc, hdd]
    linear_combination (uF h n).β d w * hω - (uF h n).β d w * ω * h2
  have hc : ∀ w, (uF h n).β c (zMat f ω c d *ᵥ w) = ω ^ 2 * (uF h n).β c w := by
    intro w
    rw [e, (uF h n).add_right, (uF h n).add_right, (uF h n).smul_right,
      (uF h n).smul_right, hcc, hcd]
    linear_combination (uF h n).β c w * hω - (uF h n).β c w * ω ^ 2 * h2
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, pow_succ, pow_succ, pow_one,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e3 : zMat f ω c d *ᵥ (zMat f ω c d *ᵥ (zMat f ω c d *ᵥ v)) = v +
      (ω ^ 2 * (uF h n).β d v + ω ^ 2 * (ω * (uF h n).β d v) +
        ω ^ 2 * (ω * (ω * (uF h n).β d v))) • c +
      (ω * (uF h n).β c v + ω * (ω ^ 2 * (uF h n).β c v) +
        ω * (ω ^ 2 * (ω ^ 2 * (uF h n).β c v))) • d := by
    rw [e (zMat f ω c d *ᵥ (zMat f ω c d *ᵥ v)), hd, hd, hc, hc, e (zMat f ω c d *ᵥ v), hd, hc,
      e v]
    module
  rw [e3, show ω ^ 2 * (uF h n).β d v + ω ^ 2 * (ω * (uF h n).β d v) +
      ω ^ 2 * (ω * (ω * (uF h n).β d v)) = 0 by linear_combination (uF h n).β d v * ω ^ 2 * hω,
    show ω * (uF h n).β c v + ω * (ω ^ 2 * (uF h n).β c v) +
      ω * (ω ^ 2 * (ω ^ 2 * (uF h n).β c v)) = 0 by
        linear_combination (uF h n).β c v * ω * (ω ^ 2 - ω + 1) * hω,
    zero_smul, zero_smul, add_zero, add_zero]

theorem zMat_comm (ω : K) {c d : Fin n → K} (hdd : (uF h n).β d d = 0)
    {X : Matrix (Fin n) (Fin n) K} (hX : ∀ u v, (uF h n).β (X *ᵥ u) (X *ᵥ v) = (uF h n).β u v)
    {l m : K} (hXc : X *ᵥ c = l • c) (hXd : X *ᵥ d = m • d) (hlm : (uF h n).σ l * m = 1)
    (hml : (uF h n).σ m * l = 1) : X * zMat f ω c d = zMat f ω c d * X := by
  have hd : ∀ v, (uF h n).β d (X *ᵥ v) = l * (uF h n).β d v := by
    intro v
    have h1 := hX d v
    rw [hXd, (uF h n).smul_left] at h1
    calc (uF h n).β d (X *ᵥ v) = ((uF h n).σ m * l) * (uF h n).β d (X *ᵥ v) := by
          rw [hml, one_mul]
      _ = l * ((uF h n).σ m * (uF h n).β d (X *ᵥ v)) := by ring
      _ = l * (uF h n).β d v := by rw [h1]
  have hc : ∀ v, (uF h n).β c (X *ᵥ v) = m * (uF h n).β c v := by
    intro v
    have h1 := hX c v
    rw [hXc, (uF h n).smul_left] at h1
    calc (uF h n).β c (X *ᵥ v) = ((uF h n).σ l * m) * (uF h n).β c (X *ᵥ v) := by
          rw [hlm, one_mul]
      _ = m * ((uF h n).σ l * (uF h n).β c (X *ᵥ v)) := by ring
      _ = m * (uF h n).β c v := by rw [h1]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    zMat_mulVec h ω hdd, zMat_mulVec h ω hdd, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hXc, hXd, hd, hc]
  module

@[expose] noncomputable def zGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {c d : Fin n → K}
    (hcd : (uF h n).β c d = 1) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (zMat f ω c d)
    (by rw [zMat_det h hω hcd]; exact one_ne_zero)

theorem coe_zGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {c d : Fin n → K}
    (hcd : (uF h n).β c d = 1) :
    ((zGL h hω hcd : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = zMat f ω c d :=
  rfl

theorem zGL_mem {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hσω : (uF h n).σ ω = ω) {c d : Fin n → K}
    (hcc : (uF h n).β c c = 0) (hdd : (uF h n).β d d = 0) (hcd : (uF h n).β c d = 1) :
    zGL h hω hcd ∈ uS h n := by
  refine ⟨?_, zMat_det h hω hcd⟩
  have h1 := (unitaryForm_preserves_iff (card_sq_of_unitary h) _).mp
    (zMat_isometry h hω hσω hcc hdd hcd)
  rw [← map_bar_eq_map_σ h] at h1
  change ((zMat f ω c d).map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix _ _ K) * zMat f ω c d =
    ((1 : GL (Fin n) K) : Matrix _ _ K)
  rw [Units.val_one, Matrix.mul_one, h1]

theorem zGL_pow_three {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {c d : Fin n → K}
    (hcc : (uF h n).β c c = 0) (hdd : (uF h n).β d d = 0) (hcd : (uF h n).β c d = 1) :
    zGL h hω hcd ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_zGL, zMat_pow_three h hω hcc hdd hcd, Units.val_one]

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
