module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtN4
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Refl
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem zs4f_isUnit_det_of_mul_self {n : ℕ} {K : Type} [Field K]
    (M : Matrix (Fin n) (Fin n) K) (h : M * M = 1) : IsUnit M.det :=
  isUnit_iff_exists.mpr ⟨M.det, by rw [← Matrix.det_mul, h, Matrix.det_one],
    by rw [← Matrix.det_mul, h, Matrix.det_one]⟩

section ZS4fCert
variable {K : Type} [Field K]

private def ctK (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, t, 0, 0; -t, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem pijMat01t_eqK {t : K} (ht : t ^ 2 = -1) :
    pijMat 0 1 t = ctK t := by
  have htt : t * t = -1 := by rw [← pow_two, ht]
  have htinv : t⁻¹ = -t := by
    have h : t * (-t) = 1 := by
      calc t * (-t) = -(t * t) := mul_neg t t
        _ = -(-1) := by rw [htt]
        _ = 1 := neg_neg 1
    exact inv_eq_of_mul_eq_one_right h
  ext i j; fin_cases i <;> fin_cases j <;> simp [pijMat, ctK, htinv]

private def n4PK1 : Matrix (Fin 4) (Fin 4) K :=
  !![(1 : K), 0, 0, 0; 0, 0, (1 : K), 0; 0, (1 : K), 0, 0; 0, 0, 0, (1 : K)]

private def n4PK2 : Matrix (Fin 4) (Fin 4) K :=
  !![0, (1 : K), 0, 0; 0, 0, (1 : K), 0; (1 : K), 0, 0, 0; 0, 0, 0, (1 : K)]

private def n4PK3 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![(-1 : K) * t, 0, 0, 0; 0, 0, (1 : K), 0; 0, (1 : K) * t, 0, 0; 0, 0, 0, (1 : K)]

private def n4PK4 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, (-1 : K) * t, 0, 0; 0, 0, (1 : K), 0; (1 : K) * t, 0, 0, 0; 0, 0, 0, (1 : K)]

private def n4PK5 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![(1 : K) * t ^ 2, 0, 0, 0; 0, 0, (1 : K), 0; 0, (1 : K) * t ^ 2, 0, 0; 0, 0, 0, (1 : K)]

private def n4PK6 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![(1 : K) * t ^ 2, 0, 0, 0; 0, (1 : K), 0, 0; 0, 0, (1 : K) * t ^ 2, 0; 0, 0, 0, (1 : K)]

private def n4PK7 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹,
          (1 : K) + (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹;
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹,
          (1 : K) + (-1 : K) * (2 : K)⁻¹]

private def n4PK8 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
          (1 : K) * (2 : K)⁻¹ * t ^ 3,
          (1 : K) * t ^ 3 + (-1 : K) * (2 : K)⁻¹ * t ^ 3,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * t + (1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹;
          (1 : K) * (2 : K)⁻¹ * t ^ 3,
          (-1 : K) * (2 : K)⁻¹ * t ^ 3,
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * (2 : K)⁻¹,
          (1 : K) + (-1 : K) * (2 : K)⁻¹]

private def n4PK9 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
          (1 : K) * t ^ 3 + (-1 : K) * (2 : K)⁻¹ * t ^ 3,
          (1 : K) * (2 : K)⁻¹ * t ^ 3,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * t + (1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹;
          (-1 : K) * (2 : K)⁻¹ * t ^ 3,
          (1 : K) * (2 : K)⁻¹ * t ^ 3,
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹ * t,
          (1 : K) * (2 : K)⁻¹ * t,
          (-1 : K) * (2 : K)⁻¹,
          (1 : K) + (-1 : K) * (2 : K)⁻¹]

private def n4PK10 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (1 : K) * t ^ 4 + (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹;
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹,
          (1 : K) + (-1 : K) * (2 : K)⁻¹]

private def n4PK11 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (1 : K) * t ^ 4 + (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹;
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (1 : K) + (-1 : K) * (2 : K)⁻¹]

private def n4PK12 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (1 : K) * t ^ 4 + (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹,
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹;
          (1 : K) * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 4,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2;
          (-1 : K) * (2 : K)⁻¹,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (-1 : K) * (2 : K)⁻¹ * t ^ 2,
          (1 : K) + (-1 : K) * (2 : K)⁻¹]

private def n4PK13 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (1 : K) * t ^ 4 + (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (1 : K) * t ^ 2 + (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2;
     (1 : K) * t ^ 2 + (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
          (-2 : K) * (2 : K)⁻¹ + (2 : K) * (2 : K)⁻¹ ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (1 : K) + (-2 : K) * (2 : K)⁻¹ + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2]

private def n4PK14 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
     (2 : K) * (2 : K)⁻¹ * t ^ 5 + (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (-1 : K) * (2 : K)⁻¹ * t ^ 3 + (-1 : K) * (2 : K)⁻¹ * t ^ 5 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (1 : K) * t ^ 4 + (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (-1 : K) * t ^ 3 + (2 : K) * (2 : K)⁻¹ * t ^ 3 + (-2 : K) * (2 : K)⁻¹ ^ 2 * t +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-1 : K) * (2 : K)⁻¹ * t + (-1 : K) * (2 : K)⁻¹ * t ^ 3 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2;
     (1 : K) * (2 : K)⁻¹ * t ^ 3 + (1 : K) * (2 : K)⁻¹ * t ^ 5 +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 + (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (1 : K) * t ^ 3 + (-2 : K) * (2 : K)⁻¹ * t ^ 3 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (1 : K) * (2 : K)⁻¹ * t + (1 : K) * (2 : K)⁻¹ * t ^ 3 +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t + (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-2 : K) * (2 : K)⁻¹ * t + (2 : K) * (2 : K)⁻¹ ^ 2 * t +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (1 : K) + (-2 : K) * (2 : K)⁻¹ + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2]

private def n4PK15 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
     (-1 : K) * (2 : K)⁻¹ * t ^ 3 + (-1 : K) * (2 : K)⁻¹ * t ^ 5 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (2 : K) * (2 : K)⁻¹ * t ^ 5 + (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (1 : K) * t ^ 4 + (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (-1 : K) * (2 : K)⁻¹ * t + (-1 : K) * (2 : K)⁻¹ * t ^ 3 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-1 : K) * t ^ 3 + (2 : K) * (2 : K)⁻¹ * t ^ 3 + (-2 : K) * (2 : K)⁻¹ ^ 2 * t +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2;
     (1 : K) * t ^ 3 + (-2 : K) * (2 : K)⁻¹ * t ^ 3 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (1 : K) * (2 : K)⁻¹ * t ^ 3 + (1 : K) * (2 : K)⁻¹ * t ^ 5 +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3 + (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 5,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (-2 : K) * (2 : K)⁻¹ * t + (2 : K) * (2 : K)⁻¹ ^ 2 * t +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (1 : K) * (2 : K)⁻¹ * t + (1 : K) * (2 : K)⁻¹ * t ^ 3 +
       (-2 : K) * (2 : K)⁻¹ ^ 2 * t + (-2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 3,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (1 : K) + (-2 : K) * (2 : K)⁻¹ + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2]

private def n4PK16 (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![
     (-2 : K) * (2 : K)⁻¹ * t ^ 6 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 6,
     (-1 : K) * (2 : K)⁻¹ * t ^ 4 + (-1 : K) * (2 : K)⁻¹ * t ^ 6 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 6,
     (1 : K) * t ^ 4 + (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (1 : K) * t ^ 4 + (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2;
     (-1 : K) * (2 : K)⁻¹ * t ^ 4 + (-1 : K) * (2 : K)⁻¹ * t ^ 6 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 6,
     (1 : K) * t ^ 4 + (-2 : K) * (2 : K)⁻¹ * t ^ 4 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 6,
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4;
     (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (-1 : K) * (2 : K)⁻¹ * t ^ 4 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-2 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 4,
     (-1 : K) * (2 : K)⁻¹ + (-1 : K) * (2 : K)⁻¹ * t ^ 2 + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2,
     (1 : K) + (-2 : K) * (2 : K)⁻¹ + (2 : K) * (2 : K)⁻¹ ^ 2 +
       (2 : K) * (2 : K)⁻¹ ^ 2 * t ^ 2]

private theorem n4stepK1 :
    (pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) K) = n4PK1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [n4PK1, pijMat]

private theorem n4stepK2 :
    (n4PK1 : Matrix (Fin 4) (Fin 4) K) * pijMat 0 1 1 = n4PK2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK1, n4PK2]

private theorem n4stepK3 {t : K} (ht : t ^ 2 = -1) :
    n4PK2 * pijMat 0 1 t = n4PK3 t := by
  rw [pijMat01t_eqK ht]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      ctK, n4PK2, n4PK3]

private theorem n4stepK4 {t : K} :
    n4PK3 t * pijMat 0 1 1 = n4PK4 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK3, n4PK4]

private theorem n4stepK5 {t : K} (ht : t ^ 2 = -1) :
    n4PK4 t * pijMat 0 1 t = n4PK5 t := by
  rw [pijMat01t_eqK ht]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      ctK, n4PK4, n4PK5] <;>
    field_simp

private theorem n4stepK6 {t : K} :
    n4PK5 t * pijMat 1 2 1 = n4PK6 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK5, n4PK6]

private theorem n4stepK7 {t : K} (h2 : (2 : K) ≠ 0) :
    n4PK6 t * halfOnesMat 4 = n4PK7 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, halfOnesMat,
      n4PK6, n4PK7] <;>
    field_simp [h2] <;> ring

private theorem n4stepK8 {t : K} (h2 : (2 : K) ≠ 0) (ht : t ^ 2 = -1) :
    n4PK7 t * pijMat 0 1 t = n4PK8 t := by
  rw [pijMat01t_eqK ht]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      ctK, n4PK7, n4PK8] <;>
    field_simp [h2]
  ring

private theorem n4stepK9 {t : K} :
    n4PK8 t * pijMat 0 1 1 = n4PK9 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK8, n4PK9]

private theorem n4stepK10 {t : K} (h2 : (2 : K) ≠ 0) (ht : t ^ 2 = -1) :
    n4PK9 t * pijMat 0 1 t = n4PK10 t := by
  rw [pijMat01t_eqK ht]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      ctK, n4PK9, n4PK10] <;>
    field_simp [h2]
  ring

private theorem n4stepK11 {t : K} :
    n4PK10 t * pijMat 1 2 1 = n4PK11 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK10, n4PK11]

private theorem n4stepK12 {t : K} :
    n4PK11 t * pijMat 0 1 1 = n4PK12 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK11, n4PK12]

private theorem n4stepK13 {t : K} (h2 : (2 : K) ≠ 0) :
    n4PK12 t * halfOnesMat 4 = n4PK13 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, halfOnesMat,
      n4PK12, n4PK13] <;>
    field_simp [h2] <;> ring

private theorem n4stepK14 {t : K} (h2 : (2 : K) ≠ 0) (ht : t ^ 2 = -1) :
    n4PK13 t * pijMat 0 1 t = n4PK14 t := by
  rw [pijMat01t_eqK ht]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      ctK, n4PK13, n4PK14] <;>
    field_simp [h2] <;> ring

private theorem n4stepK15 {t : K} :
    n4PK14 t * pijMat 0 1 1 = n4PK15 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK14, n4PK15]

private theorem n4stepK16 {t : K} (h2 : (2 : K) ≠ 0) (ht : t ^ 2 = -1) :
    n4PK15 t * pijMat 0 1 t = n4PK16 t := by
  rw [pijMat01t_eqK ht]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      ctK, n4PK15, n4PK16] <;>
    field_simp [h2] <;> ring

private theorem n4stepK17 {t : K} (h2 : (2 : K) ≠ 0) (ht : t ^ 2 = -1) :
    n4PK16 t * pijMat 1 2 1 = pijMat 2 3 1 := by
  have ht3 : t ^ 3 = -t := by rw [show t ^ 3 = t * t ^ 2 by ring, ht]; ring
  have ht4 : t ^ 4 = 1 := by rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht]; ring
  have ht5 : t ^ 5 = t := by rw [show t ^ 5 = t * t ^ 4 by ring, ht4]; ring
  have ht6 : t ^ 6 = -1 := by rw [show t ^ 6 = (t ^ 2) ^ 3 by ring, ht]; ring
  have h4 : (4 : K)⁻¹ = (2 : K)⁻¹ ^ 2 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact (inv_pow (2 : K) 2).symm
  generalize hu : (2 : K)⁻¹ = u at *
  have h2u : 2 * u = 1 := by rw [← hu]; exact mul_inv_cancel₀ h2
  have hu2 : u * 2 = 1 := by rw [mul_comm, h2u]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat,
      n4PK16, hu, ht, ht4, ht6, h2u]

private theorem pi34_wordK (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    pijMat 1 2 1 * pijMat 0 1 1 * pijMat 0 1 t * pijMat 0 1 1 * pijMat 0 1 t * pijMat 1 2 1 *
    halfOnesMat 4 * pijMat 0 1 t * pijMat 0 1 1 * pijMat 0 1 t * pijMat 1 2 1 * pijMat 0 1 1 *
    halfOnesMat 4 * pijMat 0 1 t * pijMat 0 1 1 * pijMat 0 1 t * pijMat 1 2 1
    = pijMat 2 3 1 := by
  nth_rewrite 1 [n4stepK1]
  nth_rewrite 1 [n4stepK2]
  nth_rewrite 1 [n4stepK3 ht]
  nth_rewrite 1 [n4stepK4]
  nth_rewrite 1 [n4stepK5 ht]
  nth_rewrite 1 [n4stepK6]
  nth_rewrite 1 [n4stepK7 h2]
  nth_rewrite 1 [n4stepK8 h2 ht]
  nth_rewrite 1 [n4stepK9]
  nth_rewrite 1 [n4stepK10 h2 ht]
  nth_rewrite 1 [n4stepK11]
  nth_rewrite 1 [n4stepK12]
  nth_rewrite 1 [n4stepK13 h2]
  nth_rewrite 1 [n4stepK14 h2 ht]
  nth_rewrite 1 [n4stepK15]
  nth_rewrite 1 [n4stepK16 h2 ht]
  nth_rewrite 1 [n4stepK17 h2 ht]
  rfl

private theorem zs4f_diagSign_three_sq :
    (diagSignMat 3 : Matrix (Fin 4) (Fin 4) K) * diagSignMat 3 = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, diagSignMat]

private theorem zs4f_pij34_diagSign_conj :
    (pijMat 2 3 1 : Matrix (Fin 4) (Fin 4) K) *
        (diagSignMat 3 : Matrix (Fin 4) (Fin 4) K) * pijMat 2 3 1 =
      (diagSignMat 2 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]

private theorem zs4f_pij34_diagSign_conj' :
    (pijMat 2 3 1 : Matrix (Fin 4) (Fin 4) K) *
        (diagSignMat 2 : Matrix (Fin 4) (Fin 4) K) * pijMat 2 3 1 =
      (diagSignMat 3 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]

private theorem zs4f_halfFormMat_vecMulVec (h2 : (2 : K) ≠ 0) {α : K} (hα : α ≠ 0) :
    halfFormMat α =
      1 - Matrix.vecMulVec (fun i : Fin 4 => if i = 3 then -α⁻¹ else 1)
        (fun j : Fin 4 => if j = 3 then -((2 : K)⁻¹ * α) else (2 : K)⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfFormMat, Matrix.vecMulVec_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.of_apply] <;>
    field_simp [h2, hα] <;> ring

private theorem zs4f_halfOnes_vecMulVec :
    halfOnesMat 4 = 1 - Matrix.vecMulVec (fun _ : Fin 4 => (1 : K))
        (fun _ : Fin 4 => (2 : K)⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfOnesMat, Matrix.vecMulVec_apply, Matrix.sub_apply,
      Matrix.of_apply]

private theorem zs4f_pij01_halfOnes (h2 : (2 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) :
    pijMat 0 1 t * halfOnesMat 4 * pijMat 0 1 t =
      1 - Matrix.vecMulVec (fun i : Fin 4 => if i = 0 then t else if i = 1 then t⁻¹ else 1)
        (fun j : Fin 4 =>
          if j = 0 then (2 : K)⁻¹ * t⁻¹ else if j = 1 then (2 : K)⁻¹ * t else (2 : K)⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, halfOnesMat, Matrix.vecMulVec_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply] <;>
    field_simp [h2, ht0]

private theorem zs4f_halfFormMat_ne_cdc (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (α : K) :
    halfFormMat α ≠ pijMat 0 1 t * halfOnesMat 4 * pijMat 0 1 t := by
  intro hmat
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) hmat
  simp [halfFormMat, halfOnesMat, pijMat, Matrix.mul_apply, Fin.sum_univ_four] at h01
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact absurd (show (1 : K) = 0 by linear_combination h01 + (2 : K)⁻¹ * ht - hinv) one_ne_zero

private theorem zs4f_sum_x (h2 : (2 : K) ≠ 0) {α : K} (hα : α ≠ 0) :
    ∑ i : Fin 4, (if i = 3 then -((2 : K)⁻¹ * α) else (2 : K)⁻¹) *
      (if i = 3 then -α⁻¹ else 1) = 2 := by
  simp [Fin.sum_univ_four]
  field_simp [h2, hα]
  ring

private theorem zs4f_sum_d (h2 : (2 : K) ≠ 0) :
    ∑ _ : Fin 4, (2 : K)⁻¹ * (1 : K) = 2 := by
  simp
  field_simp [h2]
  ring

private theorem zs4f_sum_cdc (h2 : (2 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) :
    ∑ i : Fin 4,
      (if i = 0 then (2 : K)⁻¹ * t⁻¹ else if i = 1 then (2 : K)⁻¹ * t else (2 : K)⁻¹) *
      (if i = 0 then t else if i = 1 then t⁻¹ else 1) = 2 := by
  simp [Fin.sum_univ_four]
  field_simp [h2, ht0]
  ring

private theorem zs4f_halfFormMat_sq_33 (h2 : (2 : K) ≠ 0) (α : K) :
    (halfFormMat α * halfFormMat α) 3 3 * 4 = 3 * α⁻¹ * α + 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, halfFormMat, Matrix.of_apply]
  field_simp [h2]
  ring
end ZS4fCert

private lemma zs4f_two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  ZMod.prime_ne_zero p 2 hp

private theorem zs4f_halfOnes_conj (hp : p ≠ 2) :
    halfOnesMat 4 * halfFormMat (1 : ZMod p) * halfOnesMat 4 = diagSignMat 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, halfOnesMat, halfFormMat, diagSignMat,
      Matrix.one_apply] <;>
    field_simp [zs4f_two_ne_zero hp] <;> ring

private theorem zs4f_four_lt_p (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1) : 4 < p := by
  have hsq : IsSquare (-1 : ZMod p) := ⟨t, by rw [← pow_two, ht]⟩
  have hmod : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  omega

private theorem zs4f_three_ne_zero (hp4 : 4 < p) : (3 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h0
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem zs4f_alpha_ne_zero (hp : p ≠ 2) (hp4 : 4 < p) {α : ZMod p}
    (h : halfFormMat α * halfFormMat α = 1) : α ≠ 0 := by
  have h3 : (3 : ZMod p) ≠ 0 := zs4f_three_ne_zero hp4
  have h33 : (halfFormMat α * halfFormMat α) 3 3 = 1 := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod p) => M 3 3) h
    simpa using this
  have h4 := zs4f_halfFormMat_sq_33 (K := ZMod p) (zs4f_two_ne_zero hp) α
  rw [h33, one_mul] at h4
  intro hα
  have hlin : 3 * (α⁻¹ * α) = 3 * 1 := by linear_combination -h4
  have hone : α⁻¹ * α = 1 := mul_left_cancel₀ h3 hlin
  rw [hα, inv_zero, zero_mul] at hone
  exact zero_ne_one hone

private theorem zs4f_mod_four (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1) : p % 4 = 1 := by
  have hsq : IsSquare (-1 : ZMod p) := ⟨t, by rw [← pow_two, ht]⟩
  have hmod : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  omega

private theorem zs4f_four_ne_zero (hp4 : 4 < p) : (4 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h0
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

private lemma zs4f_beta_two (hp4 : 4 < p) (hmod : p % 4 = 1) {S : ZMod p}
    (h1 : (10 - 3 * S) / 4 = 0 ∨ (10 - 3 * S) / 4 = 1 ∨ (10 - 3 * S) / 4 = 2)
    (h2 : (2 - S) / 4 = 2) (hb1 : (10 - 3 * S) / 4 = 7) : p = 5 ∧ S = -6 := by
  have h4 : (4 : ZMod p) ≠ 0 := zs4f_four_ne_zero hp4
  rcases h1 with h1 | h1 | h1
  · exfalso
    have h70 : (7 : ZMod p) = 0 := by rw [← hb1, h1]
    have hdvd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).mp h70
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hp5 : p = 5 := by omega
    rw [hp5] at hdvd
    norm_num at hdvd
  · exfalso
    have h71 : (7 : ZMod p) = 1 := by rw [← hb1, h1]
    have h61 : (6 : ZMod p) = 0 := by linear_combination h71
    have hdvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp h61
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hp5 : p = 5 := by omega
    rw [hp5] at hdvd
    norm_num at hdvd
  · have h72 : (7 : ZMod p) = 2 := by rw [← hb1, h1]
    have h52 : (5 : ZMod p) = 0 := by linear_combination h72
    have hdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h52
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hp5 : p = 5 := by omega
    refine ⟨hp5, ?_⟩
    have h2S : (2 - S) = 8 := by
      have h := congrArg (fun x : ZMod p => x * 4) h2
      rw [div_mul_cancel₀ _ h4] at h
      norm_num at h
      exact h
    linear_combination -h2S

private lemma zs4f_beta_cases (hp : p ≠ 2) (hp4 : 4 < p) (hmod : p % 4 = 1) {S : ZMod p}
    (h1 : (10 - 3 * S) / 4 = 0 ∨ (10 - 3 * S) / 4 = 1 ∨ (10 - 3 * S) / 4 = 2)
    (h2 : (2 - S) / 4 = 0 ∨ (2 - S) / 4 = 1 ∨ (2 - S) / 4 = 2) :
    S = 2 ∨ (p = 5 ∧ S = -6) := by
  have h4 : (4 : ZMod p) ≠ 0 := zs4f_four_ne_zero hp4
  have hrel : (10 - 3 * S) / 4 = 1 + 3 * ((2 - S) / 4) := by
    field_simp [h4]
    ring
  rcases h2 with h2 | h2 | h2
  · left
    have h : (2 - S) = 0 := by
      have := congrArg (fun x : ZMod p => x * 4) h2
      rwa [zero_mul, div_mul_cancel₀ _ h4] at this
    linear_combination -h
  · exfalso
    have hb1 : (10 - 3 * S) / 4 = 4 := by rw [hrel, h2]; ring
    rcases h1 with h1 | h1 | h1
    · exact zs4f_four_ne_zero hp4 (by rw [← hb1, h1])
    · apply zs4f_three_ne_zero hp4
      have h41 : (4 : ZMod p) = 1 := by rw [← hb1, h1]
      linear_combination h41
    · apply zs4f_two_ne_zero hp
      have h42 : (4 : ZMod p) = 2 := by rw [← hb1, h1]
      linear_combination h42
  · exact Or.inr (zs4f_beta_two hp4 hmod h1 h2 (by rw [hrel, h2]; ring))

private lemma zs4f_five_no_root : ∀ β : ZMod 5, β ^ 2 + β + 1 ≠ 0 := by decide

private lemma zs4f_five_five : (5 : ZMod 5) = 0 := by decide

private lemma zs4f_t_inv {t : ZMod p} (ht : t ^ 2 = -1) : t⁻¹ = -t := by
  have h : t * (-t) = 1 := by
    calc t * (-t) = -(t * t) := mul_neg t t
      _ = -(-1) := by rw [← pow_two, ht]
      _ = 1 := neg_neg 1
  exact inv_eq_of_mul_eq_one_right h

private lemma zs4f_t_ne_zero {t : ZMod p} (ht : t ^ 2 = -1) : t ≠ 0 := by
  intro h
  rw [h, pow_two, mul_zero] at ht
  exact zero_ne_one (show (0 : ZMod p) = 1 from (neg_eq_zero.mp ht.symm).symm)

private lemma zs4f_coord_sum_apply {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (κ : Fin m → ZMod p) (i : Fin m) :
    (∑ j, κ j • f.coord j) (f i) = κ i := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    rw [if_neg (fun h : i = j => hij h.symm), mul_zero]
  · intro hi; simp at hi

private lemma zs4f_repr_sum_smul {m : ℕ} (f : Module.Basis (Fin m) (ZMod p) U)
    (ρ : Fin m → ZMod p) (i : Fin m) :
    f.repr (∑ j, ρ j • f j) i = ρ i := by
  have h1 : f.repr (∑ j, ρ j • f j) = ∑ j, Finsupp.single j (ρ j) := by
    simp [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single]
  rw [h1, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij; rw [if_neg hij]
  · intro hi; simp at hi

private theorem zs4f_eq_of_toMatrix_eq {f : Module.Basis (Fin 4) (ZMod p) U}
    {g g' : U ≃ₗ[ZMod p] U}
    (h : LinearMap.toMatrix f f g.toLinearMap = LinearMap.toMatrix f f g'.toLinearMap) :
    g = g' :=
  LinearEquiv.ext (fun v => congrArg (fun m : U →ₗ[ZMod p] U => m v)
    ((LinearMap.toMatrix f f).injective h))

theorem toMatrix_conj_halfFormMat_one (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {d x : U ≃ₗ[ZMod p] U} (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4)
    (hx : LinearMap.toMatrix f f x.toLinearMap = halfFormMat 1) :
    LinearMap.toMatrix f f (d * x * d).toLinearMap = diagSignMat 3 := by
  calc LinearMap.toMatrix f f (d * x * d).toLinearMap
      = LinearMap.toMatrix f f (d.toLinearMap * x.toLinearMap * d.toLinearMap) := by
        rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    _ = LinearMap.toMatrix f f d.toLinearMap * LinearMap.toMatrix f f x.toLinearMap *
          LinearMap.toMatrix f f d.toLinearMap := by
        rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
    _ = diagSignMat 3 := by rw [hd, hx]; exact zs4f_halfOnes_conj hp

theorem mem_weylN4_of_toMatrix_pij (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t ^ 2 = -1) {g : U ≃ₗ[ZMod p] U}
    (hg : LinearMap.toMatrix f f g.toLinearMap = pijMat 2 3 1) :
    g ∈ basisClosure f (weylN4Mats t) := by
  have hdet1 : IsUnit (pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat])
  have hdet2 : IsUnit (pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat])
  have ht0 : t ≠ 0 := by
    intro h
    have hh := ht
    rw [h, pow_two, mul_zero] at hh
    exact zero_ne_one (show (0 : ZMod p) = 1 from (neg_eq_zero.mp hh.symm).symm)
  have hdet3 : IsUnit (pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, ht0])
  have hdet4 : IsUnit (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, halfOnesMat, Matrix.one_apply] <;>
        field_simp [zs4f_two_ne_zero hp] <;> ring)
  obtain ⟨A, hAcl, hA⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylN4Mats t)
    (M := pijMat 0 1 1) (by simp [weylN4Mats]) hdet1
  obtain ⟨B, hBcl, hB⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylN4Mats t)
    (M := pijMat 1 2 1) (by simp [weylN4Mats]) hdet2
  obtain ⟨C, hCcl, hC⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylN4Mats t)
    (M := pijMat 0 1 t) (by simp [weylN4Mats]) hdet3
  obtain ⟨D, hDcl, hD⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylN4Mats t)
    (M := halfOnesMat 4) (by simp [weylN4Mats]) hdet4
  have hWcl : B * A * C * A * C * B * D * C * A * C * B * A * D * C * A * C * B ∈
      basisClosure f (weylN4Mats t) := by
    repeat' apply Subgroup.mul_mem
    all_goals assumption
  have hWmat : LinearMap.toMatrix f f
      (B * A * C * A * C * B * D * C * A * C * B * A * D * C * A * C * B).toLinearMap =
      pijMat 2 3 1 := by
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hA, hB, hC, hD]
    exact pi34_wordK (zs4f_two_ne_zero hp) ht
  have hWlin : (B * A * C * A * C * B * D * C * A * C * B * A * D * C * A * C * B).toLinearMap
      = g.toLinearMap :=
    (LinearMap.toMatrix f f).injective (hWmat.trans hg.symm)
  have hWg : B * A * C * A * C * B * D * C * A * C * B * A * D * C * A * C * B = g :=
    LinearEquiv.ext (fun v => congrArg (fun m : U →ₗ[ZMod p] U => m v) hWlin)
  rwa [hWg] at hWcl

private theorem zs4f_pi34_mem (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t ^ 2 = -1) :
    ∃ P ∈ basisClosure f (weylN4Mats t), LinearMap.toMatrix f f P.toLinearMap = pijMat 2 3 1 := by
  have hdet : IsUnit (pijMat 2 3 1 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat])
  refine ⟨LinearEquiv.ofIsUnitDet (v := f) (v' := f) (f := Matrix.toLin f f (pijMat 2 3 1))
      (by rw [LinearMap.toMatrix_toLin]; exact hdet), ?_, ?_⟩
  · apply mem_weylN4_of_toMatrix_pij hp f ht
    rw [LinearEquiv.coe_ofIsUnitDet, LinearMap.toMatrix_toLin]
  · rw [LinearEquiv.coe_ofIsUnitDet, LinearMap.toMatrix_toLin]

theorem mem_weylEN4_of_toMatrix_diagSign (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t ^ 2 = -1) {g : U ≃ₗ[ZMod p] U}
    (hg : LinearMap.toMatrix f f g.toLinearMap = diagSignMat 2) :
    g ∈ basisClosure f (weylEN4Mats t) := by
  obtain ⟨P, hPcl, hP⟩ := zs4f_pi34_mem hp f ht
  have hsub : {x : U ≃ₗ[ZMod p] U | LinearMap.toMatrix f f x.toLinearMap ∈ weylN4Mats t} ⊆
      {x : U ≃ₗ[ZMod p] U | LinearMap.toMatrix f f x.toLinearMap ∈ weylEN4Mats t} := by
    intro x hx
    exact Set.mem_insert_of_mem (diagSignMat 3) hx
  have hPEN : P ∈ basisClosure f (weylEN4Mats t) := Subgroup.closure_mono hsub hPcl
  have hdet3 : IsUnit (diagSignMat 3 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ zs4f_diagSign_three_sq
  obtain ⟨D, hDcl, hD⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylEN4Mats t)
    (M := diagSignMat 3) (by simp [weylEN4Mats]) hdet3
  have hPDmat : LinearMap.toMatrix f f (P * D * P).toLinearMap = diagSignMat 2 := by
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hP, hD]
    exact zs4f_pij34_diagSign_conj
  have hglin : g.toLinearMap = (P * D * P).toLinearMap :=
    (LinearMap.toMatrix f f).injective (hg.trans hPDmat.symm)
  have hgPD : g = P * D * P :=
    LinearEquiv.ext (fun v => congrArg (fun m : U →ₗ[ZMod p] U => m v) hglin)
  rw [hgPD]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hPEN hDcl) hPEN

theorem weylEN4_le_of_diagSign_mem (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t ^ 2 = -1) {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : basisClosure f (weylN4Mats t) ≤ G) {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = diagSignMat 2) :
    basisClosure f (weylEN4Mats t) ≤ G := by
  obtain ⟨P, hPcl, hP⟩ := zs4f_pi34_mem hp f ht
  have hPG : P ∈ G := hN hPcl
  have hDmat : LinearMap.toMatrix f f (P * r * P).toLinearMap = diagSignMat 3 := by
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hP, hrm]
    exact zs4f_pij34_diagSign_conj'
  rw [basisClosure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  simp only [weylEN4Mats, Set.mem_insert_iff] at hg
  rcases hg with hg3 | hgN
  · have hglin : g.toLinearMap = (P * r * P).toLinearMap :=
      (LinearMap.toMatrix f f).injective (hg3.trans hDmat.symm)
    have hgD : g = P * r * P :=
      LinearEquiv.ext (fun v => congrArg (fun m : U →ₗ[ZMod p] U => m v) hglin)
    rw [hgD]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hPG hr) hPG
  · exact hN (Subgroup.subset_closure hgN)

private def zs4fGood (v : Fin 4 → ZMod p) : Prop :=
  3 ≤ (Finset.univ.filter fun k : Fin 4 => v k ≠ 0).card ∧ v 3 ≠ 0

private theorem zs4f_good_of_three {v : Fin 4 → ZMod p} {i j : Fin 4} (hij : i ≠ j)
    (hi3 : i ≠ 3) (hj3 : j ≠ 3) (hi : v i ≠ 0) (hj : v j ≠ 0) (h3 : v 3 ≠ 0) :
    zs4fGood v := by
  refine ⟨?_, h3⟩
  have hsub : ({i, j, 3} : Finset (Fin 4)) ⊆ Finset.univ.filter fun k : Fin 4 => v k ≠ 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> simp [hi, hj, h3]
  calc 3 = ({i, j, 3} : Finset (Fin 4)).card :=
        (Finset.card_eq_three.mpr ⟨i, j, 3, hij, hi3, hj3, rfl⟩).symm
    _ ≤ _ := Finset.card_le_card hsub

private theorem zs4f_halfOnes_mulVec (v : Fin 4 → ZMod p) (k : Fin 4) :
    Matrix.mulVec (halfOnesMat 4) v k = v k - 2⁻¹ * ∑ j, v j := by
  simp only [halfOnesMat, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Fin.sum_univ_four]
  fin_cases k <;> simp <;> ring

private theorem zs4f_good_of_all (hp : p ≠ 2) {v : Fin 4 → ZMod p}
    (hv : ∀ k, 2 * v k ≠ ∑ j, v j) : zs4fGood (Matrix.mulVec (halfOnesMat 4) v) := by
  have h2 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ (zs4f_two_ne_zero hp)
  have hne : ∀ k, Matrix.mulVec (halfOnesMat 4) v k ≠ 0 := fun k hk => hv k (by
    rw [zs4f_halfOnes_mulVec] at hk
    linear_combination 2 * hk + (∑ j, v j) * h2)
  exact zs4f_good_of_three (i := 0) (j := 1) (by decide) (by decide) (by decide)
    (hne 0) (hne 1) (hne 3)

private theorem zs4f_good_of_three_supp (hp : p ≠ 2) {v : Fin 4 → ZMod p} (h3 : v 3 = 0)
    (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) (hs : v 0 + v 1 + v 2 ≠ 0) :
    zs4fGood (Matrix.mulVec (halfOnesMat 4) v) := by
  have hc : ∀ k, Matrix.mulVec (halfOnesMat 4) v k = v k - 2⁻¹ * (v 0 + v 1 + v 2) :=
    fun k => by rw [zs4f_halfOnes_mulVec, Fin.sum_univ_four, h3, add_zero]
  generalize hm : (2 : ZMod p)⁻¹ * (v 0 + v 1 + v 2) = m at hc
  have h2m : 2 * m = v 0 + v 1 + v 2 := by
    rw [← hm, ← mul_assoc, mul_inv_cancel₀ (zs4f_two_ne_zero hp), one_mul]
  have e3 : Matrix.mulVec (halfOnesMat 4) v 3 ≠ 0 := by
    rw [hc, h3]; intro e; exact hs (by linear_combination -h2m - 2 * e)
  by_cases e0 : v 0 - m = 0
  · have e1 : v 1 - m ≠ 0 := fun e1 => h2 (by linear_combination -h2m - e0 - e1)
    have e2 : v 2 - m ≠ 0 := fun e2 => h1 (by linear_combination -h2m - e0 - e2)
    exact zs4f_good_of_three (i := 1) (j := 2) (by decide) (by decide) (by decide)
      (by rw [hc]; exact e1) (by rw [hc]; exact e2) e3
  · by_cases e1 : v 1 - m = 0
    · have e2 : v 2 - m ≠ 0 := fun e2 => h0 (by linear_combination -h2m - e1 - e2)
      exact zs4f_good_of_three (i := 0) (j := 2) (by decide) (by decide) (by decide)
        (by rw [hc]; exact e0) (by rw [hc]; exact e2) e3
    · exact zs4f_good_of_three (i := 0) (j := 1) (by decide) (by decide) (by decide)
        (by rw [hc]; exact e0) (by rw [hc]; exact e1) e3

private theorem zs4f_rescale_sum (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1)
    {v : Fin 4 → ZMod p} (h1 : v 1 ≠ 0) (hs : v 0 + v 1 + v 2 = 0) :
    t * v 0 + t⁻¹ * v 1 + v 2 ≠ 0 ∨ t * v 0 + v 1 + t⁻¹ * v 2 ≠ 0 ∨
      v 0 + t * v 1 + t⁻¹ * v 2 ≠ 0 := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨e1, e2, e3⟩ := hcon
  rw [zs4f_t_inv ht] at e1 e2 e3
  exact h1 ((mul_eq_zero.mp (by linear_combination e2 - e3 - e1 + hs :
    (2 : ZMod p) * v 1 = 0)).resolve_left (zs4f_two_ne_zero hp))

private theorem zs4f_good_pair (hp : p ≠ 2) {v : Fin 4 → ZMod p} {i j : Fin 4} (hij : i ≠ j)
    (hv : ∀ k, k ≠ i → k ≠ j → v k = 0) (hsq : v i ^ 2 ≠ v j ^ 2) :
    zs4fGood (Matrix.mulVec (halfOnesMat 4) v) := by
  apply zs4f_good_of_all hp
  rw [Fintype.sum_eq_add i j hij (fun k hk => hv k hk.1 hk.2)]
  intro k hk
  by_cases hki : k = i
  · rw [hki] at hk; exact hsq (by linear_combination (v i + v j) * hk)
  · by_cases hkj : k = j
    · rw [hkj] at hk; exact hsq (by linear_combination -(v i + v j) * hk)
    · rw [hv k hki hkj, mul_zero] at hk; exact hsq (by linear_combination -(v i - v j) * hk)

private theorem zs4f_supp {u : Fin 4 → ZMod p} {i j k l : Fin 4}
    (hcov : ∀ m : Fin 4, m = i ∨ m = j ∨ m = k ∨ m = l) (hk : u k = 0) (hl : u l = 0) :
    ∀ m, m ≠ i → m ≠ j → u m = 0 := by
  intro m hmi hmj
  rcases hcov m with h | h | h | h
  · exact absurd h hmi
  · exact absurd h hmj
  · rw [h, hk]
  · rw [h, hl]

private theorem zs4f_good_pair_or (hp : p ≠ 2) {u : Fin 4 → ZMod p} {i j : Fin 4} (hij : i ≠ j)
    (hu : ∀ k, k ≠ i → k ≠ j → u k = 0) (hu0 : u ≠ 0) (l : Fin 4 → ZMod p)
    (hli : l i ^ 2 = -1) (hlj : l j = 1) :
    zs4fGood (Matrix.mulVec (halfOnesMat 4) u) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (l * u)) := by
  by_cases hq : u i ^ 2 = u j ^ 2
  · refine Or.inr (zs4f_good_pair hp hij (fun k hki hkj => by simp [hu k hki hkj]) ?_)
    simp only [Pi.mul_apply, mul_pow, hli, hlj, one_mul, hq]
    intro h
    have hj : u j = 0 := (pow_eq_zero_iff two_ne_zero).mp <|
      (mul_eq_zero.mp (by linear_combination -h : (2 : ZMod p) * u j ^ 2 = 0)).resolve_left
        (zs4f_two_ne_zero hp)
    have hi : u i = 0 := (pow_eq_zero_iff two_ne_zero).mp (by simp [hq, hj])
    refine hu0 (funext fun k => ?_)
    by_cases hki : k = i
    · rw [hki, hi]; rfl
    · by_cases hkj : k = j
      · rw [hkj, hj]; rfl
      · exact hu k hki hkj
  · exact Or.inl (zs4f_good_pair hp hij hu hq)

private theorem zs4f_alg_zero (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1)
    {u : Fin 4 → ZMod p} (hu0 : u ≠ 0) (h3 : u 3 = 0) :
    zs4fGood (Matrix.mulVec (halfOnesMat 4) u) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![t, t⁻¹, 1, 1] * u)) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![t, 1, t⁻¹, 1] * u)) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![1, t, t⁻¹, 1] * u)) := by
  have hti : t⁻¹ ^ 2 = -1 := by rw [inv_pow, ht, inv_neg, inv_one]
  have ht0 : t ≠ 0 := zs4f_t_ne_zero ht
  rcases eq_or_ne (u 0) 0 with h0 | h0
  · exact (zs4f_good_pair_or hp (i := 1) (j := 2) (by decide)
      (zs4f_supp (k := 0) (l := 3) (by decide) h0 h3) hu0 ![t, t⁻¹, 1, 1]
      (by simpa using hti) (by simp)).imp_right Or.inl
  rcases eq_or_ne (u 1) 0 with h1 | h1
  · exact (zs4f_good_pair_or hp (i := 0) (j := 2) (by decide)
      (zs4f_supp (k := 1) (l := 3) (by decide) h1 h3) hu0 ![t, t⁻¹, 1, 1]
      (by simpa using ht) (by simp)).imp_right Or.inl
  rcases eq_or_ne (u 2) 0 with h2 | h2
  · exact (zs4f_good_pair_or hp (i := 0) (j := 1) (by decide)
      (zs4f_supp (k := 2) (l := 3) (by decide) h2 h3) hu0 ![t, 1, t⁻¹, 1]
      (by simpa using ht) (by simp)).imp_right fun h => Or.inr (Or.inl h)
  by_cases hs : u 0 + u 1 + u 2 = 0
  · refine Or.inr ?_
    rcases zs4f_rescale_sum hp ht h1 hs with e | e | e
    · exact Or.inl (zs4f_good_of_three_supp hp (by simp [h3]) (by simp [h0, ht0])
        (by simp [h1, ht0]) (by simp [h2]) (by simpa using e))
    · exact Or.inr (Or.inl (zs4f_good_of_three_supp hp (by simp [h3]) (by simp [h0, ht0])
        (by simp [h1]) (by simp [h2, ht0]) (by simpa using e)))
    · exact Or.inr (Or.inr (zs4f_good_of_three_supp hp (by simp [h3]) (by simp [h0])
        (by simp [h1, ht0]) (by simp [h2, ht0]) (by simpa using e)))
  · exact Or.inl (zs4f_good_of_three_supp hp h3 h0 h1 h2 hs)

private theorem zs4f_alg_ne (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1)
    {u : Fin 4 → ZMod p} (hu0 : u ≠ 0) (h3 : u 3 ≠ 0) :
    zs4fGood u ∨ zs4fGood (Matrix.mulVec (halfOnesMat 4) u) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![t, t⁻¹, 1, 1] * u)) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![t, 1, t⁻¹, 1] * u)) := by
  have hti : t⁻¹ ^ 2 = -1 := by rw [inv_pow, ht, inv_neg, inv_one]
  rcases eq_or_ne (u 0) 0 with h0 | h0 <;> rcases eq_or_ne (u 1) 0 with h1 | h1
  · exact Or.inr ((zs4f_good_pair_or hp (i := 2) (j := 3) (by decide)
      (zs4f_supp (k := 0) (l := 1) (by decide) h0 h1) hu0 ![t, 1, t⁻¹, 1]
      (by simpa using hti) (by simp)).imp_right Or.inr)
  · rcases eq_or_ne (u 2) 0 with h2 | h2
    · exact Or.inr ((zs4f_good_pair_or hp (i := 1) (j := 3) (by decide)
        (zs4f_supp (k := 0) (l := 2) (by decide) h0 h2) hu0 ![t, t⁻¹, 1, 1]
        (by simpa using hti) (by simp)).imp_right Or.inl)
    · exact Or.inl (zs4f_good_of_three (i := 1) (j := 2) (by decide) (by decide) (by decide)
        h1 h2 h3)
  · rcases eq_or_ne (u 2) 0 with h2 | h2
    · exact Or.inr ((zs4f_good_pair_or hp (i := 0) (j := 3) (by decide)
        (zs4f_supp (k := 1) (l := 2) (by decide) h1 h2) hu0 ![t, t⁻¹, 1, 1]
        (by simpa using ht) (by simp)).imp_right Or.inl)
    · exact Or.inl (zs4f_good_of_three (i := 0) (j := 2) (by decide) (by decide) (by decide)
        h0 h2 h3)
  · exact Or.inl (zs4f_good_of_three (i := 0) (j := 1) (by decide) (by decide) (by decide)
      h0 h1 h3)

private theorem zs4f_alg (hp : p ≠ 2) {t : ZMod p} (ht : t ^ 2 = -1) {u : Fin 4 → ZMod p}
    (hu0 : u ≠ 0) :
    zs4fGood u ∨ zs4fGood (Matrix.mulVec (halfOnesMat 4) u) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![t, t⁻¹, 1, 1] * u)) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![t, 1, t⁻¹, 1] * u)) ∨
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (![1, t, t⁻¹, 1] * u)) := by
  rcases eq_or_ne (u 3) 0 with h3 | h3
  · exact Or.inr (zs4f_alg_zero hp ht hu0 h3)
  · rcases zs4f_alg_ne hp ht hu0 h3 with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h)))]

private theorem zs4f_mat_ca (t : ZMod p) :
    (pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) * pijMat 0 1 1 =
      Matrix.diagonal ![t, t⁻¹, 1, 1] := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem zs4f_mat_bcab (t : ZMod p) :
    (pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) * Matrix.diagonal ![t, t⁻¹, 1, 1] *
      pijMat 1 2 1 = Matrix.diagonal ![t, 1, t⁻¹, 1] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

private theorem zs4f_mat_abcaba (t : ZMod p) :
    (pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) * Matrix.diagonal ![t, 1, t⁻¹, 1] *
      pijMat 0 1 1 = Matrix.diagonal ![1, t, t⁻¹, 1] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

private theorem zs4f_diagonal_mulVec (l v : Fin 4 → ZMod p) :
    Matrix.mulVec (Matrix.diagonal l) v = l * v :=
  funext (Matrix.mulVec_diagonal l v)

namespace NFourData

variable [Module.Finite (ZMod p) U] {f : Module.Basis (Fin 4) (ZMod p) U} {t : ZMod p}
  {a b c d : U ≃ₗ[ZMod p] U} {G : Subgroup (U ≃ₗ[ZMod p] U)}

omit [Module.Finite (ZMod p) U] in
theorem weylN4_le (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) :
    basisClosure f (weylN4Mats t) ≤ G := by
  rw [basisClosure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  simp only [weylN4Mats, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h1 | h2 | h3 | h4
  · rw [zs4f_eq_of_toMatrix_eq (h1.trans h.toMatrix_a.symm)]; exact h.a_mem
  · rw [zs4f_eq_of_toMatrix_eq (h2.trans h.toMatrix_b.symm)]; exact h.b_mem
  · rw [zs4f_eq_of_toMatrix_eq (h3.trans h.toMatrix_c.symm)]; exact h.c_mem
  · rw [zs4f_eq_of_toMatrix_eq (h4.trans hd.symm)]; exact h.d_mem

private theorem zs4f_mul_of_etaOK {s r : ZMod p} (h : EtaOK 4 s r) :
    s * r = 0 ∨ s * r = 1 ∨ s * r = 2 := by
  rcases h with ⟨e1, e2⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨e5, _⟩
  · exact Or.inl (by rw [e1, e2, mul_zero])
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)
  · omega

private theorem zs4f_alpha_of_eq_halfOnes (h2 : (2 : ZMod p) ≠ 0) {α : ZMod p}
    (hmat : halfFormMat α = halfOnesMat 4) : α = -1 := by
  have hentry : (2 : ZMod p)⁻¹ * α = -((2 : ZMod p)⁻¹) := by
    simpa [halfFormMat, halfOnesMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.of_apply] using congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod p) => M 0 3) hmat
  field_simp [h2] at hentry
  linear_combination hentry

private theorem zs4f_alpha_of_beta (hp : p ≠ 2) (hp4 : 4 < p) (hmod : p % 4 = 1) {α : ZMod p}
    (hα : α ≠ 0)
    (hcases1 : (10 - 3 * (α + α⁻¹)) / 4 = 0 ∨ (10 - 3 * (α + α⁻¹)) / 4 = 1
      ∨ (10 - 3 * (α + α⁻¹)) / 4 = 2)
    (hcases2 : (2 - (α + α⁻¹)) / 4 = 0 ∨ (2 - (α + α⁻¹)) / 4 = 1 ∨ (2 - (α + α⁻¹)) / 4 = 2) :
    α = 1 := by
  rcases zs4f_beta_cases hp hp4 hmod hcases1 hcases2 with hS | ⟨hp5, hS⟩
  · have h : α + α⁻¹ = 2 := hS
    have h' : α * α - 2 * α + 1 = 0 := by
      field_simp [hα] at h
      linear_combination h
    have hsq : (α - 1) ^ 2 = 0 := by linear_combination h'
    have hz : α - 1 = 0 := by
      rw [pow_two] at hsq
      exact mul_self_eq_zero.mp hsq
    linear_combination hz
  · exfalso
    subst hp5
    have h' : α ^ 2 + α + 1 = 0 := by
      have hα0 : α ≠ 0 := hα
      have h := hS
      field_simp [hα0] at h
      have h5 : (5 : ZMod 5) = 0 := zs4f_five_five
      linear_combination h - α * h5
    exact zs4f_five_no_root α h'

private theorem zs4f_eta_xd (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) {α : ZMod p} (hα : α ≠ 0)
    (hxα : LinearMap.toMatrix f f x.toLinearMap = halfFormMat α) (hxd : x ≠ d) :
    (10 - 3 * (α + α⁻¹)) / 4 = 0 ∨ (10 - 3 * (α + α⁻¹)) / 4 = 1
      ∨ (10 - 3 * (α + α⁻¹)) / 4 = 2 := by
  have hp4 : 4 < p := zs4f_four_lt_p hp h.sq_t
  have h2 : (2 : ZMod p) ≠ 0 := zs4f_two_ne_zero hp
  let hρx : Fin 4 → ZMod p := fun i => if i = 3 then -α⁻¹ else 1
  let hκx : Fin 4 → ZMod p := fun i => if i = 3 then -((2 : ZMod p)⁻¹ * α) else (2 : ZMod p)⁻¹
  let hρd : Fin 4 → ZMod p := fun _ => 1
  let hκd : Fin 4 → ZMod p := fun _ => (2 : ZMod p)⁻¹
  have hxshape : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec hρx hκx := by
    rw [hxα]
    simp only [hρx, hκx]
    exact zs4f_halfFormMat_vecMulVec h2 hα
  have hdshape : LinearMap.toMatrix f f d.toLinearMap = 1 - Matrix.vecMulVec hρd hκd := by
    rw [hd]
    simp only [hρd, hκd]
    exact zs4f_halfOnes_vecMulVec
  obtain ⟨hdr, hdrefl⟩ := FFourCoord.eq_reflection_of_toMatrix f hdshape
    (by simpa only [hρd, hκd] using zs4f_sum_d h2)
  have hEta1 : EtaOK 4 (∑ i, hκd i * hρx i) (∑ i, hκx i * hρd i) := by
    have := etaOK_of_toMatrix h.dmax (by norm_num) hp4 hp f h.d_mem hxG (Ne.symm hxd)
      hdr hdrefl hxshape (by simpa only [hρx, hκx] using zs4f_sum_x h2 hα)
    simpa only [zs4f_coord_sum_apply, zs4f_repr_sum_smul] using this
  have hb1 : (∑ i, hκd i * hρx i) * (∑ i, hκx i * hρd i)
      = (10 - 3 * (α + α⁻¹)) / 4 := by
    simp only [hκd, hρx, hκx, hρd]
    simp [Fin.sum_univ_four]
    field_simp [h2, hα, zs4f_four_ne_zero hp4]
    ring_nf
  rw [← hb1]
  exact zs4f_mul_of_etaOK hEta1

private theorem zs4f_eta_xcdc (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) {α : ZMod p} (hα : α ≠ 0)
    (hxα : LinearMap.toMatrix f f x.toLinearMap = halfFormMat α) (hxcdc : x ≠ c * d * c) :
    (2 - (α + α⁻¹)) / 4 = 0 ∨ (2 - (α + α⁻¹)) / 4 = 1 ∨ (2 - (α + α⁻¹)) / 4 = 2 := by
  have hp4 : 4 < p := zs4f_four_lt_p hp h.sq_t
  have h2 : (2 : ZMod p) ≠ 0 := zs4f_two_ne_zero hp
  have ht0 : t ≠ 0 := zs4f_t_ne_zero h.sq_t
  let hρx : Fin 4 → ZMod p := fun i => if i = 3 then -α⁻¹ else 1
  let hκx : Fin 4 → ZMod p := fun i => if i = 3 then -((2 : ZMod p)⁻¹ * α) else (2 : ZMod p)⁻¹
  let hρc : Fin 4 → ZMod p := fun i => if i = 0 then t else if i = 1 then t⁻¹ else 1
  let hκc : Fin 4 → ZMod p := fun j =>
    if j = 0 then (2 : ZMod p)⁻¹ * t⁻¹ else if j = 1 then (2 : ZMod p)⁻¹ * t
      else (2 : ZMod p)⁻¹
  have hxshape : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec hρx hκx := by
    rw [hxα]
    simp only [hρx, hκx]
    exact zs4f_halfFormMat_vecMulVec h2 hα
  have hcdcshape : LinearMap.toMatrix f f (c * d * c).toLinearMap =
      1 - Matrix.vecMulVec hρc hκc := by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul,
      LinearMap.toMatrix_mul, h.toMatrix_c, hd]
    simp only [hρc, hκc]
    exact zs4f_pij01_halfOnes h2 ht0
  obtain ⟨hxr, hxrefl⟩ := FFourCoord.eq_reflection_of_toMatrix f hxshape
    (by simpa only [hρx, hκx] using zs4f_sum_x h2 hα)
  have hcdcG : c * d * c ∈ G := Subgroup.mul_mem _ (Subgroup.mul_mem _ h.c_mem h.d_mem) h.c_mem
  have hEta2 : EtaOK 4 (∑ i, hκx i * hρc i) (∑ i, hκc i * hρx i) := by
    have := etaOK_of_toMatrix h.dmax (by norm_num) hp4 hp f hxG hcdcG hxcdc hxr hxrefl
      hcdcshape (by simpa only [hρc, hκc] using zs4f_sum_cdc h2 ht0)
    simpa only [zs4f_coord_sum_apply, zs4f_repr_sum_smul] using this
  have hb2 : (∑ i, hκx i * hρc i) * (∑ i, hκc i * hρx i)
      = (2 - (α + α⁻¹)) / 4 := by
    simp only [hκx, hρc, hκc, hρx]
    rw [zs4f_t_inv h.sq_t]
    simp [Fin.sum_univ_four]
    field_simp [h2, hα, zs4f_four_ne_zero hp4]
    ring_nf
  rw [← hb2]
  exact zs4f_mul_of_etaOK hEta2

theorem alpha_cases (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) (hx : IsRefl p x) {α : ZMod p}
    (hxα : LinearMap.toMatrix f f x.toLinearMap = halfFormMat α) : α = 1 ∨ α = -1 := by
  have hp4 : 4 < p := zs4f_four_lt_p hp h.sq_t
  have h2 : (2 : ZMod p) ≠ 0 := zs4f_two_ne_zero hp
  have hα : α ≠ 0 := by
    have hsq : halfFormMat α * halfFormMat α = 1 := by
      have h1 := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) hx.1
      rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hxα] at h1
      simpa using h1
    exact zs4f_alpha_ne_zero hp hp4 hsq
  by_cases hxd : x = d
  · exact Or.inr (zs4f_alpha_of_eq_halfOnes h2 (by rw [← hxα, hxd, hd]))
  by_cases hxcdc : x = c * d * c
  · refine absurd ?_ (zs4f_halfFormMat_ne_cdc h2 h.sq_t α)
    rw [← hxα, hxcdc, LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, h.toMatrix_c, hd]
  · exact Or.inl (zs4f_alpha_of_beta hp hp4 (zs4f_mod_four hp h.sq_t) hα
      (zs4f_eta_xd hp h hd hxG hα hxα hxd) (zs4f_eta_xcdc hp h hd hxG hα hxα hxcdc))

theorem mem_weylEN4_of_commute_ab (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) (hx : IsRefl p x) (hxa : x * a = a * x) (hxb : x * b = b * x)
    (hxc : orderOf (x * c) = 3) :
    x ∈ basisClosure f (weylEN4Mats t) ∧ (x ∉ basisClosure f (weylN4Mats t) →
      ∃ D ∈ G, LinearMap.toMatrix f f D.toLinearMap = diagSignMat 3) := by
  have h2 : (2 : ZMod p) ≠ 0 := zs4f_two_ne_zero hp
  obtain ⟨α, _hαne, hxα⟩ := toMatrix_of_commute_pij hp f h.sq_t h.toMatrix_a h.toMatrix_b
    h.toMatrix_c hx hxa hxb hxc
  have hdcl : d ∈ basisClosure f (weylEN4Mats t) :=
    Subgroup.subset_closure (by simp [weylEN4Mats, weylN4Mats, hd])
  rcases alpha_cases hp h hd hxG hx hxα with hα1 | hαneg
  · have hconj := toMatrix_conj_halfFormMat_one hp f hd (by rw [hxα, hα1])
    have hdxdcl : d * x * d ∈ basisClosure f (weylEN4Mats t) :=
      Subgroup.subset_closure (by
        simp only [Set.mem_setOf_eq]
        rw [hconj]
        simp [weylEN4Mats])
    have hxeq : d * (d * x * d) * d = x := by
      calc d * (d * x * d) * d = (d * d) * x * (d * d) := by group
        _ = 1 * x * 1 := by rw [h.isRefl_d.1]
        _ = x := by group
    have hxW : x ∈ basisClosure f (weylEN4Mats t) := by
      rw [← hxeq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hdcl hdxdcl) hdcl
    exact ⟨hxW, fun _ => ⟨d * x * d,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ h.d_mem hxG) h.d_mem, hconj⟩⟩
  · have hxd : x = d := by
      apply zs4f_eq_of_toMatrix_eq
      rw [hxα, hαneg, halfFormMat_neg_one h2, hd]
    have hdN : d ∈ basisClosure f (weylN4Mats t) :=
      Subgroup.subset_closure (by simp [weylN4Mats, hd])
    have hxW : x ∈ basisClosure f (weylEN4Mats t) := by rw [hxd]; exact hdcl
    have hxN : x ∈ basisClosure f (weylN4Mats t) := by rw [hxd]; exact hdN
    exact ⟨hxW, fun h => absurd hxN h⟩

private def zs4fDiag {K : Type} [Field K] (t : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal fun i => if i = 0 then t else if i = 1 then 1 else if i = 2 then 1 else -t

section ZS4fSwap

variable {K : Type} [Field K]

private lemma zs4f_t_invK {t : K} (ht : t ^ 2 = -1) : t⁻¹ = -t := by
  have h : t * (-t) = 1 := by
    calc t * (-t) = -(t * t) := mul_neg t t
      _ = -(-1) := by rw [← pow_two, ht]
      _ = 1 := neg_neg 1
  exact inv_eq_of_mul_eq_one_right h

private theorem zs4fDiag_mul_inv {t : K} (ht0 : t ≠ 0) : zs4fDiag t * zs4fDiag t⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zs4fDiag, Matrix.mul_apply, Matrix.diagonal, ht0]

private theorem zs4f_pij12_halfOnes :
    (pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) K) * halfOnesMat 4 * pijMat 1 2 1 =
      halfOnesMat 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, halfOnesMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply]

private theorem zs4f_swap_word {t : K} (ht : t ^ 2 = -1) :
    (pijMat 0 1 t⁻¹ * pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 t⁻¹ * pijMat 0 1 1 :
        Matrix (Fin 4) (Fin 4) K) =
      t • (pijMat 1 2 1 * zs4fDiag t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, zs4fDiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      Matrix.smul_apply, zs4f_t_invK ht]
  ring_nf
  linear_combination ht

private theorem zs4f_swap_word_inv {t : K} (ht : t ^ 2 = -1) :
    (pijMat 0 1 1 * pijMat 0 1 t⁻¹ * pijMat 1 2 1 * pijMat 0 1 1 * pijMat 0 1 t⁻¹ :
        Matrix (Fin 4) (Fin 4) K) =
      t⁻¹ • (zs4fDiag t⁻¹ * pijMat 1 2 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, zs4fDiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      Matrix.smul_apply, zs4f_t_invK ht]
  ring_nf
  linear_combination ht

private theorem zs4f_swap_d_matrix {t : K} (ht : t ^ 2 = -1) :
    (pijMat 0 1 t⁻¹ * pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 t⁻¹ * pijMat 0 1 1 :
        Matrix (Fin 4) (Fin 4) K) *
      (zs4fDiag t⁻¹ * halfOnesMat 4 * zs4fDiag t) *
      (pijMat 0 1 1 * pijMat 0 1 t⁻¹ * pijMat 1 2 1 * pijMat 0 1 1 * pijMat 0 1 t⁻¹) =
      halfOnesMat 4 := by
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    norm_num at ht
  rw [zs4f_swap_word ht, zs4f_swap_word_inv ht]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [smul_smul, show t⁻¹ * t = 1 by exact inv_mul_cancel₀ ht0]
  rw [one_smul]
  calc (pijMat 1 2 1 * zs4fDiag t) * (zs4fDiag t⁻¹ * halfOnesMat 4 * zs4fDiag t) *
        (zs4fDiag t⁻¹ * pijMat 1 2 1)
      = pijMat 1 2 1 * (zs4fDiag t * zs4fDiag t⁻¹) * halfOnesMat 4 *
          (zs4fDiag t * zs4fDiag t⁻¹) * pijMat 1 2 1 := by noncomm_ring
    _ = pijMat 1 2 1 * halfOnesMat 4 * pijMat 1 2 1 := by
          rw [zs4fDiag_mul_inv ht0]; simp
    _ = halfOnesMat 4 := zs4f_pij12_halfOnes

end ZS4fSwap

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_unitsSMul_c (h : NFourData f t a b c d G)
    (u : (ZMod p)ˣ) (hu : (u : ZMod p) = t) :
    LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u]) c.toLinearMap
      = pijMat 0 1 1 := by
  ext r s
  rw [toMatrix_unitsSMul_apply, h.toMatrix_c]
  fin_cases r <;> fin_cases s <;>
    simp [pijMat, hu, Units.val_inv_eq_inv_val, Units.val_neg,
      zs4f_t_ne_zero h.sq_t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_unitsSMul_b (h : NFourData f t a b c d G)
    (u : (ZMod p)ˣ) (hu : (u : ZMod p) = t) :
    LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u]) b.toLinearMap
      = pijMat 1 2 1 := by
  ext r s
  rw [toMatrix_unitsSMul_apply, h.toMatrix_b]
  fin_cases r <;> fin_cases s <;>
    simp [pijMat, hu, Units.val_inv_eq_inv_val, Units.val_neg,
      zs4f_t_ne_zero h.sq_t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_unitsSMul_a (h : NFourData f t a b c d G)
    (u : (ZMod p)ˣ) (hu : (u : ZMod p) = t) :
    LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u]) a.toLinearMap
      = pijMat 0 1 t⁻¹ := by
  ext r s
  rw [toMatrix_unitsSMul_apply, h.toMatrix_a]
  fin_cases r <;> fin_cases s <;>
    simp [pijMat, hu, Units.val_inv_eq_inv_val, Units.val_neg,
      zs4f_t_ne_zero h.sq_t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_unitsSMul_d
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4)
    (u : (ZMod p)ˣ) (hu : (u : ZMod p) = t) :
    LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u]) d.toLinearMap
      = zs4fDiag t⁻¹ * halfOnesMat 4 * zs4fDiag t := by
  ext r s
  rw [toMatrix_unitsSMul_apply, hd]
  fin_cases r <;> fin_cases s <;>
    simp [zs4fDiag, halfOnesMat, Matrix.diagonal_mul, Matrix.mul_diagonal, hu,
      Units.val_inv_eq_inv_val, Units.val_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

omit [Module.Finite (ZMod p) U] in
private lemma zs4f_repr_of_halfOnes {y : U ≃ₗ[ZMod p] U}
    (hy : LinearMap.toMatrix f f y.toLinearMap = halfOnesMat 4) (i j : Fin 4) :
    f.repr (y.toLinearMap (f i)) j = halfOnesMat 4 j i := by
  rw [← LinearMap.toMatrix_apply, hy]

private lemma zs4f_halfOnes_entry_ne_zero (hp : p ≠ 2) (k l : Fin 4) :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)) k l ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zs4f_two_ne_zero hp
  have h2inv : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  have h2inv1 : (2 : ZMod p)⁻¹ ≠ 1 := by
    intro h
    have h2eq : (2 : ZMod p) = 1 := by
      have := congrArg (fun x : ZMod p => x * 2) h
      rw [one_mul, inv_mul_cancel₀ h2] at this
      exact this.symm
    have hone : (1 : ZMod p) = 0 := by linear_combination h2eq
    exact one_ne_zero hone
  rcases eq_or_ne k l with hkl | hkl
  · subst hkl
    have hentry : (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)) k k =
        1 - (2 : ZMod p)⁻¹ := by
      simp [halfOnesMat, Matrix.sub_apply, Matrix.of_apply]
    rw [hentry]
    exact sub_ne_zero.mpr (Ne.symm h2inv1)
  · have hentry : (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)) k l =
        -((2 : ZMod p)⁻¹) := by
      simp [halfOnesMat, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply,
        if_neg hkl]
    rw [hentry]
    exact neg_ne_zero.mpr h2inv

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_not_monomial_of_halfOnes (hp : p ≠ 2) {y : U ≃ₗ[ZMod p] U}
    (hy : LinearMap.toMatrix f f y.toLinearMap = halfOnesMat 4) :
    ¬ ∀ i, ∃ j, ∃ x : ZMod p, y (f i) = x • f j := by
  intro h
  obtain ⟨j, x, hx⟩ := h 0
  have hx' : y.toLinearMap (f 0) = x • f j := hx
  have key := congrArg (fun v => f.repr v) hx'
  rw [map_smul, Module.Basis.repr_self] at key
  have h2 : (2 : ZMod p) ≠ 0 := zs4f_two_ne_zero hp
  let k : Fin 4 := if j = 0 then 1 else 0
  have hkj : k ≠ j := by
    dsimp only [k]; split_ifs with hj
    · exact fun h => by simp [hj] at h
    · exact fun h => hj h.symm
  have hkey := congrArg (fun (g : Fin 4 →₀ ZMod p) => g k) key
  rw [Finsupp.smul_apply, smul_eq_mul] at hkey
  have hsing : (Finsupp.single j (1 : ZMod p)) k = 0 := by
    rw [Finsupp.single_apply, if_neg (show j ≠ k from fun h => hkj h.symm)]
  rw [hsing, mul_zero] at hkey
  rw [zs4f_repr_of_halfOnes hy 0 k] at hkey
  exact zs4f_halfOnes_entry_ne_zero hp k 0 hkey

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_not_le_of_halfOnes (hp : p ≠ 2) {y : U ≃ₗ[ZMod p] U}
    (hy : LinearMap.toMatrix f f y.toLinearMap = halfOnesMat 4) :
    ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  intro hle
  have hmem : y (f 0) - f 0 ∈ HardMathSupport.Kantor79.movedSpace y := by
    rw [HardMathSupport.Kantor79.movedSpace]; exact ⟨f 0, rfl⟩
  have hker : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) ≤
      LinearMap.ker (f.coord 3) := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    fin_cases i <;> simp
  have hzero : f.repr (y.toLinearMap (f 0) - f 0) 3 = 0 := by
    have := hker (hle hmem)
    simpa [Module.Basis.coord_apply] using this
  have hcoord : f.repr (y.toLinearMap (f 0) - f 0) 3 = -((2 : ZMod p)⁻¹) := by
    rw [map_sub, Finsupp.sub_apply, zs4f_repr_of_halfOnes hy 0 3, Module.Basis.repr_self]
    simp [halfOnesMat, Matrix.sub_apply, Matrix.of_apply]
  rw [hcoord] at hzero
  exact (neg_ne_zero.mpr (inv_ne_zero (zs4f_two_ne_zero hp))) hzero

private theorem zs4f_swap_conj_mem (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    a * c * b * a * c * d * c * a * b * c * a ∈ G ∧
      IsRefl p (a * c * b * a * c * d * c * a * b * c * a) := by
  have h4 := fourRefl hp h
  have hinv : (a * c * b * a * c)⁻¹ = c * a * b * c * a := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev,
      inv_eq_of_mul_eq_one_right h4.isRefl_c.1, inv_eq_of_mul_eq_one_right h4.isRefl_a.1,
      inv_eq_of_mul_eq_one_right h4.isRefl_b.1]
    group
  have heq : a * c * b * a * c * d * c * a * b * c * a =
      (a * c * b * a * c) * d * (a * c * b * a * c)⁻¹ := by rw [hinv]; group
  have hw : a * c * b * a * c ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem h.a_mem h.c_mem) h.b_mem) h.a_mem) h.c_mem
  rw [heq]
  exact ⟨G.mul_mem (G.mul_mem hw h.d_mem) (G.inv_mem hw), IsRefl.conj h.isRefl_d _⟩

theorem swap_ac (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) (u : (ZMod p)ˣ)
    (hu : (u : ZMod p) = t) :
    NFourData (f.unitsSMul ![u, 1, 1, -u]) t⁻¹ c b a (a * c * b * a * c * d * c * a * b * c * a)
        G ∧
      LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u])
        (a * c * b * a * c * d * c * a * b * c * a).toLinearMap = halfOnesMat 4 := by
  have htinv : (t⁻¹) ^ 2 = -1 := by
    rw [inv_pow, h.sq_t]
    exact inv_eq_of_mul_eq_one_right (by ring : (-1 : ZMod p) * (-1) = 1)
  have hc := zs4f_unitsSMul_c h u hu
  have hb := zs4f_unitsSMul_b h u hu
  have ha := zs4f_unitsSMul_a h u hu
  have hd' := zs4f_unitsSMul_d hd u hu
  have hword : LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u])
      (a * c * b * a * c * d * c * a * b * c * a).toLinearMap = halfOnesMat 4 := by
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, ha, hc, hb, hd']
    simpa only [mul_assoc] using zs4f_swap_d_matrix h.sq_t
  obtain ⟨hmem, hrefl⟩ := zs4f_swap_conj_mem hp h
  refine ⟨?_, hword⟩
  exact { sq_t := htinv
          toMatrix_a := hc
          toMatrix_b := hb
          toMatrix_c := ha
          a_mem := h.c_mem
          b_mem := h.b_mem
          c_mem := h.a_mem
          d_mem := hmem
          isRefl_d := hrefl
          not_monomial := zs4f_not_monomial_of_halfOnes hp hword
          not_le := zs4f_not_le_of_halfOnes hp hword
          transvectionFree := h.transvectionFree
          dmax := h.dmax
          no336 := h.no336 }

omit [Module.Finite (ZMod p) U] in
private lemma zs4f_toMatrix_unitsSMul_diag (f : Module.Basis (Fin 4) (ZMod p) U)
    (w : Fin 4 → (ZMod p)ˣ) {g : U ≃ₗ[ZMod p] U}
    (hg : ∀ r c, r ≠ c → LinearMap.toMatrix f f g.toLinearMap r c = 0) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g.toLinearMap =
      LinearMap.toMatrix f f g.toLinearMap := by
  ext r c
  rw [toMatrix_unitsSMul_apply]
  rcases eq_or_ne r c with hrc | hrc
  · subst hrc
    have hw : ((w r)⁻¹ : ZMod p) * (w r : ZMod p) = 1 := by
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul]
      simp
    rw [Units.val_inv_eq_inv_val]
    linear_combination (LinearMap.toMatrix f f g.toLinearMap r r) * hw
  · rw [hg r c hrc]; ring

private theorem zs4f_swap_le_N4 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) (u : (ZMod p)ˣ)
    (hu : (u : ZMod p) = t) :
    basisClosure (f.unitsSMul ![u, 1, 1, -u]) (weylN4Mats t⁻¹) ≤
      basisClosure f (weylN4Mats t) := by
  have hc := zs4f_unitsSMul_c h u hu
  have hb := zs4f_unitsSMul_b h u hu
  have ha := zs4f_unitsSMul_a h u hu
  obtain ⟨hNF', hd'mat⟩ := swap_ac hp h hd u hu
  have haW : a ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_a])
  have hbW : b ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_b])
  have hcW : c ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_c])
  have hdW : d ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, hd])
  have hd'W : a * c * b * a * c * d * c * a * b * c * a ∈ basisClosure f (weylN4Mats t) := by
    repeat' apply Subgroup.mul_mem
    all_goals assumption
  rw [basisClosure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  simp only [weylN4Mats, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h1 | h2 | h3 | h4
  · have hgc : g = c := zs4f_eq_of_toMatrix_eq (h1.trans hc.symm)
    rw [hgc]; exact hcW
  · have hgb : g = b := zs4f_eq_of_toMatrix_eq (h2.trans hb.symm)
    rw [hgb]; exact hbW
  · have hga : g = a := zs4f_eq_of_toMatrix_eq (h3.trans ha.symm)
    rw [hga]; exact haW
  · have hgd : g = a * c * b * a * c * d * c * a * b * c * a :=
      zs4f_eq_of_toMatrix_eq (h4.trans hd'mat.symm)
    rw [hgd]; exact hd'W

private theorem zs4f_swap_le_EN4 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) (u : (ZMod p)ˣ)
    (hu : (u : ZMod p) = t) :
    basisClosure (f.unitsSMul ![u, 1, 1, -u]) (weylEN4Mats t⁻¹) ≤
      basisClosure f (weylEN4Mats t) := by
  have hdet3 : IsUnit (diagSignMat 3 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ zs4f_diagSign_three_sq
  have hN := zs4f_swap_le_N4 hp h hd u hu
  rw [basisClosure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  rw [weylEN4Mats, Set.mem_insert_iff] at hg
  rcases hg with h1 | hgN
  · obtain ⟨hh, hhcl, hhmat⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylEN4Mats t)
      (M := diagSignMat 3) (by simp [weylEN4Mats]) hdet3
    have hdiag : ∀ r c, r ≠ c → LinearMap.toMatrix f f hh.toLinearMap r c = 0 := by
      intro r c hrc
      rw [hhmat]
      simp [diagSignMat, hrc]
    have hh' : LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u])
        hh.toLinearMap = diagSignMat 3 := by
      rw [zs4f_toMatrix_unitsSMul_diag f _ hdiag, hhmat]
    have hgh : g = hh := zs4f_eq_of_toMatrix_eq (h1.trans hh'.symm)
    rw [hgh]; exact hhcl
  · have hN4EN : basisClosure f (weylN4Mats t) ≤ basisClosure f (weylEN4Mats t) :=
      Subgroup.closure_mono (by
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact Set.mem_insert_of_mem _ hy)
    exact (hN.trans hN4EN) (Subgroup.subset_closure hgN)

theorem mem_weylEN4_of_commute_bc (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) (hx : IsRefl p x) (hxb : x * b = b * x) (hxc : x * c = c * x)
    (hxa : orderOf (x * a) = 3) :
    x ∈ basisClosure f (weylEN4Mats t) ∧ (x ∉ basisClosure f (weylN4Mats t) →
      ∃ D ∈ G, LinearMap.toMatrix f f D.toLinearMap = diagSignMat 3) := by
  have hdet3 : IsUnit (diagSignMat 3 : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    zs4f_isUnit_det_of_mul_self _ zs4f_diagSign_three_sq
  let u : (ZMod p)ˣ := Units.mk0 t (zs4f_t_ne_zero h.sq_t)
  have hu : (u : ZMod p) = t := rfl
  obtain ⟨hNF', hd'mat⟩ := swap_ac hp h hd u hu
  have hab := mem_weylEN4_of_commute_ab hp hNF' hd'mat hxG hx hxc hxb hxa
  have hleN := zs4f_swap_le_N4 hp h hd u hu
  have hleE := zs4f_swap_le_EN4 hp h hd u hu
  refine ⟨hleE hab.1, ?_⟩
  intro hxN
  have hxN' : x ∉ basisClosure (f.unitsSMul ![u, 1, 1, -u]) (weylN4Mats t⁻¹) :=
    fun hxin => hxN (hleN hxin)
  obtain ⟨D, hDG, hDmat⟩ := hab.2 hxN'
  obtain ⟨hh, _hhcl, hhmat⟩ := exists_mem_basisClosure_toMatrix_eq f (S := weylEN4Mats t)
    (M := diagSignMat 3) (by simp [weylEN4Mats]) hdet3
  have hdiag : ∀ r c, r ≠ c → LinearMap.toMatrix f f hh.toLinearMap r c = 0 := by
    intro r c hrc
    rw [hhmat]
    simp [diagSignMat, hrc]
  have hh' : LinearMap.toMatrix (f.unitsSMul ![u, 1, 1, -u]) (f.unitsSMul ![u, 1, 1, -u])
      hh.toLinearMap = diagSignMat 3 := by
    rw [zs4f_toMatrix_unitsSMul_diag f _ hdiag, hhmat]
  have hDh : D = hh := zs4f_eq_of_toMatrix_eq (hDmat.trans hh'.symm)
  exact ⟨D, hDG, by rw [hDh, hhmat]⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4f_movedSpace_conj {g x : U ≃ₗ[ZMod p] U} {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.movedSpace x) :
    g w ∈ HardMathSupport.Kantor79.movedSpace (g * x * g⁻¹) := by
  obtain ⟨v, hv⟩ := hw
  refine ⟨g v, ?_⟩
  rw [← hv]
  simp only [LinearMap.sub_apply, map_sub]
  simp

omit [Module.Finite (ZMod p) U] in
private lemma zs4f_not_le_of_coord {y : U ≃ₗ[ZMod p] U} {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.movedSpace y) (h3 : f.repr w 3 ≠ 0) :
    ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  intro hle
  have hker : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) ≤
      LinearMap.ker (f.coord 3) := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    fin_cases i <;> simp
  have hzero : f.repr w 3 = 0 := by
    have := hker (hle hw)
    simpa [Module.Basis.coord_apply] using this
  exact h3 hzero

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_smul_ne_sub {w : U}
    (h3 : 3 ≤ (Finset.univ.filter (fun i : Fin 4 => f.repr w i ≠ 0)).card) {i j : Fin 4}
    {x c : ZMod p} (hcne : c ≠ 0) : c • w ≠ x • f j - f i := by
  intro hc
  have heq : f.repr (c • w) = x • Finsupp.single j 1 - Finsupp.single i 1 := by
    rw [hc]
    simp only [map_sub, map_smul, Module.Basis.repr_self]
  have hsupp : (f.repr (c • w)).support ⊆ ({i, j} : Finset (Fin 4)) := by
    rw [heq]
    intro k hk
    simp only [Finsupp.mem_support_iff, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.single_apply] at hk ⊢
    by_cases hki : k = i
    · simp [hki]
    · by_cases hkj : k = j
      · simp [hkj]
      · exfalso
        apply hk
        have h1 : j ≠ k := fun h => hkj h.symm
        have h2 : i ≠ k := fun h => hki h.symm
        simp [h1, h2]
  rw [map_smul, Finsupp.support_smul_eq hcne] at hsupp
  have hsuppeq : (f.repr w).support =
      Finset.univ.filter (fun i : Fin 4 => f.repr w i ≠ 0) := by
    ext i; simp [Finsupp.mem_support_iff]
  have hwcard : 3 ≤ (f.repr w).support.card := by rw [hsuppeq]; exact h3
  have hcard := Finset.card_le_card hsupp
  have h2 : ({i, j} : Finset (Fin 4)).card ≤ 2 := by
    by_cases hij : i = j <;> simp [hij]
  omega

private theorem zs4f_false_of_fix_basis {y : U ≃ₗ[ZMod p] U} (hy : IsRefl p y)
    (hfix : ∀ i : Fin 4, y (f i) = f i) : False := by
  have hlin : (y : U →ₗ[ZMod p] U) - 1 = 0 := f.ext fun i => by simp [hfix i]
  have hy1 : y = 1 := by
    apply LinearEquiv.ext
    intro v
    have hφv : (y : U →ₗ[ZMod p] U) v - v = 0 := by
      have := congrArg (fun L : Module.End (ZMod p) U => L v) hlin
      simpa [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe] using this
    exact sub_eq_zero.mp hφv
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y) = 0 := by
    rw [hy1, HardMathSupport.Kantor79.movedSpace]
    have h0 : (((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1 : Module.End (ZMod p) U) = 0 := by
      ext v; simp
    rw [h0]; simp
  have h1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y) = 1 := by
    rw [HardMathSupport.Kantor79.movedSpace]; exact hy.2
  exact Nat.one_ne_zero (h1.symm.trans hfin)

private theorem zs4f_not_monomial_of_three {y : U ≃ₗ[ZMod p] U} {w : U}
    (hy : IsRefl p y) (hw : w ∈ HardMathSupport.Kantor79.movedSpace y) (hw0 : w ≠ 0)
    (h3 : 3 ≤ (Finset.univ.filter (fun i : Fin 4 => f.repr w i ≠ 0)).card) :
    ¬ ∀ i, ∃ j, ∃ x : ZMod p, y (f i) = x • f j := by
  intro hmono
  set φ : Module.End (ZMod p) U := (y : U →ₗ[ZMod p] U) - 1 with hφ
  have hspan : HardMathSupport.Kantor79.movedSpace y = Submodule.span (ZMod p) {w} := by
    rw [HardMathSupport.Kantor79.movedSpace, ← hφ]
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le]; rintro v rfl; exact hw
    · rw [finrank_span_singleton hw0, hφ]
      change 1 = Module.finrank (ZMod p) ↥(LinearMap.range ((↑y : U →ₗ[ZMod p] U) - LinearMap.id))
      exact hy.2.symm
  refine zs4f_false_of_fix_basis (f := f) hy fun i => ?_
  obtain ⟨j, x, hx⟩ := hmono i
  have hmem : φ (f i) ∈ Submodule.span (ZMod p) {w} := by
    rw [← hspan]; exact ⟨f i, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hφi : φ (f i) = y (f i) - f i := by
    rw [hφ]; simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
  by_cases hcne : c = 0
  · rw [hcne, zero_smul, hφi] at hc
    exact sub_eq_zero.mp hc.symm
  · have hcw : c • w = x • f j - f i := by rw [hc, hφi, hx]
    exact absurd hcw (zs4f_smul_ne_sub h3 hcne)

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_repr_apply {g : U ≃ₗ[ZMod p] U} {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hg : LinearMap.toMatrix f f g.toLinearMap = M) (w : U) :
    ⇑(f.repr (g w)) = Matrix.mulVec M ⇑(f.repr w) := by
  subst hg
  exact (LinearMap.toMatrix_mulVec_repr f f g.toLinearMap w).symm

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_toMatrix_diag (h : NFourData f t a b c d G) :
    LinearMap.toMatrix f f (c * a).toLinearMap = Matrix.diagonal ![t, t⁻¹, 1, 1] ∧
      LinearMap.toMatrix f f (b * (c * a) * b).toLinearMap = Matrix.diagonal ![t, 1, t⁻¹, 1] ∧
      LinearMap.toMatrix f f (a * (b * (c * a) * b) * a).toLinearMap =
        Matrix.diagonal ![1, t, t⁻¹, 1] := by
  have hm : ∀ x y : U ≃ₗ[ZMod p] U, LinearMap.toMatrix f f (x * y).toLinearMap =
      LinearMap.toMatrix f f x.toLinearMap * LinearMap.toMatrix f f y.toLinearMap :=
    fun x y => by rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have h1 : LinearMap.toMatrix f f (c * a).toLinearMap = Matrix.diagonal ![t, t⁻¹, 1, 1] := by
    rw [hm, h.toMatrix_c, h.toMatrix_a]; exact zs4f_mat_ca t
  have h2 : LinearMap.toMatrix f f (b * (c * a) * b).toLinearMap =
      Matrix.diagonal ![t, 1, t⁻¹, 1] := by
    rw [hm, hm, h.toMatrix_b, h1]; exact zs4f_mat_bcab t
  exact ⟨h1, h2, by rw [hm, hm, h.toMatrix_a, h2]; exact zs4f_mat_abcaba t⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_exists_good (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {w : U} (hw0 : w ≠ 0) :
    ∃ g ∈ basisClosure f (weylN4Mats t), zs4fGood ⇑(f.repr (g w)) := by
  have haW : a ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_a])
  have hbW : b ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_b])
  have hcW : c ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_c])
  have hdW : d ∈ basisClosure f (weylN4Mats t) :=
    Subgroup.subset_closure (by simp [weylN4Mats, hd])
  have key : ∀ δ ∈ basisClosure f (weylN4Mats t), ∀ l : Fin 4 → ZMod p,
      LinearMap.toMatrix f f δ.toLinearMap = Matrix.diagonal l →
      zs4fGood (Matrix.mulVec (halfOnesMat 4) (l * ⇑(f.repr w))) →
      ∃ g ∈ basisClosure f (weylN4Mats t), zs4fGood ⇑(f.repr (g w)) := fun δ hδ l hl hg =>
    ⟨d * δ, mul_mem hdW hδ, by
      rwa [LinearEquiv.mul_apply, zs4f_repr_apply hd, zs4f_repr_apply hl, zs4f_diagonal_mulVec]⟩
  obtain ⟨h1, h2, h3⟩ := zs4f_toMatrix_diag h
  have hca := mul_mem hcW haW
  have hbcab := mul_mem (mul_mem hbW hca) hbW
  rcases zs4f_alg hp h.sq_t (u := ⇑(f.repr w)) (fun h0 =>
      hw0 (f.repr.map_eq_zero_iff.mp (Finsupp.coe_eq_zero.mp h0))) with h0 | h0 | h0 | h0 | h0
  · exact ⟨1, one_mem _, by simpa using h0⟩
  · exact ⟨d, hdW, by rwa [zs4f_repr_apply hd]⟩
  · exact key _ hca _ h1 h0
  · exact key _ hbcab _ h2 h0
  · exact key _ (mul_mem (mul_mem haW hbcab) haW) _ h3 h0

private theorem zs4f_nFourData_conj (h : NFourData f t a b c d G)
    {g x : U ≃ₗ[ZMod p] U} (hgG : g ∈ G) (hxG : x ∈ G) (hx : IsRefl p x) {w : U}
    (hw : w ∈ HardMathSupport.Kantor79.movedSpace x) (hw0 : w ≠ 0)
    (hgood : zs4fGood ⇑(f.repr (g w))) : NFourData f t a b c (g * x * g⁻¹) G := by
  have hy : IsRefl p (g * x * g⁻¹) := IsRefl.conj hx g
  have hgw : g w ∈ HardMathSupport.Kantor79.movedSpace (g * x * g⁻¹) :=
    zs4f_movedSpace_conj hw
  exact { sq_t := h.sq_t, toMatrix_a := h.toMatrix_a, toMatrix_b := h.toMatrix_b,
          toMatrix_c := h.toMatrix_c, a_mem := h.a_mem, b_mem := h.b_mem, c_mem := h.c_mem,
          d_mem := G.mul_mem (G.mul_mem hgG hxG) (G.inv_mem hgG), isRefl_d := hy,
          not_monomial := zs4f_not_monomial_of_three hy hgw (g.map_ne_zero_iff.mpr hw0)
            hgood.1,
          not_le := zs4f_not_le_of_coord hgw hgood.2,
          transvectionFree := h.transvectionFree, dmax := h.dmax, no336 := h.no336 }

omit [Module.Finite (ZMod p) U] in
private theorem zs4f_closure_abc_le (h : NFourData f t a b c d G) :
    Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) ≤ basisClosure f (weylN4Mats t) := by
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_a])
  · exact Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_b])
  · exact Subgroup.subset_closure (by simp [weylN4Mats, h.toMatrix_c])

theorem exists_conj_nFourData (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) (hx : IsRefl p x) :
    ∃ g ∈ basisClosure f (weylN4Mats t), NFourData f t a b c (g * x * g⁻¹) G := by
  have hne : HardMathSupport.Kantor79.movedSpace x ≠ ⊥ := fun hbot => by
    have h1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 1 := hx.2
    rw [hbot, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨g, hg, hgood⟩ := zs4f_exists_good hp h hd hw0
  exact ⟨g, hg, zs4f_nFourData_conj h (weylN4_le h hd hg) hxG hx hw hw0 hgood⟩

theorem mem_weylEN4 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) {x : U ≃ₗ[ZMod p] U}
    (hxG : x ∈ G) (hx : IsRefl p x) :
    x ∈ basisClosure f (weylEN4Mats t) ∧ (x ∉ basisClosure f (weylN4Mats t) →
      ∃ D ∈ G, LinearMap.toMatrix f f D.toLinearMap = diagSignMat 3) := by
  have hWE : basisClosure f (weylN4Mats t) ≤ basisClosure f (weylEN4Mats t) :=
    Subgroup.closure_mono fun y hy => Set.mem_insert_of_mem (diagSignMat 3) hy
  obtain ⟨g, hgW, hNF⟩ := exists_conj_nFourData hp h hd hxG hx
  obtain ⟨k, hk, hcase⟩ := nFourStar hp hNF
  have hkG : k ∈ G := weylN4_le h hd (zs4f_closure_abc_le h hk)
  have hkg : k * g ∈ basisClosure f (weylN4Mats t) := mul_mem (zs4f_closure_abc_le h hk) hgW
  have hzG : k * (g * x * g⁻¹) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hkG hNF.d_mem) (G.inv_mem hkG)
  have hz : IsRefl p (k * (g * x * g⁻¹) * k⁻¹) := IsRefl.conj hNF.isRefl_d k
  have hR : k * (g * x * g⁻¹) * k⁻¹ ∈ basisClosure f (weylEN4Mats t) ∧
      (k * (g * x * g⁻¹) * k⁻¹ ∉ basisClosure f (weylN4Mats t) →
        ∃ D ∈ G, LinearMap.toMatrix f f D.toLinearMap = diagSignMat 3) := by
    rcases hcase with ⟨ha, hb, hc⟩ | ⟨hb, hc, ha⟩
    · exact mem_weylEN4_of_commute_ab hp h hd hzG hz ha hb hc
    · exact mem_weylEN4_of_commute_bc hp h hd hzG hz hb hc ha
  have hx_eq : x = (k * g)⁻¹ * (k * (g * x * g⁻¹) * k⁻¹) * (k * g) := by group
  refine ⟨?_, fun hxN => hR.2 fun hzW => hxN ?_⟩
  · rw [hx_eq]; exact mul_mem (mul_mem (inv_mem (hWE hkg)) hR.1) (hWE hkg)
  · rw [hx_eq]; exact mul_mem (mul_mem (inv_mem hkg) hzW) hkg

theorem le_weylEN4 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) (hG : ReflGen p G) :
    G ≤ basisClosure f (weylEN4Mats t) := by
  rw [hG]
  exact (Subgroup.closure_le _).mpr (fun x hx => (mem_weylEN4 hp h hd hx.1 hx.2).1)

theorem eq_weylN4_or_eq_weylEN4 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hd : LinearMap.toMatrix f f d.toLinearMap = halfOnesMat 4) (hG : ReflGen p G) :
    G = basisClosure f (weylN4Mats t) ∨ G = basisClosure f (weylEN4Mats t) := by
  have hle := le_weylEN4 hp h hd hG
  have hWN : basisClosure f (weylN4Mats t) ≤ G := weylN4_le h hd
  by_cases hcase : ∃ x ∈ G, IsRefl p x ∧ x ∉ basisClosure f (weylN4Mats t)
  · right
    obtain ⟨x, hxG, hxr, hxN⟩ := hcase
    obtain ⟨D, hDG, hDmat⟩ := (mem_weylEN4 hp h hd hxG hxr).2 hxN
    obtain ⟨P, hPcl, hPmat⟩ := zs4f_pi34_mem hp f h.sq_t
    have hPG : P ∈ G := hWN hPcl
    have hrG : P * D * P ∈ G := Subgroup.mul_mem _ (Subgroup.mul_mem _ hPG hDG) hPG
    have hrmat : LinearMap.toMatrix f f (P * D * P).toLinearMap = diagSignMat 2 := by
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul,
        LinearMap.toMatrix_mul, hPmat, hDmat]
      exact zs4f_pij34_diagSign_conj
    exact le_antisymm hle (weylEN4_le_of_diagSign_mem hp f h.sq_t hWN hrG hrmat)
  · left
    apply le_antisymm ?_ hWN
    rw [hG]
    exact (Subgroup.closure_le _).mpr (fun x hx => by
      by_contra hxN
      exact hcase ⟨x, hx.1, hx.2, hxN⟩)

end NFourData

end CFSG.StandardType.ZS

end
