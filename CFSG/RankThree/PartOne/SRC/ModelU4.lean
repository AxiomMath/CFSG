module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.SubgroupLists.RationalElements

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

section Levi4

variable {K : Type} [Field K]

@[expose] def leviMat4 (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem leviMat4_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    leviMat4 (A * B) = leviMat4 A * leviMat4 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat4, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem leviMat4_one : leviMat4 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat4]

@[expose] noncomputable def blockGL4 : GL (Fin 2) K →* GL (Fin 4) K where
  toFun A := ⟨leviMat4 (A : Matrix (Fin 2) (Fin 2) K), leviMat4 ((A⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), by
    rw [← leviMat4_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, leviMat4_one], by
    rw [← leviMat4_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, leviMat4_one]⟩
  map_one' := Units.ext (by simp [leviMat4_one])
  map_mul' A B := Units.ext (by simp [leviMat4_mul])

@[expose] def negDiag4 (K : Type*) [Field K] : GL (Fin 4) K :=
  ⟨diagonal ![-1, -1, 1, 1], diagonal ![-1, -1, 1, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]⟩

theorem coe_negDiag4 : ((negDiag4 K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    diagonal ![-1, -1, 1, 1] :=
  rfl

theorem negDiag4_mem_statedSU {q : ℕ} (hq : Odd q) : negDiag4 K ∈ StatedSU 4 q K := by
  apply Subgroup.subset_closure
  refine ⟨by simp [coe_negDiag4, det_diagonal, Fin.prod_univ_four], ?_⟩
  rw [coe_negDiag4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, diagonal, hq.neg_one_pow, hq.pos.ne']

theorem negDiag4_not_scalar (h2 : (2 : K) ≠ 0) : negDiag4 K ∉ StatedScalars (Fin 4) K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
  have h0 := congrFun (congrFun h 0) 0
  have h2' := congrFun (congrFun h 2) 2
  simp [coe_negDiag4, Matrix.GeneralLinearGroup.coe_scalar, diagonal] at h0 h2'
  have h1 := congrArg Units.val (h0.symm.trans h2')
  simp only [Units.val_neg, Units.val_one] at h1
  apply h2
  linear_combination -h1

end Levi4

section PSU4

variable {K : Type} [Field K]

@[expose] noncomputable def negDiagSU4 {q : ℕ} (hq : Odd q) : StatedSU 4 q K :=
  ⟨negDiag4 K, negDiag4_mem_statedSU hq⟩

@[expose] noncomputable def leviSU4 (q : ℕ) : Subgroup (StatedSU 4 q K) :=
  ((StatedSU 2 q K).map blockGL4).subgroupOf (StatedSU 4 q K)

@[expose] noncomputable def leviPSU4 (q : ℕ) : Subgroup (StatedProj (StatedSU 4 q K)) :=
  (leviSU4 q).map (QuotientGroup.mk' _)

@[expose] noncomputable def negDiagPSU4 {q : ℕ} (hq : Odd q) : StatedProj (StatedSU 4 q K) :=
  QuotientGroup.mk' _ (negDiagSU4 (K := K) hq)

theorem negDiagPSU4_sq {q : ℕ} (hq : Odd q) : negDiagPSU4 (K := K) hq ^ 2 = 1 := by
  rw [negDiagPSU4, ← map_pow]
  rw [show negDiagSU4 (K := K) hq ^ 2 = 1 from Subtype.ext (by
    change negDiag4 K ^ 2 = 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_negDiag4, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, diagonal]), map_one]

theorem negDiagPSU4_ne_one (h2 : (2 : K) ≠ 0) {q : ℕ} (hq : Odd q) :
    negDiagPSU4 (K := K) hq ≠ 1 := by
  intro h
  rw [negDiagPSU4, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  exact negDiag4_not_scalar h2 h

end PSU4

end CFSG.RankThree.PartOne.SRC
