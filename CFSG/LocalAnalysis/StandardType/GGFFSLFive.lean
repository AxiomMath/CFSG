module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFL6Cent
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFL7Cent
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
import CFSG.GH74.GLS.Balance.SolvAPIDefs
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
import CFSG.Walter.J1Props
import Certificates.Certificate8166

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open Matrix

private theorem pow_five_two : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A ^ 5 = 1 → A = 1 := by
  decide +kernel

private theorem pow_five_three : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A ^ 5 = 1 → A = 1 := by
  decide +kernel

private def rc : Fin 4 → Matrix (Fin 2) (Fin 2) (ZMod 2) := ![0, 1, rhoM, rhoM * rhoM]

private theorem four_five_check (i j k l : Fin 4) :
    (fromBlocks (rc i) (rc j) (rc k) (rc l) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) ^ 5 = 1 →
      fromBlocks (rc i) (rc j) (rc k) (rc l) * fromBlocks rhoM 0 0 1 =
        fromBlocks rhoM 0 0 1 * fromBlocks (rc i) (rc j) (rc k) (rc l) →
        rc i = 1 ∧ rc j = 0 ∧ rc k = 0 ∧ rc l = 1 := by
  decide +kernel +revert

private theorem four_five_pow {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hX : X * fromBlocks rhoM 0 0 rhoM = fromBlocks rhoM 0 0 rhoM * X)
    (hX1 : X * fromBlocks rhoM 0 0 1 = fromBlocks rhoM 0 0 1 * X) (h5 : X ^ 5 = 1) :
    X = 1 := by
  obtain ⟨P, Q, R, T, rfl⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) (ZMod 2),
      X = fromBlocks P Q R T := ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hX
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp hX
  have hidx : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 2), B * rhoM = rhoM * B →
      ∃ i : Fin 4, rc i = B := by
    decide +kernel
  obtain ⟨i, rfl⟩ := hidx P h1
  obtain ⟨j, rfl⟩ := hidx Q h2
  obtain ⟨k, rfl⟩ := hidx R h3
  obtain ⟨l, rfl⟩ := hidx T h4
  obtain ⟨hi, hj, hk, hl⟩ := four_five_check i j k l h5 hX1
  rw [hi, hj, hk, hl]
  exact fromBlocks_one

private theorem pow_five_of_coe {n : ℕ} {x : SL(n, ZMod 2)}
    {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hx : (x : Matrix (Fin n) (Fin n) (ZMod 2)) = A) (h : A ^ 5 = 1) : x ^ 5 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hx]
  exact congrFun (congrFun h i) j

private theorem mul_eq_mul_of_coe {n : ℕ} {x y : SL(n, ZMod 2)}
    {A B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hx : (x : Matrix (Fin n) (Fin n) (ZMod 2)) = A)
    (hy : (y : Matrix (Fin n) (Fin n) (ZMod 2)) = B) (h : A * B = B * A) :
    x * y = y * x := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy]
  exact congrFun (congrFun h i) j

private theorem t1M_mul_t2M_six : W6.t1M * W6.t2M = L6.r2M := by decide +kernel

private theorem bl_t1M_split2 :
    bl L6.split2 W6.t1M = fromBlocks 1 0 0 (fromBlocks rhoM 0 0 1) := by decide +kernel

theorem no_five_SL6 : ∀ x : SL(6, ZMod 2), x ^ 5 = 1 → x * W6.T 0 = W6.T 0 * x →
    x * W6.T 1 = W6.T 1 * x → x = 1 := by
  intro x h5 h0 h1
  set X : Matrix (Fin 6) (Fin 6) (ZMod 2) := (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hX
  have hX5 : X ^ 5 = 1 := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h5
    simpa [hX] using h
  have h0m : X * W6.t1M = W6.t1M * X := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h0
    simpa [hX, W6.coe_T, Matrix.SpecialLinearGroup.coe_mul] using h
  have h1m : X * W6.t2M = W6.t2M * X := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h1
    simpa [hX, W6.coe_T, Matrix.SpecialLinearGroup.coe_mul] using h
  have h2m : X * L6.r2M = L6.r2M * X := by
    rw [← t1M_mul_t2M_six]
    calc X * (W6.t1M * W6.t2M) = (X * W6.t1M) * W6.t2M := by rw [Matrix.mul_assoc]
      _ = (W6.t1M * X) * W6.t2M := by rw [h0m]
      _ = W6.t1M * (X * W6.t2M) := by rw [Matrix.mul_assoc]
      _ = W6.t1M * (W6.t2M * X) := by rw [h1m]
      _ = (W6.t1M * W6.t2M) * X := by rw [Matrix.mul_assoc]
  have hE : X * (L6.r2M + L6.r2M ^ 2) = (L6.r2M + L6.r2M ^ 2) * X := by
    rw [Matrix.mul_add, Matrix.add_mul, h2m,
      (Commute.pow_right (show Commute X L6.r2M from h2m) 2).eq]
  have hbd : IsBlockDiag (bl L6.split2 X) :=
    isBlockDiag_of_commute (by rw [← L6.bl_r2_add_sq, ← bl_mul, ← bl_mul, hE])
  obtain ⟨X2, X4, hXeq⟩ : ∃ (X2 : Matrix (Fin 2) (Fin 2) (ZMod 2))
      (X4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)),
      bl L6.split2 X = fromBlocks X2 0 0 X4 :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag hbd⟩
  have hpow : fromBlocks (X2 ^ 5) 0 0 (X4 ^ 5) = fromBlocks 1 0 0 1 := by
    rw [fromBlocks_one, ← fromBlocks_diag_pow, ← hXeq, ← bl_pow, hX5, bl_one]
  have hX2 : X2 ^ 5 = 1 := (fromBlocks_inj.mp hpow).1
  have hX4 : X4 ^ 5 = 1 := (fromBlocks_inj.mp hpow).2.2.2
  have h4comm : X4 * fromBlocks rhoM 0 0 rhoM = fromBlocks rhoM 0 0 rhoM * X4 := by
    have h := bl_commute L6.split2 h2m
    rw [hXeq, L6.bl_r2M, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have h4comm1 : X4 * fromBlocks rhoM 0 0 1 = fromBlocks rhoM 0 0 1 * X4 := by
    have h := bl_commute L6.split2 h0m
    rw [hXeq, bl_t1M_split2, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have hX2one : X2 = 1 := pow_five_two X2 hX2
  have hX4one : X4 = 1 := four_five_pow h4comm h4comm1 hX4
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hX]
  apply bl_injective L6.split2
  rw [hXeq, hX2one, hX4one, bl_one, fromBlocks_one]

private def xM6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

private def xMi6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0]

private theorem xM6_mul_xMi6 : xM6 * xMi6 = 1 := by decide +kernel

private theorem xM6_pow_five : xM6 ^ 5 = 1 := by decide +kernel

private theorem xM6_ne_one : xM6 ≠ 1 := by decide +kernel

private theorem xM6_comm_t1 : xM6 * W6.t1M = W6.t1M * xM6 := by decide +kernel

private theorem xM6_comm_t2t3 : xM6 * (W6.t2M * W6.t3M) = W6.t2M * W6.t3M * xM6 := by
  decide +kernel

theorem five_SL6 : ∃ x : SL(6, ZMod 2), x ≠ 1 ∧ x ^ 5 = 1 ∧ x * W6.T 0 = W6.T 0 * x ∧
    x * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * x := by
  refine ⟨(W6.mkSL6 xM6 xMi6 xM6_mul_xMi6 : SL(6, ZMod 2)), ?_, ?_, ?_, ?_⟩
  · intro hx
    exact xM6_ne_one (by
      have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hx
      rw [Matrix.SpecialLinearGroup.coe_one] at h
      exact h)
  · exact pow_five_of_coe (x := (W6.mkSL6 xM6 xMi6 xM6_mul_xMi6 : SL(6, ZMod 2)))
      rfl xM6_pow_five
  · exact mul_eq_mul_of_coe (x := (W6.mkSL6 xM6 xMi6 xM6_mul_xMi6 : SL(6, ZMod 2)))
      (y := W6.T 0) rfl (W6.coe_T 0) xM6_comm_t1
  · exact mul_eq_mul_of_coe (x := (W6.mkSL6 xM6 xMi6 xM6_mul_xMi6 : SL(6, ZMod 2)))
      (y := W6.T 1 * W6.T 2) rfl
      (by
        rw [Matrix.SpecialLinearGroup.coe_mul, W6.coe_T 1, W6.coe_T 2]
        rfl) xM6_comm_t2t3

private theorem t1M_mul_t2M_seven : W7.t1M * W7.t2M = L7.r2M := by decide +kernel

private def e7 : Fin 7 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 3 :=
  L7.e42.trans (Equiv.sumCongr ((finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm)
    (Equiv.refl (Fin 3)))

private theorem bl_r2_e7 :
    bl e7 L7.r2M = fromBlocks (fromBlocks rhoM 0 0 rhoM) 0 0 1 := by decide +kernel

private theorem bl_t1_e7 :
    bl e7 W7.t1M = fromBlocks (fromBlocks rhoM 0 0 1) 0 0 1 := by decide +kernel

private theorem bl_P_e7 :
    bl e7 ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + L7.r2M + L7.r2M * L7.r2M) =
      fromBlocks 0 0 0 1 := by decide +kernel

theorem no_five_SL7 : ∀ x : SL(7, ZMod 2), x ^ 5 = 1 → x * W7.T 0 = W7.T 0 * x →
    x * W7.T 1 = W7.T 1 * x → x = 1 := by
  intro x h5 h0 h1
  set X : Matrix (Fin 7) (Fin 7) (ZMod 2) := (x : Matrix (Fin 7) (Fin 7) (ZMod 2)) with hX
  have hX5 : X ^ 5 = 1 := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h5
    simpa [hX] using h
  have h0m : X * W7.t1M = W7.t1M * X := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h0
    simpa [hX, W7.coe_T, Matrix.SpecialLinearGroup.coe_mul] using h
  have h1m : X * W7.t2M = W7.t2M * X := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h1
    simpa [hX, W7.coe_T, Matrix.SpecialLinearGroup.coe_mul] using h
  have h2m : X * L7.r2M = L7.r2M * X := by
    rw [← t1M_mul_t2M_seven]
    calc X * (W7.t1M * W7.t2M) = (X * W7.t1M) * W7.t2M := by rw [Matrix.mul_assoc]
      _ = (W7.t1M * X) * W7.t2M := by rw [h0m]
      _ = W7.t1M * (X * W7.t2M) := by rw [Matrix.mul_assoc]
      _ = W7.t1M * (W7.t2M * X) := by rw [h1m]
      _ = (W7.t1M * W7.t2M) * X := by rw [Matrix.mul_assoc]
  have hc : Commute X L7.r2M := h2m
  have hP : Commute X ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + L7.r2M + L7.r2M * L7.r2M) :=
    ((Commute.one_right X).add_right hc).add_right (hc.mul_right hc)
  have hbd : IsBlockDiag (bl e7 X) :=
    isBlockDiag_of_commute (by rw [← bl_P_e7, ← bl_mul, ← bl_mul, hP.eq])
  obtain ⟨X4, X3, hXeq⟩ : ∃ (X4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
      (X3 : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      bl e7 X = fromBlocks X4 0 0 X3 :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag hbd⟩
  have hpow : fromBlocks (X4 ^ 5) 0 0 (X3 ^ 5) = fromBlocks 1 0 0 1 := by
    rw [fromBlocks_one, ← fromBlocks_diag_pow, ← hXeq, ← bl_pow, hX5, bl_one]
  have hX4 : X4 ^ 5 = 1 := (fromBlocks_inj.mp hpow).1
  have hX3 : X3 ^ 5 = 1 := (fromBlocks_inj.mp hpow).2.2.2
  have h4comm : X4 * fromBlocks rhoM 0 0 rhoM = fromBlocks rhoM 0 0 rhoM * X4 := by
    have h := bl_commute e7 h2m
    rw [hXeq, bl_r2_e7, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).1
  have h4comm1 : X4 * fromBlocks rhoM 0 0 1 = fromBlocks rhoM 0 0 1 * X4 := by
    have h := bl_commute e7 h0m
    rw [hXeq, bl_t1_e7, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).1
  have hX4one : X4 = 1 := four_five_pow h4comm h4comm1 hX4
  have hX3one : X3 = 1 := pow_five_three X3 hX3
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hX]
  apply bl_injective e7
  rw [hXeq, hX4one, hX3one, bl_one, fromBlocks_one]

private def xM7 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 1, 0, 0, 1, 0;
     0, 0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

private def xMi7 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 1, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1]

private theorem xM7_mul_xMi7 : xM7 * xMi7 = 1 := by decide +kernel

private theorem xM7_pow_five : xM7 ^ 5 = 1 := by decide +kernel

private theorem xM7_ne_one : xM7 ≠ 1 := by decide +kernel

private theorem xM7_comm_t1 : xM7 * W7.t1M = W7.t1M * xM7 := by decide +kernel

private theorem xM7_comm_t2t3 : xM7 * (W7.t2M * W7.t3M) = W7.t2M * W7.t3M * xM7 := by
  decide +kernel

theorem five_SL7 : ∃ x : SL(7, ZMod 2), x ≠ 1 ∧ x ^ 5 = 1 ∧ x * W7.T 0 = W7.T 0 * x ∧
    x * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * x := by
  refine ⟨(W7.mkSL7 xM7 xMi7 xM7_mul_xMi7 : SL(7, ZMod 2)), ?_, ?_, ?_, ?_⟩
  · intro hx
    exact xM7_ne_one (by
      have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hx
      rw [Matrix.SpecialLinearGroup.coe_one] at h
      exact h)
  · exact pow_five_of_coe (x := (W7.mkSL7 xM7 xMi7 xM7_mul_xMi7 : SL(7, ZMod 2)))
      rfl xM7_pow_five
  · exact mul_eq_mul_of_coe (x := (W7.mkSL7 xM7 xMi7 xM7_mul_xMi7 : SL(7, ZMod 2)))
      (y := W7.T 0) rfl (W7.coe_T 0) xM7_comm_t1
  · exact mul_eq_mul_of_coe (x := (W7.mkSL7 xM7 xMi7 xM7_mul_xMi7 : SL(7, ZMod 2)))
      (y := W7.T 1 * W7.T 2) rfl
      (by
        rw [Matrix.SpecialLinearGroup.coe_mul, W7.coe_T 1, W7.coe_T 2]
        rfl) xM7_comm_t2t3

end CFSG.StandardType.GGFF

end
