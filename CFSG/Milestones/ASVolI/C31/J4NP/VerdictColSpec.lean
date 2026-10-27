module

public import Certificates.Data.CFSGNative.J4Tree.Verdict
public import CFSG.Sporadic.J4.QT2LocGenLem
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.J4.QT2AGen
public import CFSG.Sporadic.J4.QTProof
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
open CFSG.J4Tree.Native CFSG.J4Tree.Native.Col
open scoped Matrix

theorem burnsideJ4NP_col_eta_congr {G : Type*} [Group G] (u : ℕ → G) {k c d : ℕ}
    (h : ∀ j < k, c.testBit j = d.testBit j) : eta u k c = eta u k d := by
  induction k with
  | zero => simp [eta]
  | succ k ih =>
    rw [eta_succ, eta_succ, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

@[expose] noncomputable def burnsideJ4NP_colLab (x : J) : ℕ := QT2.fixDim (Mx x)

@[expose] noncomputable def burnsideJ4NP_colPair (x w : J) : ℕ :=
  QT2.fixDim ((Mx x - 1) * (Mx w - 1) + 1)

theorem burnsideJ4NP_col_Mx_conj (g x : J) :
    Mx (g * x * g⁻¹) = Mx g * Mx x * Mx g⁻¹ := by
  rw [map_mul, map_mul]

theorem burnsideJ4NP_col_Mx_mul_inv (g : J) : Mx g * Mx g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem burnsideJ4NP_col_Mx_inv_mul (g : J) : Mx g⁻¹ * Mx g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem burnsideJ4NP_colPair_conj (g x w : J) :
    burnsideJ4NP_colPair (g * x * g⁻¹) (g * w * g⁻¹) = burnsideJ4NP_colPair x w := by
  unfold burnsideJ4NP_colPair
  rw [burnsideJ4NP_col_Mx_conj, burnsideJ4NP_col_Mx_conj]
  set P := Mx g
  set Q := Mx g⁻¹
  have hPQ : P * Q = 1 := burnsideJ4NP_col_Mx_mul_inv g
  have hQP : Q * P = 1 := burnsideJ4NP_col_Mx_inv_mul g
  have e : (P * Mx x * Q - 1) * (P * Mx w * Q - 1) + 1 =
      P * ((Mx x - 1) * (Mx w - 1) + 1) * Q := by
    have e1 : P * Mx x * Q - 1 = P * (Mx x - 1) * Q := by
      rw [mul_sub, sub_mul, mul_one, hPQ]
    have e2 : P * Mx w * Q - 1 = P * (Mx w - 1) * Q := by
      rw [mul_sub, sub_mul, mul_one, hPQ]
    rw [e1, e2]
    calc P * (Mx x - 1) * Q * (P * (Mx w - 1) * Q) + 1
        = P * (Mx x - 1) * (Q * P) * (Mx w - 1) * Q + P * Q := by
          rw [hPQ]; simp only [Matrix.mul_assoc]
      _ = P * ((Mx x - 1) * (Mx w - 1) + 1) * Q := by
          rw [hQP, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e]
  exact QT2.fixDim_conj _ _ hPQ hQP _

end CFSG.ASVolI
