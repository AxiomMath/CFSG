module

public import CFSG.Quasithin.H13.NQCatJ4Rank
public import CFSG.Sporadic.J4.QT2LocGenLem
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
public import CFSG.Sporadic.J4
public import Certificates.Certificate7852

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open Matrix

theorem burnsideJ4NP_rowsMatrix_natRows (R : Array V2) :
    CFSG.Sporadic.SmallF2.rowsMatrix 112 (burnsideJ4NP_natRows R) = rowsMatrix R := by
  ext i j
  rw [CFSG.Sporadic.SmallF2.rowsMatrix_apply, rowsMatrix_apply,
    CFSG.Sporadic.SmallF2.toVecD_apply, V2.toVec_apply]
  have h : (burnsideJ4NP_natRows R)[i.val]?.getD 0 = (R[i.val]?.getD V2.zero).toNat := by
    unfold burnsideJ4NP_natRows
    rw [Array.getElem?_map]
    cases R[i.val]? with
    | none => simp [V2.toNat, V2.zero]
    | some v => rfl
  have hj : j.val < 128 := by have := j.isLt; omega
  rw [h, V2.testBit_toNat _ hj]

theorem burnsideJ4NP_fixDim_eq_finrank (A : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    QT2.fixDim A = Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (Aᵀ - 1))) := by
  have e : Matrix.vecMulLinear (A - 1) = Matrix.mulVecLin (Aᵀ - 1) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.vecMulLinear_apply, Matrix.mulVecLin_apply,
      show Aᵀ - 1 = (A - 1)ᵀ by rw [Matrix.transpose_sub, Matrix.transpose_one],
      Matrix.mulVec_transpose]
  unfold QT2.fixDim QT2.fixPhi
  rw [e]

theorem burnsideJ4NP_fixDim_of_rowFixOK {R : Array V2} {k : ℕ}
    (h : burnsideJ4NP_rowFixOK R k = true) : QT2.fixDim (rowsMatrix R) = k := by
  have h1 := CFSG.Quasithin.H13.NQCat.finrank_ker_of_fixDimOK h
  rw [burnsideJ4NP_rowsMatrix_natRows, rowsMatrix_transposeRows] at h1
  rw [burnsideJ4NP_fixDim_eq_finrank]
  exact h1

theorem burnsideJ4NP_fixOK_spec :
    burnsideJ4NP_rowFixOK (etaR 1) 56 = true ∧ burnsideJ4NP_rowFixOK (etaR 1131) 62 = true := by
  have h := Certificates.certificate7852
  unfold burnsideJ4NP_fixOK burnsideJ4NP_fixOKOf at h
  exact Bool.and_eq_true_iff.1 h

theorem burnsideJ4NP_fixDim_eta_one :
    QT2.fixDim (Mx (eta uJ 11 1)) = 56 := by
  rw [Mx_etaR j4Facts.mat]
  exact burnsideJ4NP_fixDim_of_rowFixOK burnsideJ4NP_fixOK_spec.1

theorem burnsideJ4NP_fixDim_z0 :
    QT2.fixDim (Mx CFSG.Quasithin.J4Loc.z0) = 62 := by
  rw [CFSG.Quasithin.J4Loc.z0, Mx_etaR j4Facts.mat]
  exact burnsideJ4NP_fixDim_of_rowFixOK burnsideJ4NP_fixOK_spec.2

theorem burnsideJ4NP_fixDim_conj (g x : J) :
    QT2.fixDim (Mx (g * x * g⁻¹)) = QT2.fixDim (Mx x) := by
  rw [map_mul, map_mul]
  refine QT2.fixDim_conj (Mx g) (Mx g⁻¹) ?_ ?_ (Mx x)
  · rw [← map_mul, mul_inv_cancel, map_one]
  · rw [← map_mul, inv_mul_cancel, map_one]

theorem burnsideJ4NP_not_isConj_eta_one_z0 :
    ¬ IsConj (eta uJ 11 1) CFSG.Quasithin.J4Loc.z0 := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  have h1 := burnsideJ4NP_fixDim_conj g (eta uJ 11 1)
  rw [hg, burnsideJ4NP_fixDim_z0, burnsideJ4NP_fixDim_eta_one] at h1
  omega

end CFSG.ASVolI
