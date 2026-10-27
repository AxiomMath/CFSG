module

public import CFSG.Sporadic.J4.QTOutCoc
public import CFSG.Sporadic.J4.QTOutLin
public import CFSG.Sporadic.J4.QTOutObsCheck

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native Matrix

noncomputable def yJ : J := b * a * b⁻¹

section Obs

variable (hM : MatFacts)
include hM

theorem Mx_yJ : Mx yJ = rowsMatrix yRows := by
  unfold yJ yRows
  rw [map_mul, map_mul, Mx_b hM, Mx_a hM, Mx_b_inv hM, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem yJ_sq : yJ * yJ = 1 := by
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 obs_y_sq)
  rw [rowsMatrix_mulRows, rowsMatrix_idRows, ← Mx_yJ hM] at this
  rw [map_mul, map_one]
  exact this

theorem yJ_conj : yJ * eta uJ 11 cA * yJ = eta uJ 11 cB * wordProd xJ wObs := by
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 obs_conj)
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows] at this
  rw [map_mul, map_mul, map_mul, Mx_yJ hM, Mx_etaR hM, Mx_etaR hM, Mx_wordProd hM]
  exact this

omit hM in
theorem no_delta_class (hF : J4Facts) (β : MulAut J)
    (hfix : ∀ c < 2 ^ 11, β (eta uJ 11 c) = eta uJ 11 c) (h0 : β (xJ 0) = xJ 0)
    (h1 : β (xJ 1) = eta uJ 11 1373 * xJ 1) (h2 : β (xJ 2) = eta uJ 11 689 * xJ 2) : False := by
  have hM := hF.mat
  have h0' : β (xJ 0) = eta uJ 11 0 * xJ 0 := by rw [eta_zero, one_mul]; exact h0
  have hw : β (wordProd xJ wObs) = eta uJ 11 aObs * wordProd xJ wObs :=
    alpha_word hM β h0' h1 h2 obs_letters
  have hconj := yJ_conj hM
  have hysq := yJ_sq hM
  obtain ⟨hAlt, hBlt⟩ := obs_lt
  have e1 : β yJ * eta uJ 11 cA * β yJ = eta uJ 11 (cB ^^^ aObs) * wordProd xJ wObs := by
    have h := congrArg β hconj
    rw [map_mul, map_mul, map_mul, hfix cA hAlt, hfix cB hBlt, hw] at h
    rw [h, eta_xor (elem_uJ hM) le_rfl, mul_assoc]
  have hy'sq : β yJ * β yJ = 1 := by rw [← map_mul, hysq, map_one]
  have e2 : β yJ * (eta uJ 11 (cB ^^^ aObs) * wordProd xJ wObs) = eta uJ 11 cA * β yJ := by
    rw [← e1]
    calc β yJ * (β yJ * eta uJ 11 cA * β yJ) = (β yJ * β yJ) * eta uJ 11 cA * β yJ := by group
      _ = eta uJ 11 cA * β yJ := by rw [hy'sq]; group
  have hG : Mx (eta uJ 11 (cB ^^^ aObs) * wordProd xJ wObs) = rowsMatrix gRows := by
    rw [map_mul, Mx_etaR hM, Mx_wordProd hM, gRows, hRows, rowsMatrix_mulRows]
    rfl
  have hE : Mx (eta uJ 11 cA) = rowsMatrix e5Rows := Mx_etaR hM cA
  have hZ : Mx (β yJ) * Mx (β yJ) = 1 := by rw [← map_mul, hy'sq, map_one]
  have hcomm : Mx (β yJ) * rowsMatrix gRows = rowsMatrix e5Rows * Mx (β yJ) := by
    rw [← hG, ← hE, ← map_mul, ← map_mul, e2]
  have hfs : ∀ k : Fin fvs.size, ((fvs[k.val]!).toVec) ᵥ* rowsMatrix e5Rows = (fvs[k.val]!).toVec := by
    intro k
    have hmem : fvs[k.val]! ∈ fvs := by simp [k.isLt]
    have := V2.beq_iff.1 (obs_fixed _ hmem)
    rw [← frApply_toVec_eq_vecMul, this]
  have hxs : ∀ k : Fin ximgs.size,
      ((xvs[k.val]!).toVec) ᵥ* (rowsMatrix gRows - 1) = (ximgs[k.val]!).toVec := by
    intro k
    have hk : k.val < xvs.size := by
      have := k.isLt
      simpa [ximgs] using this
    have hx : ximgs[k.val]! = (frApply (frTable gRows) (xvs[k.val]!)).xor (xvs[k.val]!) := by
      simp [ximgs, hk]
    rw [hx, V2.toVec_xor, frApply_toVec_eq_vecMul, Matrix.vecMul_sub, Matrix.vecMul_one]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply]
    generalize ((xvs[k.val]!).toVec ᵥ* rowsMatrix gRows) j = a
    generalize (xvs[k.val]!).toVec j = c
    revert a c
    decide
  have hxi : IndepF (fun k : Fin ximgs.size => ((xvs[k.val]!).toVec) ᵥ* (rowsMatrix gRows - 1)) := by
    have : (fun k : Fin ximgs.size => ((xvs[k.val]!).toVec) ᵥ* (rowsMatrix gRows - 1)) =
        fun k : Fin ximgs.size => (ximgs[k.val]!).toVec := funext hxs
    rw [this]
    exact tri_indep obs_tri_x
  have hab : 112 < fvs.size + ximgs.size := by
    have h1 := obs_sizes
    have h2 : ximgs.size = xvs.size := by simp [ximgs]
    omega
  exact rank_obstruction (E := rowsMatrix e5Rows) (G := rowsMatrix gRows) (Z := Mx (β yJ))
    (Zi := Mx (β yJ)) hZ hcomm (fun k : Fin fvs.size => (fvs[k.val]!).toVec)
    (fun k : Fin ximgs.size => (xvs[k.val]!).toVec) hfs (tri_indep obs_tri_f) hxi hab

end Obs

end CFSG.Sporadic.J4.QT
