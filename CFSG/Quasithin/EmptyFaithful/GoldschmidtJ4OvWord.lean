module

public import Certificates.Data.J4Ov.Fam
public import CFSG.Sporadic.J4.QT2LocCntProofBase

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

structure RowFam (gs : ℕ → J) (mats invs : Array (Array V2)) : Prop where
  mat : ∀ m, Mx (gs m) = rowsMatrix (mats[m]?.getD idRows)
  inv : ∀ m, Mx ((gs m)⁻¹) = rowsMatrix (invs[m]?.getD idRows)

theorem RowFam.mx_wordProd {gs : ℕ → J} {mats invs : Array (Array V2)}
    (h : RowFam gs mats invs) (w : List ℤ) :
    Mx (wordProd gs w) = rowsMatrix (wordRows mats invs w) := by
  unfold wordRows wordProd
  suffices ∀ (acc : Array V2) (g : J), Mx g = rowsMatrix acc →
      Mx (g * (w.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod) =
        rowsMatrix (w.foldl (fun acc l => mulRows acc (if 0 < l then mats[l.toNat - 1]?.getD idRows
          else invs[(-l).toNat - 1]?.getD idRows)) acc) by
    simpa using this idRows 1 (by rw [map_one, rowsMatrix_idRows])
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih
    rw [map_mul, hg, rowsMatrix_mulRows]
    congr 1
    split_ifs
    · exact h.mat _
    · exact h.inv _


@[expose] noncomputable def uEl (ℓ : ℕ) : J := (pathElt (repPaths.getD ℓ []))⁻¹

theorem uEl_zero : uEl 0 = 1 := by simp [uEl, repPaths, pathElt]

section Mat

variable (hM : MatFacts)
include hM

theorem Mx_kEl {ℓ : ℕ} (hℓ : ℓ < 7) :
    Mx (pathElt (repPaths.getD ℓ [])) = rowsMatrix (kR ℓ) :=
  Mx_pathElt hM _ (repPaths_letters ℓ hℓ)

theorem Mx_uEl {ℓ : ℕ} (hℓ : ℓ < 7) (hinv : eqRows (mulRows (kR ℓ) (uR ℓ)) idRows = true) :
    Mx (uEl ℓ) = rowsMatrix (uR ℓ) := by
  have h1 : Mx (pathElt (repPaths.getD ℓ [])) * rowsMatrix (uR ℓ) = 1 := by
    rw [Mx_kEl hM hℓ]
    have := rowsMatrix_eq_of_eqRows hinv
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have h2 : Mx (uEl ℓ) * Mx (pathElt (repPaths.getD ℓ [])) = 1 := by
    rw [← map_mul, uEl, inv_mul_cancel, map_one]
  calc Mx (uEl ℓ) = Mx (uEl ℓ) * (Mx (pathElt (repPaths.getD ℓ [])) * rowsMatrix (uR ℓ)) := by
        rw [h1, Matrix.mul_one]
    _ = (Mx (uEl ℓ) * Mx (pathElt (repPaths.getD ℓ []))) * rowsMatrix (uR ℓ) := by
        rw [Matrix.mul_assoc]
    _ = rowsMatrix (uR ℓ) := by rw [h2, Matrix.one_mul]

theorem Mx_uEl_inv {ℓ : ℕ} (hℓ : ℓ < 7) : Mx ((uEl ℓ)⁻¹) = rowsMatrix (kR ℓ) := by
  rw [uEl, inv_inv]
  exact Mx_kEl hM hℓ

theorem Mx_xJ' (k : ℕ) : Mx (xJ k) = rowsMatrix ((locMats ())[k]?.getD idRows) :=
  (locMats_spec hM k).symm

theorem Mx_xJ_inv (k : ℕ) : Mx ((xJ k)⁻¹) = rowsMatrix ((locInvs ())[k]?.getD idRows) := by
  rw [Mx_apply, show (((xJ k)⁻¹ : J) : GL (Fin 112) (ZMod 2)) = (locGL k)⁻¹ from rfl,
    ← locInvs_spec hM]

omit hM in
theorem mem_Hj_of_rows_fix (hF : J4Facts) {g : J} {R : Array V2} (hg : Mx g = rowsMatrix R)
    (h : (frApply (frTable R) rootV).beq rootV = true) : g ∈ Hj := by
  have hv : frApply (frTable R) rootV = rootV := V2.beq_iff.1 h
  have h1 : g⁻¹ • w₀ = w₀ := by
    rw [← ofRow_inj, inv_smul_row, ← Mx_apply, hg]
    show rootV.toVec ᵥ* rowsMatrix R = rootV.toVec
    rw [← frApply_toVec_eq_vecMul, hv]
  simpa using Hj.inv_mem (mem_Hj_of_smul_root hF h1)

theorem not_mem_Hj_of_rows_move {g : J} {R : Array V2} (hg : Mx g = rowsMatrix R)
    (h : differs (frApply (frTable R) rootV) rootV = true) : g ∉ Hj := by
  intro hmem
  have h1 := smul_root_of_mem_Hj hM (Hj.inv_mem hmem)
  have h2 := congrArg ofRow h1
  rw [inv_smul_row (g := g), ← Mx_apply, hg] at h2
  apply differs_toVec h
  rw [frApply_toVec_eq_vecMul]
  exact h2

theorem ofRow_uEl_smul {ℓ : ℕ} (hℓ : ℓ < 7) : ofRow (uEl ℓ • w₀) = (rV ℓ).toVec := by
  rw [smul_row, uEl, inv_inv, ← Mx_apply, Mx_kEl hM hℓ]
  show rootV.toVec ᵥ* rowsMatrix (pathRows (repPaths.getD ℓ [])) = (rV ℓ).toVec
  rw [rV, pathVec, pathVecFrom_toVec]

omit hM in
theorem inv_mul_uEl_mem_Hj (hF : J4Facts) {W : J} {R : Array V2} (hW : Mx W = rowsMatrix R)
    {k : ℕ} (hk : k < 7) (h : (frApply (frTable R) (rV k)).beq rootV = true) :
    W⁻¹ * uEl k ∈ Hj := by
  have hv : frApply (frTable R) (rV k) = rootV := V2.beq_iff.1 h
  apply mem_Hj_of_smul_root hF
  rw [← ofRow_inj, mul_smul, inv_smul_row, ofRow_uEl_smul hF.mat hk, ← Mx_apply, hW,
    ← frApply_toVec_eq_vecMul, hv]
  rfl

end Mat

end CFSG.Quasithin.J4Ov
