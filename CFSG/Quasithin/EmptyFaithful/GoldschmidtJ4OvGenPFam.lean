module

public import Certificates.Data.J4Ov.CheckP
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenEBase
public import CFSG.Sporadic.J4.QTRankInvProof

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

@[expose] noncomputable def zEl (r : RepEntry) : J :=
  pathElt (repPaths.getD r.l []) * wordProd xJ (decodeWord r.xw)

section Mat

variable (hM : MatFacts)
include hM

theorem Mx_zEl {r : RepEntry} (hl : r.l < 7) : Mx (zEl r) = rowsMatrix (repZ r) := by
  rw [zEl, map_mul, Mx_kEl hM hl, Mx_wordProd hM, repZ, rowsMatrix_mulRows]

end Mat

theorem Mx_inv_of_rows {g : J} {R Ri : Array V2} (hg : Mx g = rowsMatrix R)
    (h : eqRows (mulRows R Ri) idRows = true) : Mx (g⁻¹) = rowsMatrix Ri := by
  have h1 : Mx g * rowsMatrix Ri = 1 := by
    rw [hg]
    have := rowsMatrix_eq_of_eqRows h
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have h2 : Mx (g⁻¹) * Mx g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc Mx (g⁻¹) = Mx (g⁻¹) * (Mx g * rowsMatrix Ri) := by rw [h1, Matrix.mul_one]
    _ = (Mx (g⁻¹) * Mx g) * rowsMatrix Ri := by rw [Matrix.mul_assoc]
    _ = rowsMatrix Ri := by rw [h2, Matrix.one_mul]

theorem pConj_get (Zi Z : Array V2) {j : ℕ} (hj : j < 11) :
    (pConj Zi Z)[j]? = some (conjBy Zi ((uTab (locMats ()) (locInvs ()))[j]?.getD idRows) Z) := by
  have hlt : j < (uTab (locMats ()) (locInvs ())).size := by rw [uTab_size]; exact hj
  rw [pConj, Array.getElem?_map, show uBasis = uTab (locMats ()) (locInvs ()) from rfl,
    Array.getElem?_eq_getElem hlt]
  simp

theorem pConj_size (Zi Z : Array V2) : (pConj Zi Z).size = 11 := by
  simp [pConj, uBasis, uTab_size]

theorem kT_size : kT.size = 4 := by simp [kT, kRowsTab]

theorem kTi_size : kTi.size = 4 := by simp [kTi, kT_size]

theorem cat3_get_lt {A K C : Array (Array V2)} (hA : A.size = 11) (hK : K.size = 4) {m : ℕ}
    (hm : m < 11) : (A ++ K ++ C)[m]? = A[m]? := by
  rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left (by omega)]

theorem cat3_get_mid {A K C : Array (Array V2)} (hA : A.size = 11) (hK : K.size = 4) {m : ℕ}
    (h1 : 11 ≤ m) (h2 : m < 15) : (A ++ K ++ C)[m]? = K[m - 11]? := by
  rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_right (by omega), hA]

theorem cat3_get_ge {A K C : Array (Array V2)} (hA : A.size = 11) (hK : K.size = 4) {m : ℕ}
    (h : 15 ≤ m) : (A ++ K ++ C)[m]? = C[m - 15]? := by
  rw [Array.getElem?_append_right (by simp; omega)]
  simp only [Array.size_append, hA, hK]

section Fam

variable (hM : MatFacts)
include hM

@[expose] noncomputable def pGs (r : RepEntry) (m : ℕ) : J :=
  if m < 11 then uJ m else if m < 15 then kJ (m - 11) else if m < 26 then
    (zEl r)⁻¹ * uJ (m - 15) * zEl r else 1

theorem pFam {r : RepEntry} (hl : r.l < 7)
    (hz : eqRows (mulRows (repZ r) (invRows (repZ r))) idRows = true)
    (hk : ∀ i < 4, eqRows (mulRows ((kRowsTab ())[i]?.getD idRows) (kTi[i]?.getD idRows))
      idRows = true) :
    RowFam (pGs r) (uBasis ++ kT ++ pConj (invRows (repZ r)) (repZ r))
      (uBasis ++ kTi ++ pConj (invRows (repZ r)) (repZ r)) := by
  have hZ := Mx_zEl hM hl
  have hZi : Mx ((zEl r)⁻¹) = rowsMatrix (invRows (repZ r)) := Mx_inv_of_rows hZ hz
  have hA : uBasis.size = 11 := by simp [uBasis, uTab_size]
  have hmat : ∀ m, Mx (pGs r m) = rowsMatrix
      ((uBasis ++ kT ++ pConj (invRows (repZ r)) (repZ r))[m]?.getD idRows) := by
    intro m
    unfold pGs
    split_ifs with h1 h2 h3
    · rw [cat3_get_lt hA kT_size h1]
      exact Mx_uJ hM h1
    · rw [cat3_get_mid hA kT_size (by omega) h2]
      exact Mx_kJ hM (by omega)
    · rw [cat3_get_ge hA kT_size (by omega), pConj_get _ _ (by omega), Option.getD_some,
        conjBy, rowsMatrix_mulRows, rowsMatrix_mulRows, map_mul, map_mul, hZi, hZ,
        Mx_uJ hM (by omega)]
    · have : (uBasis ++ kT ++ pConj (invRows (repZ r)) (repZ r))[m]? = none := by
        rw [Array.getElem?_eq_none_iff]
        simp only [Array.size_append, hA, kT_size, pConj_size]
        omega
      rw [this, Option.getD_none, rowsMatrix_idRows, map_one]
  have hinvself : ∀ m, (m < 11 ∨ 15 ≤ m) → (pGs r m)⁻¹ = pGs r m := by
    intro m hm
    unfold pGs
    by_cases h1 : m < 11
    · rw [ite_eq_left h1]
      exact uJ_inv hM h1
    · have h15 : 15 ≤ m := by omega
      rw [ite_eq_right h1, ite_eq_right (by omega)]
      by_cases h3 : m < 26
      · rw [ite_eq_left h3, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.inv_inv,
          uJ_inv hM (by omega), _root_.mul_assoc]
      · rw [ite_eq_right h3, inv_one]
  have hsame : ∀ m, (m < 11 ∨ 15 ≤ m) →
      (uBasis ++ kTi ++ pConj (invRows (repZ r)) (repZ r))[m]?.getD idRows =
        (uBasis ++ kT ++ pConj (invRows (repZ r)) (repZ r))[m]?.getD idRows := by
    intro m hm
    rcases hm with h | h
    · rw [cat3_get_lt hA kTi_size h, cat3_get_lt hA kT_size h]
    · rw [cat3_get_ge hA kTi_size h, cat3_get_ge hA kT_size h]
  refine ⟨hmat, fun m => ?_⟩
  by_cases hm : m < 11 ∨ 15 ≤ m
  · rw [hinvself m hm, hsame m hm]
    exact hmat m
  · have h1 : ¬ m < 11 := fun h => hm (Or.inl h)
    have h2 : m < 15 := by omega
    have hlt : m - 11 < 4 := by omega
    rw [cat3_get_mid hA kTi_size (by omega) h2]
    have e : pGs r m = kJ (m - 11) := by
      unfold pGs
      rw [ite_eq_right h1, ite_eq_left h2]
    rw [e]
    exact Mx_inv_of_rows (Mx_kJ hM hlt) (hk (m - 11) hlt)

end Fam

end CFSG.Quasithin.J4Ov
