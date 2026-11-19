
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvWord
public import Certificates.Data.J4Ov.CheckE

@[expose] public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

theorem eMats_size (ℓ : ℕ) : (eMats ℓ).size = 22 := by
  simp [eMats, eConj, uBasis, uTab_size]

theorem eMats_get_lt (ℓ : ℕ) {m : ℕ} (hm : m < 11) :
    (eMats ℓ)[m]?.getD idRows = (uTab (locMats ()) (locInvs ()))[m]?.getD idRows := by
  rw [eMats, Array.getElem?_append_left (by simp [uBasis, uTab_size]; omega)]
  rfl

theorem eMats_get_mid (ℓ : ℕ) {m : ℕ} (h1 : 11 ≤ m) (h2 : m < 22) :
    (eMats ℓ)[m]?.getD idRows =
      conjBy (uR ℓ) ((uTab (locMats ()) (locInvs ()))[m - 11]?.getD idRows) (kR ℓ) := by
  rw [eMats, Array.getElem?_append_right (by simp [uBasis, uTab_size]; omega)]
  have hs : uBasis.size = 11 := by simp [uBasis, uTab_size]
  rw [hs, eConj, Array.getElem?_map]
  have hlt : m - 11 < (uTab (locMats ()) (locInvs ())).size := by rw [uTab_size]; omega
  rw [show uBasis = uTab (locMats ()) (locInvs ()) from rfl, Array.getElem?_eq_getElem hlt]
  simp

theorem eMats_get_ge (ℓ : ℕ) {m : ℕ} (h : 22 ≤ m) : (eMats ℓ)[m]?.getD idRows = idRows := by
  have : (eMats ℓ)[m]? = none := by
    rw [Array.getElem?_eq_none_iff, eMats_size]; exact h
  rw [this, Option.getD_none]

section Fam

variable (hM : MatFacts)
include hM

noncomputable def eGs (ℓ m : ℕ) : J :=
  if m < 11 then uJ m else if m < 22 then uEl ℓ * uJ (m - 11) * (uEl ℓ)⁻¹ else 1

theorem uJ_inv {j : ℕ} (hj : j < 11) : (uJ j)⁻¹ = uJ j :=
  inv_eq_of_mul_eq_one_right ((elem_uJ hM).1 j hj)

theorem eGs_inv (ℓ m : ℕ) : (eGs ℓ m)⁻¹ = eGs ℓ m := by
  unfold eGs
  split_ifs with h1 h2
  · exact uJ_inv hM h1
  · rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.inv_inv, uJ_inv hM (by omega),
      _root_.mul_assoc]
  · exact inv_one

theorem eFam {ℓ : ℕ} (hℓ : ℓ < 7) (hinv : eqRows (mulRows (kR ℓ) (uR ℓ)) idRows = true) :
    RowFam (eGs ℓ) (eMats ℓ) (eMats ℓ) := by
  have hmat : ∀ m, Mx (eGs ℓ m) = rowsMatrix ((eMats ℓ)[m]?.getD idRows) := by
    intro m
    unfold eGs
    split_ifs with h1 h2
    · rw [eMats_get_lt ℓ h1]
      exact Mx_uJ hM h1
    · rw [eMats_get_mid ℓ (by omega) h2, conjBy, rowsMatrix_mulRows, rowsMatrix_mulRows,
        map_mul, map_mul, Mx_uEl hM hℓ hinv, Mx_uEl_inv hM hℓ, Mx_uJ hM (by omega)]
    · rw [eMats_get_ge ℓ (by omega), rowsMatrix_idRows, map_one]
  exact ⟨hmat, fun m => by rw [eGs_inv hM, hmat m]⟩

theorem eOK_spec {ℓ i : ℕ} (hℓ : ℓ < 7)
    (hinv : eqRows (mulRows (kR ℓ) (uR ℓ)) idRows = true) (h : eOK ℓ i = true) :
    ∃ c < 2048, wordProd (eGs ℓ) (decodeWord (eData.getD (3 * (ℓ - 1) + i) ("", 0)).1) *
      (xJ i)⁻¹ = eta uJ 11 c := by
  unfold eOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, heq⟩ := h
  refine ⟨(eData.getD (3 * (ℓ - 1) + i) ("", 0)).2, hc, ?_⟩
  apply Mx_injective
  have := rowsMatrix_eq_of_eqRows heq
  rw [rowsMatrix_mulRows] at this
  rw [map_mul, (eFam hM hℓ hinv).mx_wordProd, Mx_xJ_inv hM, Mx_eta hM 11 le_rfl]
  exact this

end Fam

end CFSG.Quasithin.J4Ov
