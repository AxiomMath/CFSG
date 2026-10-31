
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvWord
public import Certificates.Data.J4Ov.CheckMax

@[expose] public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

section Fam

variable (hM : MatFacts)
include hM

noncomputable def maxGs (ℓ : ℕ) (m : ℕ) : J :=
  if m < 3 then xJ m else if m = 3 then uEl ℓ else 1

theorem maxFam {ℓ : ℕ} (hℓ : ℓ < 7)
    (hinv : eqRows (mulRows (kR ℓ) (uR ℓ)) idRows = true) :
    RowFam (maxGs ℓ) (maxMats ℓ) (maxInvs ℓ) := by
  have hs : (locMats ()).size = 3 := hM.locSize
  have hs' : (locInvs ()).size = 3 := by simp [locInvs, hs]
  constructor
  · intro m
    by_cases h3 : m < 3
    · rw [maxGs, ite_eq_left h3, maxMats, Array.getElem?_append_left (by omega)]
      exact Mx_xJ' hM m
    · by_cases h4 : m = 3
      · subst h4
        rw [maxGs, ite_eq_right (by omega), ite_eq_left rfl, maxMats,
          Array.getElem?_append_right (by omega)]
        simp [hs, Mx_uEl hM hℓ hinv]
      · rw [maxGs, ite_eq_right h3, ite_eq_right h4, maxMats,
          Array.getElem?_append_right (by omega)]
        have : (#[uR ℓ] : Array (Array V2))[m - (locMats ()).size]? = none := by
          rw [Array.getElem?_eq_none_iff]; simp; omega
        rw [this, Option.getD_none, rowsMatrix_idRows, map_one]
  · intro m
    by_cases h3 : m < 3
    · rw [maxGs, ite_eq_left h3, maxInvs, Array.getElem?_append_left (by omega)]
      exact Mx_xJ_inv hM m
    · by_cases h4 : m = 3
      · subst h4
        rw [maxGs, ite_eq_right (by omega), ite_eq_left rfl, maxInvs,
          Array.getElem?_append_right (by omega)]
        simp [hs', Mx_uEl_inv hM hℓ]
      · rw [maxGs, ite_eq_right h3, ite_eq_right h4, maxInvs,
          Array.getElem?_append_right (by omega)]
        have : (#[kR ℓ] : Array (Array V2))[m - (locInvs ()).size]? = none := by
          rw [Array.getElem?_eq_none_iff]; simp; omega
        rw [this, Option.getD_none, rowsMatrix_idRows, inv_one, map_one]

end Fam

theorem uEl_mem_of_word (hF : J4Facts) {ℓ k : ℕ} (hℓ : ℓ < 7) (hk : k < 7)
    (hinv : eqRows (mulRows (kR ℓ) (uR ℓ)) idRows = true) {w : String}
    (hw : maxOK ℓ k w = true) {D : Subgroup J} (hD : Hj ≤ D) (hu : uEl ℓ ∈ D) : uEl k ∈ D := by
  have hfam := maxFam hF.mat hℓ hinv
  have hWD : wordProd (maxGs ℓ) (decodeWord w) ∈ D := by
    refine wordProd_mem D (fun m => ?_) _
    unfold maxGs
    split_ifs with h3 h4
    · exact hD (xJ_mem h3)
    · exact hu
    · exact D.one_mem
  have hMx := hfam.mx_wordProd (decodeWord w)
  have h1 := inv_mul_uEl_mem_Hj hF hMx hk hw
  have e : uEl k = wordProd (maxGs ℓ) (decodeWord w) *
      ((wordProd (maxGs ℓ) (decodeWord w))⁻¹ * uEl k) := by group
  rw [e]
  exact D.mul_mem hWD (hD h1)

end CFSG.Quasithin.J4Ov
