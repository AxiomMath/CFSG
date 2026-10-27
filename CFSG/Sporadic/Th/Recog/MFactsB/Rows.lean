module

public import CFSG.Sporadic.Th.Recog.MFactsB.Complement
public import Certificates.Data.Th687.MFactsC

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Recog.MFactsCData

section Basic

theorem isRows_rowsWJ (i : Fin 8) (hi : i ≠ 1) : IsRows (rowsWJ i) (hswJ i) := by
  rw [hswJ_eq_wordProd i hi]
  unfold rowsWJ
  exact (IsRows.word Max3.isRows_x Max3.isRows_y (wJ i)).mul
    (IsRows.pow Max3.isRows_a (εJ i))

theorem isRows_zM : IsRows rowsA (zM : J) := by
  rw [show (zM : J) = Max3.z from rfl, Max3.z_eq_a]
  exact Max3.isRows_a

theorem isRows_cM : IsRows (rowsWJ 2) (cM : J) := isRows_rowsWJ 2 (by decide)

theorem isRows_dM : IsRows (rowsWJ 3) (dM : J) := isRows_rowsWJ 3 (by decide)

theorem isRows_eM : IsRows (rowsWJ 4) (eM : J) := isRows_rowsWJ 4 (by decide)

theorem isRows_uM : IsRows (rowsWJ 7) (uM : J) := isRows_rowsWJ 7 (by decide)

theorem isRows_sLetter : IsRows (rowsWJ 5) (sLetter : J) := isRows_rowsWJ 5 (by decide)

theorem isRows_tLetter : IsRows (rowsWJ 6) (tLetter : J) := isRows_rowsWJ 6 (by decide)

theorem isRows_ω₁ : IsRows (rowsW1 (rowsWJ 3) (rowsWJ 4)) ((ω₁ : ↥Max3.M) : J) := by
  unfold rowsW1 ω₁
  exact isRows_dM.mul isRows_eM

theorem isRows_ω₁_inv :
    IsRows (rowsW1I (rowsWJ 3) (rowsWJ 4)) ((ω₁⁻¹ : ↥Max3.M) : J) := by
  unfold rowsW1I
  have hω : (ω₁⁻¹ : ↥Max3.M) = eM * dM := by
    change (dM * eM)⁻¹ = eM * dM
    rw [mul_inv_rev, dM_inv, eM_inv]
  rw [hω]
  exact isRows_eM.mul isRows_dM

theorem isRows_uInv : IsRows (rowsUI (rowsWJ 7)) ((uM⁻¹ : ↥Max3.M) : J) := by
  unfold rowsUI
  rw [uM_inv]
  exact isRows_uM.pow 3

theorem isRows_ω₂ :
    IsRows (rowsW2 (rowsWJ 7) (rowsW1 (rowsWJ 3) (rowsWJ 4)) (rowsUI (rowsWJ 7)))
      ((ω₂ : ↥Max3.M) : J) := by
  unfold rowsW2 ω₂
  exact (isRows_uM.mul isRows_ω₁).mul isRows_uInv

theorem isRows_x₁ :
    IsRows (rowsX1 (rowsWJ 2) (rowsWJ 3)) ((x₁ : ↥Max3.M) : J) := by
  unfold rowsX1 x₁
  exact (isRows_cM.mul isRows_dM).pow 2

theorem isRows_x₂ :
    IsRows (rowsX2 (rowsWJ 7) (rowsX1 (rowsWJ 2) (rowsWJ 3)) (rowsUI (rowsWJ 7)))
      ((x₂ : ↥Max3.M) : J) := by
  unfold rowsX2 x₂
  exact (isRows_uM.mul isRows_x₁).mul isRows_uInv

theorem isRows_y₁ :
    IsRows (rowsY1 (rowsW1 (rowsWJ 3) (rowsWJ 4))
      (rowsX1 (rowsWJ 2) (rowsWJ 3)) (rowsW1I (rowsWJ 3) (rowsWJ 4)))
      ((y₁ : ↥Max3.M) : J) := by
  unfold rowsY1 y₁
  exact (isRows_ω₁.mul isRows_x₁).mul isRows_ω₁_inv

theorem isRows_e₀ : IsRows (rowsE0 (rowsWJ 2) (rowsWJ 3)) ((e₀ : ↥Max3.M) : J) := by
  unfold rowsE0 e₀
  exact (isRows_dM.mul isRows_cM).mul isRows_dM

theorem isRows_e₁ :
    IsRows (rowsE1 (rowsWJ 7) (rowsE0 (rowsWJ 2) (rowsWJ 3)) (rowsUI (rowsWJ 7)))
      ((e₁ : ↥Max3.M) : J) := by
  unfold rowsE1 e₁
  exact (isRows_uM.mul isRows_e₀).mul isRows_uInv

theorem isRows_e8 (l : Fin 8) :
    IsRows (rowsE8 rowsA (rowsE0 (rowsWJ 2) (rowsWJ 3))
      (rowsE1 (rowsWJ 7) (rowsE0 (rowsWJ 2) (rowsWJ 3)) (rowsUI (rowsWJ 7))) l)
      ((e8 l : ↥Max3.M) : J) := by
  unfold rowsE8 e8
  exact ((isRows_zM.pow _).mul (isRows_e₀.pow _)).mul (isRows_e₁.pow _)

theorem isRows_e8Tab (l : Fin 8) :
    IsRows ((e8Tab rowsA (rowsE0 (rowsWJ 2) (rowsWJ 3))
      (rowsE1 (rowsWJ 7) (rowsE0 (rowsWJ 2) (rowsWJ 3)) (rowsUI (rowsWJ 7))))[l.val]!)
      ((e8 l : ↥Max3.M) : J) := by
  rw [e8Tab_get]
  exact isRows_e8 l

theorem isRows_pre (a : Fin 18) :
    IsRows (rowsPRE (rowsW1 (rowsWJ 3) (rowsWJ 4))
      (rowsW2 (rowsWJ 7) (rowsW1 (rowsWJ 3) (rowsWJ 4)) (rowsUI (rowsWJ 7)))
      (rowsWJ 3) a) ((pre a : ↥Max3.M) : J) := by
  unfold rowsPRE pre
  exact ((isRows_ω₁.pow _).mul (isRows_ω₂.pow _)).mul (isRows_dM.pow _)

theorem isRows_preTab (a : Fin 18) :
    IsRows ((preTab (rowsW1 (rowsWJ 3) (rowsWJ 4))
      (rowsW2 (rowsWJ 7) (rowsW1 (rowsWJ 3) (rowsWJ 4)) (rowsUI (rowsWJ 7)))
      (rowsWJ 3))[a.val]!) ((pre a : ↥Max3.M) : J) := by
  rw [preTab_get]
  exact isRows_pre a

theorem isRows_nE (i : Fin 5) :
    IsRows ((neTab (rowsWJ 2) (rowsWJ 3) (rowsWJ 4) (rowsWJ 7) (rowsUI (rowsWJ 7)))[i.val]!)
      ((nE i : ↥Max3.M) : J) := by
  fin_cases i
  · simpa [neTab, nE] using isRows_cM
  · simp [neTab, nE]
    exact (((isRows_dM.mul isRows_eM).mul isRows_uM).mul isRows_dM).mul isRows_uInv
  · simp [neTab, nE]
    exact (((isRows_dM.mul isRows_eM).mul isRows_uM).mul isRows_dM).mul isRows_uM
  · simp [neTab, nE]
    exact ((isRows_dM.mul isRows_uM).mul isRows_dM).mul isRows_uM
  · simp [neTab, nE]
    exact ((isRows_dM.mul isRows_uM).mul isRows_dM).mul isRows_uInv

theorem isRows_cE (i : Fin 7) :
    IsRows ((ceTab (rowsWJ 5) (rowsWJ 6))[i.val]!) ((cE i : ↥Max3.M) : J) := by
  fin_cases i
  · simpa [ceTab, cE] using IsRows.one
  · simpa [ceTab, cE] using isRows_sLetter
  · simp [ceTab, cE]
    exact isRows_sLetter.pow 6
  · simp [ceTab, cE]
    exact isRows_sLetter.pow 2
  · simp [ceTab, cE]
    exact isRows_sLetter.mul (isRows_tLetter.pow 2)
  · simp [ceTab, cE]
    exact isRows_sLetter.pow 5
  · simp [ceTab, cE]
    exact (isRows_sLetter.pow 6).mul (isRows_tLetter.pow 2)

theorem isRows_cN (j : Fin 6) :
    IsRows ((cnTab (rowsWJ 3) (rowsWJ 4) (rowsWJ 7) (rowsWJ 5) (rowsWJ 6))[j.val]!)
      ((cN j : ↥Max3.M) : J) := by
  fin_cases j
  · simp [cnTab, cN]
    exact ((isRows_dM.mul isRows_eM).mul isRows_uM).mul isRows_dM
  · simpa [cnTab, cN] using isRows_sLetter
  · simp [cnTab, cN]
    exact isRows_sLetter.pow 2
  · simp [cnTab, cN]
    exact isRows_sLetter.pow 3
  · simp [cnTab, cN]
    exact ((isRows_dM.mul isRows_eM).mul isRows_dM).mul isRows_tLetter
  · change IsRows (mulRows (mulRows (rowsWJ 5)
        (mulRows (mulRows (rowsWJ 3) (rowsWJ 4)) (rowsWJ 3))) (rowsWJ 5))
      ((sLetter * dM * eM * dM * sLetter : ↥Max3.M) : J)
    rw [show (sLetter * dM * eM * dM * sLetter : ↥Max3.M) =
      sLetter * (dM * eM * dM) * sLetter by group]
    exact (isRows_sLetter.mul ((isRows_dM.mul isRows_eM).mul isRows_dM)).mul
      isRows_sLetter

@[expose] noncomputable def cEI : Fin 7 → ↥Max3.M :=
  ![1, sLetter ^ 6, sLetter, sLetter ^ 5, tLetter * sLetter ^ 6, sLetter ^ 2,
    tLetter * sLetter]

@[expose] noncomputable def cNI : Fin 6 → ↥Max3.M :=
  ![dM * uM⁻¹ * eM * dM, sLetter ^ 6, sLetter ^ 5, sLetter ^ 4,
    tLetter ^ 2 * (dM * eM * dM), sLetter ^ 6 * (dM * eM * dM) * sLetter ^ 6]

theorem isRows_cEI (i : Fin 7) :
    IsRows ((ceiTab (rowsWJ 5) (rowsWJ 6))[i.val]!) ((cEI i : ↥Max3.M) : J) := by
  fin_cases i
  · simpa [ceiTab, cEI] using IsRows.one
  · simp [ceiTab, cEI]
    exact isRows_sLetter.pow 6
  · simpa [ceiTab, cEI] using isRows_sLetter
  · simp [ceiTab, cEI]
    exact isRows_sLetter.pow 5
  · simp [ceiTab, cEI]
    exact isRows_tLetter.mul (isRows_sLetter.pow 6)
  · simp [ceiTab, cEI]
    exact isRows_sLetter.pow 2
  · simp [ceiTab, cEI]
    exact isRows_tLetter.mul isRows_sLetter

theorem isRows_cNI (j : Fin 6) :
    IsRows ((cniTab (rowsWJ 3) (rowsWJ 4) (rowsUI (rowsWJ 7)) (rowsWJ 5) (rowsWJ 6))[j.val]!)
      ((cNI j : ↥Max3.M) : J) := by
  fin_cases j
  · simp [cniTab, cNI]
    exact ((isRows_dM.mul isRows_uInv).mul isRows_eM).mul isRows_dM
  · simp [cniTab, cNI]
    exact isRows_sLetter.pow 6
  · simp [cniTab, cNI]
    exact isRows_sLetter.pow 5
  · simp [cniTab, cNI]
    exact isRows_sLetter.pow 4
  · simp [cniTab, cNI]
    exact (isRows_tLetter.pow 2).mul ((isRows_dM.mul isRows_eM).mul isRows_dM)
  · simp [cniTab, cNI]
    exact ((isRows_sLetter.pow 6).mul ((isRows_dM.mul isRows_eM).mul isRows_dM)).mul
      (isRows_sLetter.pow 6)

theorem eq_of_commR {X Y : Array V4} {g h : J} (hX : IsRows X g) (hY : IsRows Y h)
    (e : commR X Y = true) : g * h = h * g := by
  unfold commR at e
  exact IsRows.eq_of_eqRows (hX.mul hY) (hY.mul hX) e

theorem ne_of_commR {X Y : Array V4} {g h : J} (hX : IsRows X g) (hY : IsRows Y h)
    (e : commR X Y = false) : g * h ≠ h * g := by
  unfold commR at e
  exact IsRows.ne_of_eqRows (hX.mul hY) (hY.mul hX) e

end Basic

end CFSG.Sporadic.Th.Recog.MFactsB
