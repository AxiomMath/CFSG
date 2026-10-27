module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8Model
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.RonanK429F (Om8)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt wreathW isPGroup_wreathW le_card_wreathW)
open scoped MatrixGroups

section OmegaBlock

open Matrix
open scoped commutatorElement

private abbrev omegaI : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

private abbrev omegaQ : (omegaI → ZMod 2) → ZMod 2 := CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1

private abbrev omegaOm : Type := ↥(CFSG.Open.StatedOmega omegaQ)

private def omegaEquiv : omegaI ≃ Fin 8 :=
  (Equiv.sumCongr (Equiv.refl (Fin (4 - 1)))
      (finSumFinEquiv : Fin (4 - 1) ⊕ Fin 2 ≃ Fin (4 - 1 + 2))).trans
    (finSumFinEquiv : Fin (4 - 1) ⊕ Fin (4 - 1 + 2) ≃ Fin (4 - 1 + (4 - 1 + 2)))

private def omegaM (T : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omegaI omegaI (ZMod 2) :=
  T.submatrix omegaEquiv omegaEquiv

private def omegaV (x : Fin 8 → ZMod 2) : omegaI → ZMod 2 := fun i => x (omegaEquiv i)

private def omegaInv (T : Matrix (Fin 8) (Fin 8) (ZMod 2)) (h : omegaM T * omegaM T = 1) :
    Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  Units.mk (omegaM T) (omegaM T) h h

private def omegaUnit (T T' : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (h : omegaM T * omegaM T' = 1) (h' : omegaM T' * omegaM T = 1) :
    Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  Units.mk (omegaM T) (omegaM T') h h'

private def omegaRe0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaRf0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaRe1 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaRf1 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaRe2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaRf2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaSig : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaZeta : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaEta : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaZl0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaZl1 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaZl2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaSl : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of ![![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

private def omegaUE0 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaRe0 (by decide +kernel)

private def omegaUF0 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaRf0 (by decide +kernel)

private def omegaUE1 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaRe1 (by decide +kernel)

private def omegaUF1 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaRf1 (by decide +kernel)

private def omegaUE2 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaRe2 (by decide +kernel)

private def omegaUF2 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaRf2 (by decide +kernel)

private def omegaSig2 : Matrix (Fin 8) (Fin 8) (ZMod 2) := omegaSig * omegaSig

private def omegaUSig : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaUnit omegaSig omegaSig2 (by decide +kernel) (by decide +kernel)

private def omegaUEta : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaEta (by decide +kernel)

private def omegaUZeta : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaZeta (by decide +kernel)

private def omegaUSl : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaInv omegaSl (by decide +kernel)

private def omegaZG0 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaUnit omegaZl0 (omegaZl0 * omegaZl0) (by decide +kernel) (by decide +kernel)

private def omegaZG1 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaUnit omegaZl1 (omegaZl1 * omegaZl1) (by decide +kernel) (by decide +kernel)

private def omegaZG2 : Matrix.GeneralLinearGroup omegaI (ZMod 2) :=
  omegaUnit omegaZl2 (omegaZl2 * omegaZl2) (by decide +kernel) (by decide +kernel)

private theorem omega_isom (A : Matrix.GeneralLinearGroup omegaI (ZMod 2))
    (h : ∀ v : omegaI → ZMod 2,
      omegaQ (Matrix.mulVec (A : Matrix omegaI omegaI (ZMod 2)) v) = omegaQ v) :
    A ∈ CFSG.MatrixModel.isometryCore omegaQ := by
  unfold CFSG.MatrixModel.isometryCore
  have hA : A ∈ {B : Matrix.GeneralLinearGroup omegaI (ZMod 2) |
      ∀ v : omegaI → ZMod 2, omegaQ (Matrix.mulVec (B : Matrix omegaI omegaI (ZMod 2)) v) =
        omegaQ v} := h
  exact Subgroup.subset_closure hA

private theorem omegaRe0_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaRe0 *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaRf0_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaRf0 *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaRe1_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaRe1 *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaRf1_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaRf1 *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaRe2_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaRe2 *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaRf2_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaRf2 *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaSig_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaSig *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaEta_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaEta *ᵥ v) = omegaQ v := by
  decide +kernel
private theorem omegaZeta_iso : ∀ v : omegaI → ZMod 2, omegaQ (omegaM omegaZeta *ᵥ v) = omegaQ v := by
  decide +kernel

private theorem omegaUE0_mem : omegaUE0 ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUE0 omegaRe0_iso
private theorem omegaUF0_mem : omegaUF0 ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUF0 omegaRf0_iso
private theorem omegaUE1_mem : omegaUE1 ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUE1 omegaRe1_iso
private theorem omegaUF1_mem : omegaUF1 ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUF1 omegaRf1_iso
private theorem omegaUE2_mem : omegaUE2 ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUE2 omegaRe2_iso
private theorem omegaUF2_mem : omegaUF2 ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUF2 omegaRf2_iso
private theorem omegaUSig_mem' : omegaUSig ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUSig omegaSig_iso
private theorem omegaUEta_mem : omegaUEta ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUEta omegaEta_iso
private theorem omegaUZeta_mem : omegaUZeta ∈ CFSG.MatrixModel.isometryCore omegaQ :=
  omega_isom omegaUZeta omegaZeta_iso

private theorem omegaZG0_eq : omegaZG0 = ⁅omegaUE0, omegaUF0⁆ := by
  apply Units.ext
  simp only [omegaZG0, omegaUnit, omegaUE0, omegaUF0, omegaInv, commutatorElement_def,
    Units.val_mul, Units.inv_mk, Units.val_mk]
  decide +kernel

private theorem omegaZG1_eq : omegaZG1 = ⁅omegaUE1, omegaUF1⁆ := by
  apply Units.ext
  simp only [omegaZG1, omegaUnit, omegaUE1, omegaUF1, omegaInv, commutatorElement_def,
    Units.val_mul, Units.inv_mk, Units.val_mk]
  decide +kernel

private theorem omegaZG2_eq : omegaZG2 = ⁅omegaUE2, omegaUF2⁆ := by
  apply Units.ext
  simp only [omegaZG2, omegaUnit, omegaUE2, omegaUF2, omegaInv, commutatorElement_def,
    Units.val_mul, Units.inv_mk, Units.val_mk]
  decide +kernel

private theorem omegaUSig_eq : omegaUSig = ⁅omegaUEta, omegaUZeta⁆ := by
  apply Units.ext
  simp only [omegaUSig, omegaUnit, omegaUEta, omegaUZeta, omegaInv, omegaSig2,
    commutatorElement_def, Units.val_mul, Units.inv_mk, Units.val_mk]
  decide +kernel

private theorem omegaUSl_eq : omegaUSl = ⁅omegaUE0, omegaUSig⁆ := by
  apply Units.ext
  simp only [omegaUSl, omegaInv, omegaUE0, omegaUSig, omegaUnit, omegaSig2,
    commutatorElement_def, Units.val_mul, Units.inv_mk, Units.val_mk]
  decide +kernel

private theorem omegaZG0_mem : omegaZG0 ∈ CFSG.Open.StatedOmega omegaQ := by
  rw [omegaZG0_eq]
  unfold CFSG.Open.StatedOmega
  exact Subgroup.commutator_mem_commutator omegaUE0_mem omegaUF0_mem

private theorem omegaZG1_mem : omegaZG1 ∈ CFSG.Open.StatedOmega omegaQ := by
  rw [omegaZG1_eq]
  unfold CFSG.Open.StatedOmega
  exact Subgroup.commutator_mem_commutator omegaUE1_mem omegaUF1_mem

private theorem omegaZG2_mem : omegaZG2 ∈ CFSG.Open.StatedOmega omegaQ := by
  rw [omegaZG2_eq]
  unfold CFSG.Open.StatedOmega
  exact Subgroup.commutator_mem_commutator omegaUE2_mem omegaUF2_mem

private theorem omegaUSig_mem : omegaUSig ∈ CFSG.Open.StatedOmega omegaQ := by
  rw [omegaUSig_eq]
  unfold CFSG.Open.StatedOmega
  exact Subgroup.commutator_mem_commutator omegaUEta_mem omegaUZeta_mem

private theorem omegaUSl_mem : omegaUSl ∈ CFSG.Open.StatedOmega omegaQ := by
  rw [omegaUSl_eq]
  unfold CFSG.Open.StatedOmega
  exact Subgroup.commutator_mem_commutator omegaUE0_mem omegaUSig_mem'

private def omegaZs : Fin 3 → omegaOm :=
  ![⟨omegaZG0, omegaZG0_mem⟩, ⟨omegaZG1, omegaZG1_mem⟩, ⟨omegaZG2, omegaZG2_mem⟩]

private def omegaTt : omegaOm := ⟨omegaUSig, omegaUSig_mem⟩

private def omegaSs : omegaOm := ⟨omegaUSl, omegaUSl_mem⟩

private def omegaMat (x : omegaOm) : Matrix omegaI omegaI (ZMod 2) :=
  Units.val (x : Matrix.GeneralLinearGroup omegaI (ZMod 2))

private theorem omegaMat_mul (x y : omegaOm) : omegaMat (x * y) = omegaMat x * omegaMat y := rfl

private theorem omegaMat_one : omegaMat 1 = 1 := rfl

private theorem omegaMat_pow (x : omegaOm) (n : ℕ) : omegaMat (x ^ n) = omegaMat x ^ n := by
  simp only [omegaMat, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

private theorem omegaSub_eq {x y : omegaOm} (h : omegaMat x = omegaMat y) : x = y :=
  Subtype.ext (Units.ext h)

private theorem omegaMat_Zs0 : omegaMat (omegaZs 0) = omegaM omegaZl0 := rfl
private theorem omegaMat_Zs1 : omegaMat (omegaZs 1) = omegaM omegaZl1 := rfl
private theorem omegaMat_Zs2 : omegaMat (omegaZs 2) = omegaM omegaZl2 := rfl
private theorem omegaMat_Tt : omegaMat omegaTt = omegaM omegaSig := rfl
private theorem omegaMat_Ss : omegaMat omegaSs = omegaM omegaSl := rfl

private def omegaZM : Fin 3 → Matrix omegaI omegaI (ZMod 2) :=
  ![omegaM omegaZl0, omegaM omegaZl1, omegaM omegaZl2]

private theorem omegaMat_Zs (i : Fin 3) : omegaMat (omegaZs i) = omegaZM i := by
  fin_cases i <;> rfl

private theorem omega_pow_ZM : ∀ i : Fin 3, omegaZM i ^ 3 = 1 := by decide +kernel
private theorem omega_comm_ZM : ∀ i j : Fin 3, omegaZM i * omegaZM j = omegaZM j * omegaZM i := by
  decide +kernel
private theorem omega_conj_ZM : ∀ i : Fin 3,
    omegaM omegaSig * omegaZM i = omegaZM (i + 1) * omegaM omegaSig := by
  decide +kernel
private theorem omega_pow_Sig : omegaM omegaSig ^ 3 = 1 := by decide +kernel
private theorem omega_sign0M : omegaM omegaSl * omegaZM 0 = omegaZM 0 ^ 2 * omegaM omegaSl := by
  decide +kernel
private theorem omega_sign1M : omegaM omegaSl * omegaZM 1 = omegaZM 1 ^ 2 * omegaM omegaSl := by
  decide +kernel
private theorem omega_sign2M : omegaM omegaSl * omegaZM 2 = omegaZM 2 * omegaM omegaSl := by
  decide +kernel

private def omegaEv0 : omegaI → ZMod 2 := omegaV ![1, 0, 0, 1, 0, 0, 0, 0]
private def omegaEv1 : omegaI → ZMod 2 := omegaV ![0, 1, 0, 0, 1, 0, 0, 0]
private def omegaEv2 : omegaI → ZMod 2 := omegaV ![0, 0, 1, 0, 0, 1, 0, 0]

private theorem omega_mulVec3 (A B C : Matrix omegaI omegaI (ZMod 2)) (x : omegaI → ZMod 2) :
    (A * B * C) *ᵥ x = A *ᵥ (B *ᵥ (C *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem omega_key0 : ∀ v : Fin 3 → ZMod 3,
    omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv0)) = omegaEv0 → v 0 = 0 := by
  decide +kernel
private theorem omega_key1 : ∀ v : Fin 3 → ZMod 3,
    omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv1)) = omegaEv1 → v 1 = 0 := by
  decide +kernel
private theorem omega_key2 : ∀ v : Fin 3 → ZMod 3,
    omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv2)) = omegaEv2 → v 2 = 0 := by
  decide +kernel
private theorem omega_keyne : ∀ v : Fin 3 → ZMod 3,
    ¬ (omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv0)) = omegaM omegaSig *ᵥ omegaEv0) := by
  decide +kernel

private theorem omega_matVecElt (v : Fin 3 → ZMod 3) :
    omegaMat (vecElt omegaZs v) =
      omegaM omegaZl0 ^ (v 0).val * omegaM omegaZl1 ^ (v 1).val *
        omegaM omegaZl2 ^ (v 2).val := by
  rw [vecElt, omegaMat_mul, omegaMat_mul, omegaMat_pow, omegaMat_pow, omegaMat_pow,
    omegaMat_Zs0, omegaMat_Zs1, omegaMat_Zs2]

private theorem omega_inj : ∀ v : Fin 3 → ZMod 3, vecElt omegaZs v = 1 → v = 0 := by
  intro v hv
  have h1 : omegaM omegaZl0 ^ (v 0).val * omegaM omegaZl1 ^ (v 1).val *
      omegaM omegaZl2 ^ (v 2).val = 1 := by
    rw [← omega_matVecElt v, hv, omegaMat_one]
  have e0 : omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv0)) = omegaEv0 := by
    rw [← omega_mulVec3, h1, Matrix.one_mulVec]
  have e1 : omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv1)) = omegaEv1 := by
    rw [← omega_mulVec3, h1, Matrix.one_mulVec]
  have e2 : omegaM omegaZl0 ^ (v 0).val *ᵥ (omegaM omegaZl1 ^ (v 1).val *ᵥ
      (omegaM omegaZl2 ^ (v 2).val *ᵥ omegaEv2)) = omegaEv2 := by
    rw [← omega_mulVec3, h1, Matrix.one_mulVec]
  funext i
  fin_cases i
  · exact omega_key0 v e0
  · exact omega_key1 v e1
  · exact omega_key2 v e2

private theorem omega_t_ne : ∀ v : Fin 3 → ZMod 3, vecElt omegaZs v ≠ omegaTt := by
  intro v hv
  have h1 : omegaMat (vecElt omegaZs v) *ᵥ omegaEv0 = omegaM omegaSig *ᵥ omegaEv0 := by
    rw [hv, omegaMat_Tt]
  rw [omega_matVecElt, omega_mulVec3] at h1
  exact omega_keyne v h1

private theorem omega_wreath : WreathFacts omegaZs omegaTt where
  pow_z := fun i => by
    apply omegaSub_eq
    rw [omegaMat_pow, omegaMat_one, omegaMat_Zs]
    exact omega_pow_ZM i
  comm_z := fun i j => by
    apply omegaSub_eq
    rw [omegaMat_mul, omegaMat_mul, omegaMat_Zs, omegaMat_Zs]
    exact omega_comm_ZM i j
  inj := omega_inj
  pow_t := by
    apply omegaSub_eq
    rw [omegaMat_pow, omegaMat_one, omegaMat_Tt]
    exact omega_pow_Sig
  conj0 := by
    rw [mul_inv_eq_iff_eq_mul]
    apply omegaSub_eq
    rw [omegaMat_mul, omegaMat_mul, omegaMat_Tt, omegaMat_Zs, omegaMat_Zs]
    exact omega_conj_ZM 0
  conj1 := by
    rw [mul_inv_eq_iff_eq_mul]
    apply omegaSub_eq
    rw [omegaMat_mul, omegaMat_mul, omegaMat_Tt, omegaMat_Zs, omegaMat_Zs]
    exact omega_conj_ZM 1
  conj2 := by
    rw [mul_inv_eq_iff_eq_mul]
    apply omegaSub_eq
    rw [omegaMat_mul, omegaMat_mul, omegaMat_Tt, omegaMat_Zs, omegaMat_Zs]
    exact omega_conj_ZM 2
  t_ne := omega_t_ne

private theorem omega_sign0 : omegaSs * omegaZs 0 * omegaSs⁻¹ = omegaZs 0 ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply omegaSub_eq
  rw [omegaMat_mul, omegaMat_mul, omegaMat_pow, omegaMat_Ss, omegaMat_Zs]
  exact omega_sign0M

private theorem omega_sign1 : omegaSs * omegaZs 1 * omegaSs⁻¹ = omegaZs 1 ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply omegaSub_eq
  rw [omegaMat_mul, omegaMat_mul, omegaMat_pow, omegaMat_Ss, omegaMat_Zs]
  exact omega_sign1M

private theorem omega_sign2 : omegaSs * omegaZs 2 * omegaSs⁻¹ = omegaZs 2 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply omegaSub_eq
  rw [omegaMat_mul, omegaMat_mul, omegaMat_Ss, omegaMat_Zs]
  exact omega_sign2M

private theorem omega_factorization {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card omegaOm).factorization 3 = 4 := by
  have h : Nat.card omegaOm = 197406720 :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8.card_Om8 hbc
  rw [h, show (197406720 : ℕ) = 3 ^ 4 * 2437120 by norm_num]
  exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)

private theorem omega_card_wreathW {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (wreathW omegaZs omegaTt) = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup
    (isPGroup_wreathW omega_wreath)
  rw [omega_factorization hbc] at hle
  have hge := le_card_wreathW omega_wreath
  norm_num at hle
  omega

theorem omega_sylowSignModel {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) : SylowSignModel Om8 := by
  unfold SylowSignModel
  refine ⟨omegaZs, omegaTt, omegaSs, omega_wreath, ?_, omega_card_wreathW hbc, ?_⟩
  · rw [omega_card_wreathW hbc, omega_factorization hbc]
    all_goals norm_num
  · intro w
    exact CFSG.RankThree.PartTwo.Sec8.Item812Res12.conj_vecElt_of_sgn omega_wreath omega_sign0
      omega_sign1 omega_sign2 w

end OmegaBlock
end CFSG.RankThree.PartTwo.Sec18.Item185Proof
