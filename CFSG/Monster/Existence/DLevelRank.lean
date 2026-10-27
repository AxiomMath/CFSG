module

public import CFSG.Monster.Existence.DLevelConj
public import CFSG.Monster.B.Final.PairNodes
public import CFSG.Monster.B.Dyadic.FixedLine
public import CFSG.Monster.B.Rep4371.ExactActions
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Blueprint MulOpposite Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def betaStd :
    Cbar →* GL (Fin 4370) (ZMod 2) :=
  Dyadic.betaS

theorem betaStd_explicit :
    IsExplicitBinary betaStd := betaS_explicit

@[expose] noncomputable def eB :
    NativeSporadic.B ≃* Sbp :=
  Classical.choose (pinned_B_explicit_native_isomorphism betaStd_explicit).2

theorem betaRow_eB
    (X : NativeSporadic.B) :
    ((betaRow betaStd (eB X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹ :=
  (Classical.choose_spec (pinned_B_explicit_native_isomorphism betaStd_explicit).2).1 X

@[expose] noncomputable def phiB :
    Cbar ≃* NativeSporadic.B :=
  (MulEquiv.inv' Cbar).trans eB.symm

theorem card_Cbar_eq_card_B :
    Nat.card Cbar = Nat.card NativeSporadic.B :=
  Nat.card_congr phiB.toEquiv

theorem eB_phiB
    (y : Cbar) : eB (phiB y) = op y⁻¹ := by
  rw [phiB, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem rank_conj_sub_one {A M : MatB} {A' : MatB} (hA : A * A' = 1) (hA' : A' * A = 1) :
    (A * M * A' - 1).rank = (M - 1).rank := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 ⟨⟨A, A', hA, hA'⟩, rfl⟩
  have hdet' : IsUnit A'.det := (Matrix.isUnit_iff_isUnit_det A').1 ⟨⟨A', A, hA', hA⟩, rfl⟩
  have h : A * M * A' - 1 = A * (M - 1) * A' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hA]
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]

theorem uBar_inv : uBar⁻¹ = uBar := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ← orderOf_uBar, pow_orderOf_eq_one]

theorem rank_phiB_uBar_sub_one :
    Matrix.rank ((phiB uBar).val.val - 1) = 1860 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_uBar_packetElt_one
  have hu : uBar = c⁻¹ * packetElt 1 * c := by
    rw [← hc]
    group
  have hg0 : ((betaRow betaStd (op (packetElt 1)) : MatBˣ) : MatB) = Dyadic.Qmat 0 := by
    have h := betaStd_explicit.gen 0 (by norm_num)
    rw [gSeq_of_lt (by norm_num : 0 < 26)] at h
    exact h.trans (Qn_eq 0)
  have hrow : ((betaRow betaStd (op uBar) : MatBˣ) : MatB) =
      ((betaRow betaStd (op c) : MatBˣ) : MatB) * Dyadic.Qmat 0 *
        (((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB) := by
    rw [hu, op_mul, op_mul, map_mul, map_mul, Units.val_mul, Units.val_mul, hg0, op_inv, map_inv,
      Matrix.mul_assoc]
  have hX : ((phiB uBar).val.val : MatB) = bMat (phiB uBar) := rfl
  have hbm : bMat (phiB uBar) =
      Tmat⁻¹ * ((betaRow betaStd (op uBar) : MatBˣ) : MatB) * Tmat := by
    have h := betaRow_eB (phiB uBar)
    rw [eB_phiB, uBar_inv] at h
    rw [h]
    calc bMat (phiB uBar) = (Tmat⁻¹ * Tmat) * bMat (phiB uBar) * (Tmat⁻¹ * Tmat) := by
          rw [Tmat_inv_mul, Matrix.one_mul, Matrix.mul_one]
      _ = Tmat⁻¹ * (Tmat * bMat (phiB uBar) * Tmat⁻¹) * Tmat := by simp only [Matrix.mul_assoc]
  rw [hX, hbm, hrow]
  have e1 : Tmat⁻¹ * (((betaRow betaStd (op c) : MatBˣ) : MatB) * Dyadic.Qmat 0 *
        (((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB)) * Tmat =
      (Tmat⁻¹ * ((betaRow betaStd (op c) : MatBˣ) : MatB)) * Dyadic.Qmat 0 *
        ((((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB) * Tmat) := by
    simp only [Matrix.mul_assoc]
  rw [e1, rank_conj_sub_one]
  · exact Dyadic.rank_Q0
  · calc (Tmat⁻¹ * ((betaRow betaStd (op c) : MatBˣ) : MatB)) *
          ((((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB) * Tmat)
        = Tmat⁻¹ * (((betaRow betaStd (op c) : MatBˣ) : MatB) *
          (((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB)) * Tmat := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, Tmat_inv_mul]
  · calc ((((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB) * Tmat) *
          (Tmat⁻¹ * ((betaRow betaStd (op c) : MatBˣ) : MatB))
        = (((betaRow betaStd (op c))⁻¹ : MatBˣ) : MatB) * (Tmat * Tmat⁻¹) *
          ((betaRow betaStd (op c) : MatBˣ) : MatB) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Tmat_mul_inv, Matrix.mul_one, Units.inv_mul]

end CFSG.Monster.Existence
