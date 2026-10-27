module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdentA
public import CFSG.Quasithin.Background.G118CanonNineF2TensorPerm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Schreier.TitsIso

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.G11.Canon.F2Tensor
open scoped TensorProduct

theorem galoisField_two_two_finrank :
    Module.finrank (ZMod 2) (GaloisField 2 2) = 2 := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := GaloisField 2 2)
  rw [Nat.card_zmod, hcard] at h
  have h2 : 2 ^ Module.finrank (ZMod 2) (GaloisField 2 2) = 2 ^ 2 := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hval : a.val < 2 := ZMod.val_lt a
  have hcases : a.val = 0 ∨ a.val = 1 := by omega
  rcases hcases with h | h
  · left
    rw [← ZMod.natCast_zmod_val a, h]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val a, h]
    norm_num

@[expose] def permCoreCoord : ↥(CFSG.Quasithin.permCore 3) →ₗ[ZMod 2]
    (Fin 2 → ZMod 2) where
  toFun x := ![s16c1610_pi0 x, s16c1610_pi1 x]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

@[expose] def permCoreCoordInv : (Fin 2 → ZMod 2) →ₗ[ZMod 2]
    ↥(CFSG.Quasithin.permCore 3) where
  toFun v := v 0 • s16c1610_b1 + v 1 • s16c1610_b2
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_add, smul_smul]
    rfl

theorem permCoreCoord_left (v : Fin 2 → ZMod 2) :
    permCoreCoord (permCoreCoordInv v) = v := by
  ext i
  fin_cases i <;>
    simp [permCoreCoord, permCoreCoordInv, s16c1610_pi0, s16c1610_pi1,
      s16c1610_b1, s16c1610_b2]

theorem permCoreCoord_right (x : ↥(CFSG.Quasithin.permCore 3)) :
    permCoreCoordInv (permCoreCoord x) = x := by
  rw [← s16c1610_pi0_smul_b1_add_pi1_smul_b2 x]
  ext i
  fin_cases i <;>
    simp [permCoreCoord, permCoreCoordInv, s16c1610_pi0, s16c1610_pi1,
      s16c1610_b1, s16c1610_b2]

@[expose] noncomputable def permCoreCoordEquiv :
    ↥(CFSG.Quasithin.permCore 3) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofLinearMap permCoreCoord permCoreCoordInv
    (LinearMap.ext permCoreCoord_left) (LinearMap.ext permCoreCoord_right)

@[expose] def py2MatrixMap : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![v 0, v 0 + v 1]
  map_add' u v := by
    ext i
    fin_cases i
    · rfl
    · change (u 0 + v 0) + (u 1 + v 1) = (u 0 + u 1) + (v 0 + v 1)
      abel
  map_smul' a v := by
    ext i
    fin_cases i
    · rfl
    · change a * v 0 + a * v 1 = a * (v 0 + v 1)
      ring

theorem py2MatrixMap_involutive (v : Fin 2 → ZMod 2) :
    py2MatrixMap (py2MatrixMap v) = v := by
  ext i
  fin_cases i
  · rfl
  · change v 0 + (v 0 + v 1) = v 1
    calc v 0 + (v 0 + v 1) = (v 0 + v 0) + v 1 :=
          (add_assoc (v 0) (v 0) (v 1)).symm
      _ = 0 + v 1 := by rw [CharTwo.add_self_eq_zero]
      _ = v 1 := zero_add _

@[expose] noncomputable def py2MatrixEquiv :
    (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofLinearMap py2MatrixMap py2MatrixMap
    (LinearMap.ext py2MatrixMap_involutive) (LinearMap.ext py2MatrixMap_involutive)

theorem exists_eF_of_scalar (c : GaloisField 2 2) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ eF : GaloisField 2 2 ≃ₗ[ZMod 2] ↥(CFSG.Quasithin.permCore 3),
      (∀ x : GaloisField 2 2, eF (c * x) =
        permActLin 3 (finRotate 3) (eF x)) ∧
      (∀ x : GaloisField 2 2, eF (x ^ 2) =
        permActLin 3 (Equiv.swap 0 1) (eF x)) := by
  have h2 : (2 : GaloisField 2 2) = 0 := CharTwo.two_eq_zero
  have hc_sq : c ^ 2 = c + 1 := by
    have hpoly : c ^ 2 + c + 1 = 0 := by
      have h : (c + 1) * (c ^ 2 + c + 1) = 0 := by
        calc (c + 1) * (c ^ 2 + c + 1) = c ^ 3 + 2 * c ^ 2 + 2 * c + 1 := by ring
          _ = c ^ 3 + 1 := by rw [h2]; ring
          _ = 1 + 1 := by rw [hc3]
          _ = 0 := CharTwo.add_self_eq_zero 1
      have hc1' : c + 1 ≠ 0 := by
        intro h0
        have hc : c = 1 := CharTwo.add_eq_zero.mp h0
        exact hc1 hc
      exact (mul_eq_zero.mp h).resolve_left hc1'
    exact CharTwo.add_eq_zero.mp (by
      rw [← add_assoc]
      exact hpoly)
  have hliF : LinearIndependent (ZMod 2) ![1, c] := by
    refine LinearIndependent.pair_iff.mpr ?_
    intro α β h
    rcases zmod_two_eq_zero_or_one α with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one β with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      have h' : c = 0 := by simpa using h
      rw [h'] at hc3
      norm_num at hc3
    · exfalso
      have h' : (1 : GaloisField 2 2) = 0 := by simpa using h
      exact one_ne_zero h'
    · exfalso
      have h2' : (1 : GaloisField 2 2) + c = 0 := by simpa using h
      have h' : (1 : GaloisField 2 2) = c := CharTwo.add_eq_zero.mp h2'
      exact hc1 h'.symm
  let bF : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
    basisOfLinearIndependentOfCardEqFinrank (b := ![1, c]) hliF
      (by rw [Fintype.card_fin, galoisField_two_two_finrank])
  let eF : GaloisField 2 2 ≃ₗ[ZMod 2] ↥(CFSG.Quasithin.permCore 3) :=
    (bF.equivFun).trans (py2MatrixEquiv.trans permCoreCoordEquiv.symm)
  have hbF0 : bF 0 = 1 := by
    simp only [bF, coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  have hbF1 : bF 1 = c := by
    simp only [bF, coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  have hcoord_b1 : permCoreCoord s16c1610_b1 = ![1, 0] := by
    ext i
    fin_cases i <;>
      simp [permCoreCoord, s16c1610_pi0, s16c1610_pi1, s16c1610_b1]
  have hcoord_b2 : permCoreCoord s16c1610_b2 = ![0, 1] := by
    ext i
    fin_cases i <;>
      simp [permCoreCoord, s16c1610_pi0, s16c1610_pi1, s16c1610_b2]
  have hbF_e0 : bF.equivFun 1 = ![1, 0] := by
    rw [← hbF0]
    ext i
    rw [Module.Basis.equivFun_self]
    fin_cases i <;> simp
  have hbF_e1 : bF.equivFun c = ![0, 1] := by
    rw [← hbF1]
    ext i
    rw [Module.Basis.equivFun_self]
    fin_cases i <;> simp
  have hpy0 : py2MatrixEquiv ![1, 0] = ![1, 1] := by
    ext i
    fin_cases i <;> simp [py2MatrixEquiv, py2MatrixMap]
  have hpy1 : py2MatrixEquiv ![0, 1] = ![0, 1] := by
    ext i
    fin_cases i <;> simp [py2MatrixEquiv, py2MatrixMap]
  have hcoord_inv0 : permCoreCoordEquiv.symm ![1, 1] =
      s16c1610_b1 + s16c1610_b2 := by
    change permCoreCoordInv ![1, 1] = s16c1610_b1 + s16c1610_b2
    simp [permCoreCoordInv]
  have hcoord_inv1 : permCoreCoordEquiv.symm ![0, 1] = s16c1610_b2 := by
    change permCoreCoordInv ![0, 1] = s16c1610_b2
    simp [permCoreCoordInv]
  have heF_one : eF 1 = s16c1610_b1 + s16c1610_b2 := by
    simp only [eF, LinearEquiv.trans_apply]
    rw [hbF_e0, hpy0, hcoord_inv0]
  have heF_c : eF c = s16c1610_b2 := by
    simp only [eF, LinearEquiv.trans_apply]
    rw [hbF_e1, hpy1, hcoord_inv1]
  have hfix : permActLin 3 (Equiv.swap 0 1)
      (s16c1610_b1 + s16c1610_b2) = s16c1610_b1 + s16c1610_b2 := by
    apply Subtype.ext
    decide
  have hrho1 : permActLin 3 (finRotate 3)
      (s16c1610_b1 + s16c1610_b2) = s16c1610_b2 := by
    apply Subtype.ext
    decide
  have hrho2 : permActLin 3 (finRotate 3) s16c1610_b2 =
      s16c1610_b1 := by
    apply Subtype.ext
    decide
  have htau2 : permActLin 3 (Equiv.swap 0 1) s16c1610_b2 =
      s16c1610_b1 := by
    apply Subtype.ext
    decide
  have hleft : (s16c1610_b1 + s16c1610_b2) + s16c1610_b2 = s16c1610_b1 := by
    have hb2 : s16c1610_b2 + s16c1610_b2 = 0 := by
      have h : (2 : ZMod 2) • s16c1610_b2 =
          s16c1610_b2 + s16c1610_b2 :=
        two_smul (R := ZMod 2) (x := s16c1610_b2)
      rw [← h, (CharTwo.two_eq_zero (R := ZMod 2)), zero_smul]
    rw [add_assoc, hb2, add_zero]
  let mulCx : GaloisField 2 2 →ₗ[ZMod 2] GaloisField 2 2 :=
    LinearMap.mulLeft (ZMod 2) c
  have hmulCx : ∀ x, mulCx x = c * x := fun x => rfl
  have hx_lin : eF.toLinearMap.comp mulCx =
      (permActLin 3 (finRotate 3)).toLinearMap.comp eF.toLinearMap := by
    apply bF.ext
    intro i
    fin_cases i
    · change eF (mulCx (bF 0)) = permActLin 3 (finRotate 3) (eF (bF 0))
      rw [hbF0, hmulCx, mul_one, heF_c, heF_one]
      simpa using hrho1.symm
    · change eF (mulCx (bF 1)) = permActLin 3 (finRotate 3) (eF (bF 1))
      rw [hbF1, hmulCx, heF_c]
      rw [show c * c = c ^ 2 by ring, hc_sq]
      simp only [map_add, heF_one, heF_c]
      rw [show s16c1610_b2 + (s16c1610_b1 + s16c1610_b2) = s16c1610_b1 by
        rw [add_comm s16c1610_b2 (s16c1610_b1 + s16c1610_b2), hleft]]
      simpa using hrho2.symm
  let frobF : GaloisField 2 2 →ₗ[ZMod 2] GaloisField 2 2 :=
    { toFun := fun x => x ^ 2
      map_add' := fun x y => CharTwo.add_sq x y
      map_smul' := fun r x => by
        rcases zmod_two_eq_zero_or_one r with h | h <;> rw [h] <;> simp }
  have hfrob : ∀ x, frobF x = x ^ 2 := fun x => rfl
  have ht_lin : eF.toLinearMap.comp frobF =
      (permActLin 3 (Equiv.swap 0 1)).toLinearMap.comp eF.toLinearMap := by
    apply bF.ext
    intro i
    fin_cases i
    · change eF (frobF (bF 0)) = permActLin 3 (Equiv.swap 0 1) (eF (bF 0))
      rw [hbF0, hfrob, one_pow, heF_one]
      simpa using hfix.symm
    · change eF (frobF (bF 1)) = permActLin 3 (Equiv.swap 0 1) (eF (bF 1))
      rw [hbF1, hfrob, heF_c]
      rw [hc_sq]
      simp only [map_add, heF_one, heF_c]
      rw [show s16c1610_b2 + (s16c1610_b1 + s16c1610_b2) = s16c1610_b1 by
        rw [add_comm s16c1610_b2 (s16c1610_b1 + s16c1610_b2), hleft]]
      simpa using htau2.symm
  refine ⟨eF, ?_, ?_⟩
  · intro x
    exact LinearMap.congr_fun hx_lin x
  · intro x
    exact LinearMap.congr_fun ht_lin x

@[expose] noncomputable def tensorAction (σ : Equiv.Perm (Fin 3))
    (A : GL (Fin 2) (ZMod 2)) :
    (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
      (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin 2 → ZMod 2)) :=
  TensorProduct.congr (permActLin 3 σ) (s16c1610_glAction 2 A)

theorem tensorAction_tmul (σ : Equiv.Perm (Fin 3)) (A : GL (Fin 2) (ZMod 2))
    (a : ↥(CFSG.Quasithin.permCore 3)) (c : Fin 2 → ZMod 2) :
    tensorAction σ A (a ⊗ₜ[ZMod 2] c) =
      permActLin 3 σ a ⊗ₜ[ZMod 2] s16c1610_glAction 2 A c := by
  simp [tensorAction]

theorem isTensorS3L2_of_tensorModel {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {G : Subgroup (MulAut W)}
    (φ : ↥G ≃* (Equiv.Perm (Fin 3) × GL (Fin 2) (ZMod 2)))
    (e : Additive W ≃ₗ[ZMod 2]
      (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin 2 → ZMod 2)))
    (h : ∀ (γ : ↥G) (v : Additive W),
      e (Additive.ofMul ((γ : MulAut W) (Additive.toMul v))) =
        tensorAction (φ γ).1 (φ γ).2 (e v)) :
    IsTensorS3L2 W G 2 := by
  let ψ : W ≃* Multiplicative
      (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin 2 → ZMod 2)) :=
    AddEquiv.toMultiplicativeRight e.toAddEquiv
  refine ⟨φ, ψ, ?_⟩
  intro γ a a' c c' ha' hc'
  let w : W := ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c))
  have hw : e (Additive.ofMul w) = a ⊗ₜ[ZMod 2] c := by
    have h1 : ψ w = Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c) :=
      MulEquiv.apply_symm_apply ψ _
    have h2 : ψ w = Multiplicative.ofAdd (e (Additive.ofMul w)) := rfl
    exact Multiplicative.ofAdd.injective (h2.symm.trans h1)
  have hgoal : e (Additive.ofMul ((γ : MulAut W) w)) = a' ⊗ₜ[ZMod 2] c' := by
    calc e (Additive.ofMul ((γ : MulAut W) w))
        = tensorAction (φ γ).1 (φ γ).2 (e (Additive.ofMul w)) := h γ (Additive.ofMul w)
      _ = tensorAction (φ γ).1 (φ γ).2 (a ⊗ₜ[ZMod 2] c) := by rw [hw]
      _ = permActLin 3 (φ γ).1 a ⊗ₜ[ZMod 2]
            s16c1610_glAction 2 (φ γ).2 c := tensorAction_tmul _ _ _ _
      _ = a' ⊗ₜ[ZMod 2] c' := by
        rw [show permActLin 3 (φ γ).1 a = a' from Subtype.ext ha'.symm]
        rw [show s16c1610_glAction 2 (φ γ).2 c = c' by
          rw [s16c1610_glAction_apply]
          exact hc'.symm]
  have hw' : ψ ((γ : MulAut W) w) =
      Multiplicative.ofAdd (e (Additive.ofMul ((γ : MulAut W) w))) := rfl
  rw [hw', hgoal]

end CFSG.LocalAnalysis.WeakClosure81
