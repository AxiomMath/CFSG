module

public import CFSG.RankThree.GF2n.Parrott.ActionV

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

section LinearAut

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] noncomputable def mulAutToAddMonoidHom (g : MulAut (Multiplicative M)) : M →+ M where
  toFun m := (g (Multiplicative.ofAdd m)).toAdd
  map_zero' := by simp
  map_add' := by
    intro x y
    rw [ofAdd_add, map_mul, toAdd_mul]

@[expose] noncomputable def mulAutToLinearMap (g : MulAut (Multiplicative M)) : M →ₗ[ZMod 2] M :=
  (mulAutToAddMonoidHom g).toZModLinearMap 2

@[simp] lemma mulAutToLinearMap_apply (g : MulAut (Multiplicative M)) (m : M) :
    mulAutToLinearMap g m = (g (Multiplicative.ofAdd m)).toAdd := rfl

noncomputable def mulAutMultiplicativeGeneralLinearEquiv :
    MulAut (Multiplicative M) ≃* LinearMap.GeneralLinearGroup (ZMod 2) M where
  toFun g :=
    { val := mulAutToLinearMap g
      inv := mulAutToLinearMap g.symm
      val_inv := by
        ext x
        simp [mulAutToLinearMap_apply]
      inv_val := by
        ext x
        simp [mulAutToLinearMap_apply] }
  invFun u :=
    { toFun := fun x => Multiplicative.ofAdd (u.val x.toAdd)
      invFun := fun x => Multiplicative.ofAdd (u.inv x.toAdd)
      left_inv := by
        intro x
        show Multiplicative.ofAdd (u.inv (u.val x.toAdd)) = x
        rw [show u.inv (u.val x.toAdd) = x.toAdd from
          congrArg (fun f : M →ₗ[ZMod 2] M => f x.toAdd) u.inv_val]
        simp
      right_inv := by
        intro x
        show Multiplicative.ofAdd (u.val (u.inv x.toAdd)) = x
        rw [show u.val (u.inv x.toAdd) = x.toAdd from
          congrArg (fun f : M →ₗ[ZMod 2] M => f x.toAdd) u.val_inv]
        simp
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (u.val (x.toAdd + y.toAdd)) =
          Multiplicative.ofAdd (u.val x.toAdd) * Multiplicative.ofAdd (u.val y.toAdd)
        rw [map_add, ofAdd_add] }
  left_inv g := by
    ext x
    simp [mulAutToLinearMap_apply]
  right_inv u := by
    ext x
    simp
  map_mul' g₁ g₂ := by
    ext x
    simp [mulAutToLinearMap_apply]

end LinearAut

local instance instModulePiF2 : Module (ZMod 2) (Fin 8 → ZMod 2) :=
  Pi.Function.module (Fin 8) (ZMod 2) (ZMod 2)

section ParrottHyp

variable (h : Tim79a.ParrottHyp z)

@[expose, reducible] noncomputable def commGroupV : CommGroup (QuotientV.V z) :=
  { (inferInstance : Group (QuotientV.V z)) with
    mul_comm := (QuotientV.isMulCommutative_V h).is_comm.comm }

@[reducible] noncomputable def moduleV :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    Module (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← pow_two]
    exact QuotientV.pow_two_eq_one_V h x.toMul

theorem finrank_addV :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Module.finrank (ZMod 2) (Additive (QuotientV.V z)) = 8 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hcard : Nat.card (Additive (QuotientV.V z)) = 2 ^ 8 := by
    rw [Nat.card_congr Additive.toMul]
    exact QuotientV.card_V h
  have hdim := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (QuotientV.V z))
  rw [hcard, Nat.card_zmod] at hdim
  exact Nat.pow_right_injective (by norm_num) hdim.symm

noncomputable def linearEquivAddV :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Additive (QuotientV.V z) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact LinearEquiv.ofFinrankEq _ _ (by rw [finrank_addV h, Module.finrank_fin_fun])

noncomputable def mulEquivV : QuotientV.V z ≃* Multiplicative (Fin 8 → ZMod 2) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let e := linearEquivAddV h
  exact
    { toFun := fun v => Multiplicative.ofAdd (e (Additive.ofMul v))
      invFun := fun w => Additive.toMul (e.symm w.toAdd)
      left_inv := by intro v; simp
      right_inv := by intro w; simp
      map_mul' := by
        intro v w
        show Multiplicative.ofAdd (e (Additive.ofMul (v * w))) =
          Multiplicative.ofAdd (e (Additive.ofMul v)) * Multiplicative.ofAdd (e (Additive.ofMul w))
        rw [ofMul_mul, map_add, ofAdd_add] }

noncomputable def mulAutVEquivGL :
    MulAut (QuotientV.V z) ≃* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  (MulAut.congr (mulEquivV h)).trans
    ((@mulAutMultiplicativeGeneralLinearEquiv (Fin 8 → ZMod 2) Pi.addCommGroup
      (Pi.Function.module (Fin 8) (ZMod 2) (ZMod 2))).trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin 8) (R := ZMod 2)).symm)

noncomputable def actionGL :
    (↥(H z) ⧸ (J z).subgroupOf (H z)) →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  (mulAutVEquivGL h).toMonoidHom.comp (actionA h)

theorem actionGL_mk (g : H z) :
    actionGL h (QuotientGroup.mk' ((J z).subgroupOf (H z)) g) =
      mulAutVEquivGL h (conjV h g) := by
  rw [actionGL, MonoidHom.comp_apply, actionA_mk]
  rfl

theorem mulVec_mulAutVEquivGL (g : MulAut (QuotientV.V z)) (v : QuotientV.V z) :
    ((mulAutVEquivGL h g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (mulEquivV h v)) =
      Multiplicative.toAdd (mulEquivV h (g v)) := by
  have h1 := Matrix.GeneralLinearGroup.toLin_apply (mulAutVEquivGL h g)
    (Multiplicative.toAdd (mulEquivV h v))
  have h2 : Matrix.GeneralLinearGroup.toLin (mulAutVEquivGL h g) =
      @mulAutMultiplicativeGeneralLinearEquiv (Fin 8 → ZMod 2) Pi.addCommGroup
        (Pi.Function.module (Fin 8) (ZMod 2) (ZMod 2)) (MulAut.congr (mulEquivV h) g) := by
    have h3 : mulAutVEquivGL h g = Matrix.GeneralLinearGroup.toLin.symm
        (@mulAutMultiplicativeGeneralLinearEquiv (Fin 8 → ZMod 2) Pi.addCommGroup
          (Pi.Function.module (Fin 8) (ZMod 2) (ZMod 2)) (MulAut.congr (mulEquivV h) g)) := rfl
    rw [h3]
    exact MulEquiv.apply_symm_apply _ _
  rw [h2] at h1
  rw [Matrix.mulVecLin_apply] at h1
  rw [← h1]
  show (MulAut.congr (mulEquivV h) g
    (Multiplicative.ofAdd (Multiplicative.toAdd (mulEquivV h v)))).toAdd = _
  simp [MulAut.congr_apply]

end ParrottHyp

end CFSG.RankThree.GF2n.Parrott
