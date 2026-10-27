module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module
import all CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.GL52.OrderThreeFour
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.GroupTheory.GL52 (F4 F4poly F4poly_natDegree F4poly_ne_zero)
open Polynomial

variable {W : Type*} [CommGroup W] [Finite W]

section Subgroup

variable {U : Subgroup W}

@[expose, instance_reducible] def addModTwoSub (hw2 : ∀ w : W, w ^ 2 = 1) :
    Module (ZMod 2) (Additive U) :=
  AddCommGroup.zmodModule (n := 2) (fun v => by
    have hv : Additive.ofMul (Additive.toMul (α := U) v) = v := rfl
    rw [← hv, two_nsmul]
    change Additive.ofMul
      ((Additive.toMul (α := U) v : U) * Additive.toMul (α := U) v) = 0
    have h : (Additive.toMul (α := U) v : U) * Additive.toMul (α := U) v = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hw2 ((Additive.toMul (α := U) v : U) : W)
    rw [h]
    rfl)

@[expose] def autAddHomSub (x : MulAut W) (hU : ∀ u ∈ U, x u ∈ U) :
    Additive U →+ Additive U where
  toFun v := Additive.ofMul
    ⟨x (Additive.toMul (α := U) v), hU (Additive.toMul (α := U) v) v.2⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change x (1 : W) = 1
    simp
  map_add' a b := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    change x (Additive.toMul (α := U) (a + b) : W) =
      x (Additive.toMul (α := U) a : W) * x (Additive.toMul (α := U) b : W)
    rw [toMul_add]
    exact map_mul x _ _

@[expose] def autEndSub (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hU : ∀ u ∈ U, x u ∈ U) :
    @Module.End (ZMod 2) (Additive U) _ _ (addModTwoSub (U := U) hw2) :=
  @AddMonoidHom.toZModLinearMap 2 (Additive U) (Additive U) _ _
    (addModTwoSub (U := U) hw2) (addModTwoSub (U := U) hw2) (autAddHomSub x hU)

@[simp] theorem autEndSub_apply (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hU : ∀ u ∈ U, x u ∈ U) (v : Additive U) :
    autEndSub hw2 x hU v = autAddHomSub x hU v := rfl

@[simp] theorem autAddHomSub_apply (x : MulAut W) (hU : ∀ u ∈ U, x u ∈ U)
    (v : Additive U) :
    autAddHomSub x hU v =
      Additive.ofMul
        ⟨x (Additive.toMul (α := U) v), hU (Additive.toMul (α := U) v) v.2⟩ := rfl

end Subgroup

end CFSG.LocalAnalysis.WeakClosure81

