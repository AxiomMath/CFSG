module

public import Mathlib.RepresentationTheory.Invariants

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
Representations attached to actions on elementary abelian groups.

An elementary abelian `p`-group is canonically a `ZMod p`-module after passing to
`Additive`. Any action by group automorphisms is therefore linear over `ZMod p`.
-/

namespace CFSG.Theory.Representation

open _root_.Representation

variable {A G : Type*} [Group A] [Group G] {p : ℕ} [Fact p.Prime]

/-- The `ZMod p` representation associated to an action by automorphisms on an elementary abelian
`p`-group. -/
public noncomputable def ofElementaryAbelianAction [IsElementaryAbelian p G]
    [MulDistribMulAction A G] : Representation (ZMod p) A (Additive G) where
  toFun a :=
    let eAdd : Additive G ≃+ Additive G :=
      MulEquiv.toAdditive (MulDistribMulAction.toMulAut A G a)
    let eLin : Additive G ≃ₗ[ZMod p] Additive G :=
      eAdd.toLinearEquiv (fun c x => by
        simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
    eLin.toLinearMap
  map_one' := by
    ext x
    apply Additive.toMul.injective
    simp [MulDistribMulAction.toMulAut]
  map_mul' := by
    intro a b
    ext x
    apply Additive.toMul.injective
    simp [MulDistribMulAction.toMulAut, smul_smul]

@[simp]
public theorem ofElementaryAbelianAction_apply [IsElementaryAbelian p G]
    [MulDistribMulAction A G] (a : A) (x : Additive G) :
    ofElementaryAbelianAction (A := A) (G := G) (p := p) a x =
      Additive.ofMul (a • Additive.toMul x) := by
  rfl

@[simp]
public theorem ofElementaryAbelianAction_apply_ofMul [IsElementaryAbelian p G]
    [MulDistribMulAction A G] (a : A) (x : G) :
    ofElementaryAbelianAction (A := A) (G := G) (p := p) a (Additive.ofMul x) =
      Additive.ofMul (a • x) := by
  rfl

/-- The kernel of the linear representation is the subgroup acting trivially on the elementary
abelian group. -/
public theorem ker_ofElementaryAbelianAction_eq_fixingSubgroup [IsElementaryAbelian p G]
    [MulDistribMulAction A G] :
    (ofElementaryAbelianAction (A := A) (G := G) (p := p)).ker =
      fixingSubgroupOf A G (Set.univ : Set G) := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha
    refine (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set G))).2 ?_
    intro x _hx
    have hfix :
        ofElementaryAbelianAction (A := A) (G := G) (p := p) a (Additive.ofMul x) =
          Additive.ofMul x := by
      simpa using congrArg (fun f : Module.End (ZMod p) (Additive G) => f (Additive.ofMul x)) ha
    exact Additive.ofMul.injective hfix
  · intro ha
    ext x
    have hfix :
        a • Additive.toMul x = Additive.toMul x :=
      (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set G))).1 ha
        (Additive.toMul x) (Set.mem_univ _)
    simp [hfix]


end CFSG.Theory.Representation
