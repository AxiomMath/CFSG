module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG

namespace FiveTransitive.CharacteristicAutomorphism

variable {G : Type*} [Group G]

lemma mem (N : Subgroup G) [N.Characteristic] (a : MulAut G) {x : G}
    (hx : x ∈ N) : a x ∈ N := by
  change x ∈ N.comap a.toMonoidHom
  rw [(inferInstance : N.Characteristic).fixed a]
  exact hx

lemma map_eq (N : Subgroup G) [N.Characteristic] (a : MulAut G) :
    N.map a.toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact mem N a hy
  · intro hx
    exact ⟨a.symm x,mem N a.symm hx,a.apply_symm_apply x⟩

@[expose] def restrict (N : Subgroup G) [N.Characteristic] : MulAut G →* MulAut N where
  toFun a :=
    { toFun := fun x => ⟨a x,mem N a x.property⟩
      invFun := fun x => ⟨a.symm x,mem N a.symm x.property⟩
      left_inv := fun x => Subtype.ext (a.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (a.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (a.map_mul x y) }
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

@[simp] theorem restrict_apply_val (N : Subgroup G) [N.Characteristic]
    (a : MulAut G) (x : N) : ((restrict N a x : N) : G) = a x := rfl

@[expose] def quotient (N : Subgroup G) [N.Characteristic] : MulAut G →* MulAut (G ⧸ N) where
  toFun a := QuotientGroup.congr N N a (map_eq N a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro g
    rfl
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro g
    rfl

@[simp] theorem quotient_apply_mk (N : Subgroup G) [N.Characteristic]
    (a : MulAut G) (x : G) :
    quotient N a ((QuotientGroup.mk' N) x) = (QuotientGroup.mk' N) (a x) :=
  QuotientGroup.congr_mk' N N a (map_eq N a) x

end FiveTransitive.CharacteristicAutomorphism

end CFSG
