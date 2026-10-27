module

public import CFSG.Monster.GMS.TwoAGraph
public import Mathlib.Algebra.Order.Group.End
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

abbrev GammaAut (a : G) := (twoAGraph a) ≃g (twoAGraph a)

@[expose] def conjAut (a : G) (g : G) : GammaAut a where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have h' := twoAGraph_adj_smul g⁻¹ h
      simpa using h'
    · intro h
      exact twoAGraph_adj_smul g h

@[simp]
theorem conjAut_apply (a g : G) (x : ConjVert a) : conjAut a g x = g • x := rfl

@[expose] def actHom (a : G) : G →* GammaAut a where
  toFun := conjAut a
  map_one' := RelIso.ext fun x => by simp
  map_mul' g h := RelIso.ext fun x => by simp [RelIso.mul_apply, mul_smul]

@[simp]
theorem actHom_apply (a g : G) (x : ConjVert a) : actHom a g x = g • x := rfl

end CFSG.Monster.GMS
