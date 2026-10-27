module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCADefs

public section

namespace CFSG.StandardType

@[expose] noncomputable def ggKGCARestrict {V : Type} [AddCommGroup V] [Module GGKGCF V]
    (p : Submodule GGKGCF V) (e : V ≃ₗ[GGKGCF] V) (hp : ∀ x ∈ p, e x ∈ p)
    (hp' : ∀ x ∈ p, e.symm x ∈ p) : p ≃ₗ[GGKGCF] p where
  toFun x := ⟨e x, hp x x.2⟩
  invFun y := ⟨e.symm y, hp' y y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

theorem ggKGCARestrict_apply {V : Type} [AddCommGroup V] [Module GGKGCF V]
    (p : Submodule GGKGCF V) (e : V ≃ₗ[GGKGCF] V) (hp : ∀ x ∈ p, e x ∈ p)
    (hp' : ∀ x ∈ p, e.symm x ∈ p) (x : p) :
    ((ggKGCARestrict p e hp hp' x : p) : V) = e (x : V) := rfl

@[expose] noncomputable def ggKGCARes {V : Type} [AddCommGroup V] [Module GGKGCF V]
    (p : Submodule GGKGCF V) (S : Subgroup (V ≃ₗ[GGKGCF] V))
    (hS : ∀ a ∈ S, ∀ x ∈ p, a x ∈ p) : S →* (p ≃ₗ[GGKGCF] p) where
  toFun a := ggKGCARestrict p a (hS a a.2) (fun x hx => hS a⁻¹ (S.inv_mem a.2) x hx)
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

theorem ggKGCARes_apply {V : Type} [AddCommGroup V] [Module GGKGCF V]
    (p : Submodule GGKGCF V) (S : Subgroup (V ≃ₗ[GGKGCF] V))
    (hS : ∀ a ∈ S, ∀ x ∈ p, a x ∈ p) (a : S) (x : p) :
    ((ggKGCARes p S hS a x : p) : V) = (a : V ≃ₗ[GGKGCF] V) (x : V) := rfl

end CFSG.StandardType

end
