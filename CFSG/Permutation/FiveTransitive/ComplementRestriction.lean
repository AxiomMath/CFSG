module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG

namespace FiveTransitive.ComplementRestriction

open scoped Pointwise

variable {G X : Type*} [Group G]

@[expose] def restrictHom (ρ : G →* Equiv.Perm X) (F : Set X)
    (hF : ∀ g x, ρ g x ∈ F ↔ x ∈ F) : G →* Equiv.Perm F where
  toFun g := (ρ g).subtypePerm (hF g)
  map_one' := by
    ext x
    change ρ 1 x = x
    simp
  map_mul' g h := by
    ext x
    change ρ (g * h) x = ρ g (ρ h x)
    simp

@[simp] theorem restrictHom_apply (ρ : G →* Equiv.Perm X) (F : Set X)
    (hF : ∀ g x, ρ g x ∈ F ↔ x ∈ F) (g : G) (x : F) :
    (restrictHom ρ F hF g x : X) = ρ g x := rfl

@[expose] def complementHom (ρ : G →* Equiv.Perm X) (F : Set X)
    (hF : ∀ g x, ρ g x ∈ F ↔ x ∈ F) : G →* Equiv.Perm (Fᶜ : Set X) :=
  restrictHom ρ Fᶜ (fun g x => not_congr (hF g x))

@[simp] theorem complementHom_apply (ρ : G →* Equiv.Perm X) (F : Set X)
    (hF : ∀ g x, ρ g x ∈ F ↔ x ∈ F) (g : G) (x : (Fᶜ : Set X)) :
    (complementHom ρ F hF g x : X) = ρ g x := rfl

@[expose] def kernelImage (ρ : G →* Equiv.Perm X) (F : Set X)
    (hF : ∀ g x, ρ g x ∈ F ↔ x ∈ F) :
    Subgroup (restrictHom ρ F hF).range :=
  (complementHom ρ F hF).ker.map (restrictHom ρ F hF).rangeRestrict

instance kernelImage_normal (ρ : G →* Equiv.Perm X) (F : Set X)
    (hF : ∀ g x, ρ g x ∈ F ↔ x ∈ F) : (kernelImage ρ F hF).Normal :=
  (inferInstance : (complementHom ρ F hF).ker.Normal).map _
    (restrictHom ρ F hF).rangeRestrict_surjective

end FiveTransitive.ComplementRestriction

end CFSG
