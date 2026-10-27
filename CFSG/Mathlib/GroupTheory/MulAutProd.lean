module

public import Mathlib.SetTheory.Cardinal.Finite

public section

set_option autoImplicit false

universe u v

namespace MulAut

variable {G : Type u} {H : Type v} [Group G] [Group H]

@[expose] def prodLeftHom : MulAut G →* MulAut (G × H) where
  toFun φ := φ.prodCongr (MulEquiv.refl H)
  map_one' := by
    ext p : 1
    rfl
  map_mul' := by
    intro φ ψ
    ext p : 1
    rfl

@[simp] theorem prodLeftHom_apply (φ : MulAut G) (p : G × H) :
    prodLeftHom φ p = (φ p.1, p.2) := rfl

theorem prodLeftHom_injective : Function.Injective (prodLeftHom (G := G) (H := H)) := by
  intro φ ψ h
  ext g : 1
  exact congrArg (fun f : MulAut (G × H) => (f (g, 1)).1) h

@[expose] def prodRightHom : MulAut H →* MulAut (G × H) where
  toFun φ := (MulEquiv.refl G).prodCongr φ
  map_one' := by apply MulEquiv.ext; intro p; rfl
  map_mul' := by intro φ ψ; apply MulEquiv.ext; intro p; rfl

@[simp] theorem prodRightHom_apply (φ : MulAut H) (p : G × H) :
    prodRightHom φ p = (p.1, φ p.2) := rfl

theorem prodRightHom_injective : Function.Injective (prodRightHom (G := G) (H := H)) := by
  intro φ ψ h
  apply MulEquiv.ext
  intro t
  exact congrArg (fun f : MulAut (G × H) => (f (1, t)).2) h

theorem card_fixed_prodRightHom (φ : MulAut H) :
    Nat.card {p : G × H // prodRightHom φ p = p} =
      Nat.card G * Nat.card {t : H // φ t = t} := by
  let e : {p : G × H // prodRightHom φ p = p} ≃ G × {t : H // φ t = t} :=
    { toFun := fun p => (p.1.1, ⟨p.1.2, congrArg Prod.snd p.2⟩)
      invFun := fun p => ⟨(p.1, p.2.1), Prod.ext rfl p.2.2⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => rfl }
  exact (Nat.card_congr e).trans (Nat.card_prod G {t : H // φ t = t})

end MulAut
