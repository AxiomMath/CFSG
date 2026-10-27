module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChH.Transport

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V]

@[expose] def Clause3Gen (M L : Subgroup (MulAut V)) (V1 V2 : Subgroup V)
    (perp : Subgroup V → Subgroup V) (c : ℕ) (Q : Type*) [Group Q] {A : Type*} [CommGroup A]
    (Γ : Subgroup (MulAut A)) (T : Subgroup (MulAut V)) (v₁ : V) : Prop :=
  (M ⊓ centSub (Subgroup.zpowers v₁) = twoResidual (L ⊓ centSub (Subgroup.zpowers v₁)) ∧
    (∃ E : Subgroup (MulAut V), IsElemAbelian 2 E ∧ Nat.card E = c ∧
      IsExtOf (M ⊓ centSub (Subgroup.zpowers v₁)) E Q) ∧
    commOn V1 (twoResidual (L ⊓ centSub (Subgroup.zpowers v₁))) = V1 ∧
    commOn V2 (twoResidual (L ⊓ centSub (Subgroup.zpowers v₁))) =
      V2 ⊓ perp (Subgroup.zpowers v₁) ∧
    (V2 ⊓ perp (Subgroup.zpowers v₁)).relIndex V2 = 2 ∧
    InducesOn (twoResidual (L ⊓ centSub (Subgroup.zpowers v₁)))
      (commOn V2 (twoResidual (L ⊓ centSub (Subgroup.zpowers v₁)))) ⊥ A Γ ∧
    T ⊓ stabSub V1 = T ⊓ centSub (Subgroup.zpowers v₁) ∧
    IsSylowIn 2 (T ⊓ stabSub V1) (M ⊓ centSub (Subgroup.zpowers v₁)))

@[expose] def Clause4Gen (M L : Subgroup (MulAut V)) (V1 V2 : Subgroup V)
    (perp : Subgroup V → Subgroup V) (polar : V → V → ZMod 2) (Orb : Set V)
    (X : Type*) [Group X] {A : Type*} [CommGroup A] (Γ : Subgroup (MulAut A))
    (T : Subgroup (MulAut V)) (v₁ v₂ : V) : Prop :=
  v₁ * v₂ ∈ Orb ∧
  (∃ S : Subgroup (MulAut V),
    IsSylowIn 2 S (M ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ∧
    S ⊓ L = T ⊓ centSub (Subgroup.zpowers (v₁ * v₂)) ∧
    ∃ t ∈ S, t ∉ L ∧ t ^ 2 = 1 ∧ t v₁ = v₂ ∧ t v₂ = v₁ ∧
    M ⊓ centSub (Subgroup.zpowers (v₁ * v₂)) =
      Subgroup.zpowers t ⊔ twoResidual (L ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ∧
    Nonempty (↥(M ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ≃* X) ∧
    twoResidual (L ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) =
      twoResidual (M ⊓ centSub (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
    IsSylowIn 2 (T ⊓ centSub (Subgroup.zpowers (v₁ * v₂)))
      (twoResidual (L ⊓ centSub (Subgroup.zpowers (v₁ * v₂))))) ∧
  (V1 = Subgroup.zpowers v₁ ⊔ (V1 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
    Subgroup.zpowers v₁ ⊓ (V1 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) = ⊥ ∧
    V2 = Subgroup.zpowers v₂ ⊔ (V2 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
    Subgroup.zpowers v₂ ⊓ (V2 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) = ⊥) ∧
  InducesOn (twoResidual (L ⊓ centSub (Subgroup.zpowers (v₁ * v₂))))
    (V1 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ⊥ A Γ ∧
  ((∀ w ∈ V1 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), w ≠ 1 →
      ∃ w' ∈ V2 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), polar w w' ≠ 0) ∧
    (∀ w' ∈ V2 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), w' ≠ 1 →
      ∃ w ∈ V1 ⊓ perp (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), polar w w' ≠ 0))

end CFSG.ASVolI.ChH.Transport
