module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S153Q

section Defs

variable {K : Type*} [Group K]

structure HatGrp (Γ Ah : Subgroup K) (z : K) : Prop where
  Ah_le : Ah ≤ Γ
  Ah_norm : ∀ g ∈ Γ, ∀ a ∈ Ah, g * a * g⁻¹ ∈ Ah
  index2 : ∀ g ∈ Γ, ∀ h ∈ Γ, g ∉ Ah → h ∉ Ah → g * h ∈ Ah
  z_mem : z ∈ Ah
  z_ne : z ≠ 1
  z_cube : z ^ 3 = 1
  z_central : ∀ g ∈ Ah, g * z = z * g
  outer : ∀ t ∈ Γ, t ∉ Ah → t * z * t⁻¹ = z⁻¹
  perfect : Ah ≤ ⁅Ah, Ah⁆
  card : Nat.card ↥Ah = 1080
  psi : ∃ ψ : ↥Ah →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ ∧
    ∀ g : ↥Ah, ψ g = 1 ↔ (g : K) ∈ Subgroup.zpowers z
  gen_odd : ∀ X : Subgroup K, (∀ x ∈ Γ, Odd (orderOf x) → x ∈ X) → Ah ≤ X

section W

variable {W : Type} [CommGroup W]

@[expose] def stab (V₁ : Subgroup W) : Subgroup (MulAut W) where
  carrier := {x | ∀ v ∈ V₁, x v ∈ V₁ ∧ x⁻¹ v ∈ V₁}
  one_mem' := fun _ hv => ⟨hv, hv⟩
  mul_mem' := fun ha hb v hv => ⟨(ha _ (hb v hv).1).1, (hb _ (ha v hv).2).2⟩
  inv_mem' := fun ha v hv => ⟨(ha v hv).2, (ha v hv).1⟩

@[expose] def IsPt (z : MulAut W) (o : Subgroup W) : Prop := Nat.card ↥o = 4 ∧ ∀ w ∈ o, z w ∈ o

structure OvalData0 (Ah : Subgroup (MulAut W)) (z : MulAut W) (lab : Fin 6 → Subgroup W) : Prop where
  pt : ∀ k, IsPt z (lab k)
  inj : Function.Injective lab
  equiv : ∀ g ∈ Ah, ∃ σ ∈ alternatingGroup (Fin 6), ∀ k, ∀ w ∈ lab k, g w ∈ lab (σ k)
  surj : ∀ σ ∈ alternatingGroup (Fin 6), ∃ g ∈ Ah, ∀ k, ∀ w ∈ lab k, g w ∈ lab (σ k)
  ker : ∀ g ∈ Ah, (∀ k, ∀ w ∈ lab k, g w ∈ lab k) → g ∈ Subgroup.zpowers z

structure OvalData (Ah : Subgroup (MulAut W)) (z : MulAut W) (lab : Fin 6 → Subgroup W) : Prop
    extends OvalData0 Ah z lab where
  arc : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → ¬ (lab c ≤ lab a ⊔ lab b)

end W

end Defs

@[expose] def HatGeomAbs : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) → Nat.card W = 2 ^ 6 →
    ∀ (Γ X P : Subgroup (MulAut W)), F6.IsHatSym 6 ↥Γ → X ≤ Γ →
    (∀ x ∈ Γ, Odd (orderOf x) → x ∈ X) → P ≤ Γ → IsPGroup 2 ↥P → P ≠ ⊥ →
    ∀ V V₁ V₂ : Subgroup W, V₁ ⊔ V₂ = V → V₁ ⊓ V₂ = ⊥ → Nat.card ↥V₁ = 4 → Nat.card ↥V₂ = 4 →
    (∀ p ∈ P, ∀ v ∈ V, p v = v) →
    (∀ x ∈ X, (∀ v ∈ V, x v ∈ V) → (∀ v ∈ V₁, x v ∈ V₁) ∨ (∀ v ∈ V₁, x v ∈ V₂)) →
    ¬ Group.IsSolvable ↥(X ⊓ stab V₁)

end S153Q

end CFSG.Quasithin
