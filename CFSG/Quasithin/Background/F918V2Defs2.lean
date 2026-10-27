module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.Z391

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def EndUnitsTrivial (Λ : Subgroup Γ) (P : Subgroup Q) : Prop :=
  ∀ φ : ↥P ≃* ↥P, (∀ (l : ↥Λ) (x y : ↥P), l • (x : Q) = (y : Q) →
    l • ((φ x : ↥P) : Q) = ((φ y : ↥P) : Q)) → φ = MulEquiv.refl _

@[expose] def AutFromGroup (Λ : Subgroup Γ) (P : Subgroup Q) : Prop :=
  ∀ h : ↥P ≃* ↥P, ∃ l ∈ Λ, ∀ x : ↥P, ((h x : ↥P) : Q) = l • (x : Q)

@[expose] def FaithfulOn (Λ : Subgroup Γ) (P : Subgroup Q) : Prop :=
  ∀ l ∈ Λ, (∀ x ∈ P, l • x = x) → l = 1

end CFSG.Quasithin.Z391
