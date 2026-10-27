module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.Quasithin.F7Two

variable {Γ : Type*} [Group Γ]

@[expose] def invXi (L : Subgroup Γ) (a : Γ) : Set Γ :=
  {x | x ∈ L ∧ ¬ IsPGroup 2 ↥(Subgroup.zpowers (a * x * a⁻¹ * x⁻¹))}

@[expose] def InvGen (L : Subgroup Γ) (a : Γ) : Prop :=
  Subgroup.closure (invXi L a) = L

@[expose] def InvAutGen (L : Type*) [Group L] (φ : MulAut L) : Prop :=
  Subgroup.closure {x : L | ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹))} = ⊤

@[expose] def InvAutGenSQTK : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
    ∀ (H : Subgroup X) (N : Subgroup H) [N.Normal], IsSimpleGroup (H ⧸ N) →
      (∃ x y : H ⧸ N, x * y ≠ y * x) →
      ∀ φ : MulAut (H ⧸ N), φ * φ = 1 → φ ≠ 1 → InvAutGen (H ⧸ N) φ

end CFSG.Quasithin.F7Two
