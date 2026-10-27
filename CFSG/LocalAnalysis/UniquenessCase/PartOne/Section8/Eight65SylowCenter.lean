module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

@[expose] def SylowCenterWeaklyClosed (Y : Type) [Group Y] : Prop :=
  ∀ (Q : Sylow 3 Y) (Z : Subgroup Y), Z ≤ (Q : Subgroup Y) →
    Z ≤ Subgroup.centralizer ((Q : Subgroup Y) : Set Y) → Nat.card Z = 3 →
    ∀ g : Y, CFSG.conjugate Z g ≤ (Q : Subgroup Y) → CFSG.conjugate Z g = Z

@[expose] def SylowCenterInverted (Y : Type) [Group Y] : Prop :=
  ∀ (Q : Sylow 3 Y) (z : Y), z ∈ (Q : Subgroup Y) →
    z ∈ Subgroup.centralizer ((Q : Subgroup Y) : Set Y) → orderOf z = 3 →
    ∃ t : Y, t * z * t⁻¹ = z⁻¹

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
