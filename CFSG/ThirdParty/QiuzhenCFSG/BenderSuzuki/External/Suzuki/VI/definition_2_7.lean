module

public import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI, Definition 2.7

The source definition of a trivial-intersection subset relative to an ambient
group and a subgroup.
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u

/-- Suzuki, *Group Theory II*, Chapter 6, Definition 2.7. -/
@[expose] public def IsTISubsetRelative
    {G : Type u} [Group G] (H : Subgroup G) (K : Set G) : Prop :=
  K ⊆ H ∧
    Subgroup.normalizer K = H ∧
    (∀ {x y : G}, x ∈ K → y ∈ K →
      (∃ g : G, g * x * g⁻¹ = y) →
        ∃ h : H, (h : G) * x * (h : G)⁻¹ = y) ∧
    ∀ x : G, x ∈ K → x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ H

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
