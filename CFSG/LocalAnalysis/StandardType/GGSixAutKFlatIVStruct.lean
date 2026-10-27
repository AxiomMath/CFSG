module

public import CFSG.Assembly.LargeEvenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGStructSOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (G₀ A : Subgroup X),
    p.Prime → p ≠ 2 → IsSimpleGroup ↥G₀ → IsElemAbelian p A →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    ∀ C : Subgroup X, LargeEvenPComponent p (Subgroup.centralizer (A : Set X) ⊓ G₀) C →
      CFSG.Assembly.IsQuasisimple ↥C ∧ LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True)

end CFSG.StandardType
