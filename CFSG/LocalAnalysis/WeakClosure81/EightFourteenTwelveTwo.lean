module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.LocalAnalysis.WeakClosure81.Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

@[expose] def W3Lem122One : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {G : Type} [Group G]
    (ρ : G →* LGL 2 V) (B : Subgroup G) (Z : Submodule (ZMod 2) V) (A : Subgroup G) (n m : ℕ),
    Setting12One ρ B Z A n m → (∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤) →
    IsSumNatSection ρ ⊥ (commSub ((⊤ : Subgroup G).map ρ)) (cE ((⊤ : Subgroup G).map ρ)) n

end CFSG.LocalAnalysis.WeakClosure81

end
