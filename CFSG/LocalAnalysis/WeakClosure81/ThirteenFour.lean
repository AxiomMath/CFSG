module

public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

@[expose] def SevenSixThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), Hyp7 V →
    ∀ (H E J A Y : Subgroup G) (p : ℕ), p.Prime → p ≠ 2 →
      E ≤ H → (E.subgroupOf H).Normal → IsMulCommutative E →
      iSub V H E ≤ J → J ≤ pCoreOf 2 H → (J.subgroupOf H).Normal →
      A ∈ omegaSet V H E → A ≤ H → J.relIndex A = 2 →
      J ≤ Y → Y ≤ H → A ≤ normalizer (Y : Set G) → Y ≤ ⁅Y, A⁆ ⊔ J →
      (∀ a ∈ A, (∀ y ∈ Y, ⁅a, y⁆ ∈ J) → a ∈ J) →
      (∀ y ∈ Y, y ^ p ∈ J) → (∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ⁅⁅x, y⁆, z⁆ ∈ J) →
      J.relIndex Y = p ∨ (J.relIndex Y = p ^ 3 ∧ ∃ y ∈ Y, ∃ z ∈ Y, ⁅y, z⁆ ∉ J)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

end CFSG.LocalAnalysis.WeakClosure81
