module

public import CFSG.LocalAnalysis.WeakClosure81.W15Defs
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

@[expose] def W3Lem122Two : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {G : Type} [Group G]
    (ρ : G →* LGL 2 V) (B : Subgroup G) (Z : Submodule (ZMod 2) V) (A : Subgroup G) (n m : ℕ),
    Setting12One ρ B Z A n m → (∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤) →
    Module.finrank (ZMod 2) Z ≤ m →
    n = m ∧ Module.finrank (ZMod 2) Z = m ∧
      ∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0

variable {G : Type} [Group G] [Finite G]

@[expose] def W15Thm145 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (M V₀ V : Subgroup G), Hyp15 M V₀ V → ∀ g : G,
    InCalO1 (mSub V - 1) M V₀ V g → ¬ ⁅conjSubgroup V₀ g, V ⊓ conjSubgroup M g⁆ ≤ V₀ →
    (E3.mQuot V (conjSubgroup M g) = 1 ∧ rMV M V = (mSub V₀ : ℕ∞)) ∧
      (M ≤ normalizer ((V₀ ⊓ conjSubgroup M g : Subgroup G) : Set G) ∧
        ⁅F11.CTilde M V₀ V, V⁆ ≤ V₀ ⊓ conjSubgroup M g)

end CFSG.LocalAnalysis.WeakClosure81
