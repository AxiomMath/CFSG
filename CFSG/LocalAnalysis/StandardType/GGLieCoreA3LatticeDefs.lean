module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open Matrix

@[expose] def a3Ker (τ : Tag) (c₁ c₂ : Fin τ.rank → ZMod 3) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ ggLiePair γ c₁ = 0 ∧ ggLiePair γ c₂ = 0}

@[expose] def a3Comp (τ : Tag) (c₁ c₂ : Fin τ.rank → ZMod 3) (m : Fin τ.rank → ℤ) :
    Set (Fin τ.rank → ℤ) :=
  {δ | δ ∈ a3Ker τ c₁ c₂ ∧ Relation.EqvGen (fun α β : Fin τ.rank → ℤ =>
    α ∈ a3Ker τ c₁ c₂ ∧ β ∈ a3Ker τ c₁ c₂ ∧ α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) ≠ 0) m δ}

@[expose] def A3SpecF4 : Prop :=
  ∀ c₁ c₂ : Fin (langTag .F4).rank → ZMod 3, (∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0) →
    ∀ m ∈ a3Ker (langTag .F4) c₁ c₂, (a3Comp (langTag .F4) c₁ c₂ m).ncard ≠ 12

@[expose] def A3SpecTwE6 : Prop :=
  ∀ (w : WeylGroup (langTag .twistedE6)) (c₁ c₂ : Fin (langTag .twistedE6).rank → ZMod 3),
    (∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0) →
    (∀ γ, IsRoot (langTag .twistedE6) γ →
      ggLiePair (w • ggGraphLat .twistedE6 γ) c₁ = 2 * ggLiePair γ c₁) →
    (∀ γ, IsRoot (langTag .twistedE6) γ →
      ggLiePair (w • ggGraphLat .twistedE6 γ) c₂ = 2 * ggLiePair γ c₂) →
    ∀ m ∈ a3Ker (langTag .twistedE6) c₁ c₂,
      (a3Comp (langTag .twistedE6) c₁ c₂ m).ncard = 12 →
      (fun u => w • ggGraphLat .twistedE6 u) '' a3Comp (langTag .twistedE6) c₁ c₂ m =
        a3Comp (langTag .twistedE6) c₁ c₂ m →
      twistInner (a3Comp (langTag .twistedE6) c₁ c₂ m)
        (fun u => w • ggGraphLat .twistedE6 u) → False

end CFSG.StandardType.LieCore
