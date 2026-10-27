module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def partOf {τ : Tag} (K : KacData τ) (D : Set (Option (Fin τ.rank))) (l : ℤ) :
    Set (Fin τ.rank → ℤ) :=
  {β | β ∈ K.rootsOf D ∧ iform β β = l}

@[expose] def ExcRankOK (τ : Tag) (k : ℕ) : Prop :=
  3 ≤ k ∧ τ.rank ≤ k + 2 ∧ (τ.rank ≤ k + 1 ∨ τ = Tag.E6)

@[expose] def ExcFinite
    (τ : Tag) (K : KacData τ) : Prop :=
  ∀ (D : Finset (Option (Fin τ.rank))) (l : ℤ), D ≠ Finset.univ →
    (∀ α ∈ partOf K D l, ∀ β ∈ partOf K D l,
      Relation.ReflTransGen (fun a b => b ∈ partOf K D l ∧ iform a b ≠ 0) α β) →
    (∃ s : Finset (Fin τ.rank → ℤ), (s : Set (Fin τ.rank → ℤ)) ⊆ partOf K D l ∧
      LinearIndependent ℚ (fun v : s => (fun i => ((v : Fin τ.rank → ℤ) i : ℚ))) ∧
      ExcRankOK τ s.card) →
    TCRoot (isFiniteType_cartan τ) (partOf K D l)

end CFSG.StandardType.LevTwo
