module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Dichotomy
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.StronglyEmbedded.ParityCriterion

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem lemma_6_12 (h : Counterexample p A θ) {X : Subgroup G}
    (hX : ∃ T ⊆ Msig p A θ, X = sSup T) :
    ((∀ Y ∈ Msig p A θ, Y ≤ X) ∧ X ∉ Msig p A θ) ∨
      (X ∈ Msig p A θ ∧ ∀ B ∈ signalizerFunctorEk p 2 A, ∃ a ∈ B, a ≠ 1 ∧ ¬ θ a ≤ X) := by
  rcases glauberman_dichotomy h.prime h.elemAbelian h.rank_two_le h.isFunctor h.hypC
    (fun _ _ hYX _ hXB => hypB_mono hYX hXB) h.notComplete h.hmin hX with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, fun B hB => h3 B hB.1 hB.2.ge⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
