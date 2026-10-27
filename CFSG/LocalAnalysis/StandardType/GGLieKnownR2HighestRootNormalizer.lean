module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcCore
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis CFSG.StandardType.GGOppRadExc

@[expose] def thetaPerpF (τ : Tag) : Finset (Fin τ.rank) :=
  Finset.univ.filter fun i => ∑ k, Tag.cartan τ i k * highRoot τ k = 0

theorem jθ_eq_thetaPerpF (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    Jθ τ = (thetaPerpF τ : Set (Fin τ.rank)) := by
  rcases hτ with rfl | rfl | rfl <;>
  · ext i
    simp only [Jθ, thetaPerpF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    revert i
    decide +kernel

theorem even_highest_root_normalizer
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) ⊓
        adjointGroup τ K = parabolicSubgroup τ K (Jθ τ) ∧
      pCoreOf 2 (parabolicSubgroup τ K (Jθ τ)) =
        parabolicRadical τ K (Jθ τ) ⊓ adjointGroup τ K := by
  refine ⟨by rw [inf_comm]; exact (Pθ_eq_inf_normalizer τ K).symm, ?_⟩
  rw [pCoreOf_parabolicSubgroup, inf_eq_left.2
    ((parabolicRadical_le_posUnipotent _).trans (posUnipotent_le_adjointGroup (τ := τ) (K := K)))]

theorem even_exc_highest_root_normalizer
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) ⊓
        adjointGroup τ K = parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank)) ∧
      pCoreOf 2 (parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank))) =
        parabolicRadical τ K (thetaPerpF τ : Set (Fin τ.rank)) ⊓ adjointGroup τ K := by
  rw [← jθ_eq_thetaPerpF τ hτ]
  exact even_highest_root_normalizer τ K

end CFSG.StandardType.LieKnownR2
