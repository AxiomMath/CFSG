module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6A5

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc.E6Three E6TwoPilot

section Inputs


@[expose] def GGE6TwoD4NodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (h2 : (2 : K) = 0), Nat.card K = 2 →
    NodeCount 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd d2E6))

@[expose] def GGE6TwoIsoNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (h2 : (2 : K) = 0), Nat.card K = 2 →
    ¬ (IsComponentOf (LargeEvenLayer (Subgroup.centralizer
          ({torusE6Two h2 (.ofAdd d0E6)} : Set (adjointGroup .E6 K))))
        (Subgroup.centralizer ({torusE6Two h2 (.ofAdd d0E6)} : Set (adjointGroup .E6 K))) ∧
      ∀ s ∈ (torusE6Two (K := K) h2).range,
        ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer
            ({torusE6Two h2 (.ofAdd d0E6)} : Set (adjointGroup .E6 K))), s * j = j * s) ↔
          s ∈ Subgroup.zpowers (torusE6Two h2 (.ofAdd d0E6))))

end Inputs

section Counts

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nodeCount_torusE6Two (hD4 : GGE6TwoD4NodeInput) (hIso : GGE6TwoIsoNodeInput)
    (h2 : (2 : K) = 0) (hK : Nat.card K = 2) {v : Fin 4 → ZMod 3} (hv : v ≠ 0) :
    NodeCount 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd v)) := by
  have hcase : normE6 v = 1 ∨ normE6 v = 2 ∨ normE6 v = 0 := by
    generalize normE6 v = z
    revert z
    decide
  rcases hcase with h | h | h
  · exact nodeCount_norm_one h2 hK h
  · obtain ⟨g, hg, hgv⟩ := inOrbit_of_reachB h2 d2E6 5 v (reachB_two v h)
    exact nodeCount_of_normalizer hg hgv (hD4 K h2 hK)
  · obtain ⟨g, hg, hgv⟩ := inOrbit_of_reachB h2 d0E6 4 v (reachB_zero v h hv)
    exact nodeCount_of_normalizer hg hgv (fun hc hs => absurd ⟨hc, hs⟩ (hIso K h2 hK))

end Counts

end CFSG.StandardType.SmallExc

end
