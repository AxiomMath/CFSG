module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
import Mathlib.GroupTheory.FiniteAbelian.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

@[expose] def K332S : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ → CFSG.Open.pRank 3 S ≤ 3 →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    Disjoint (Z.subgroupOf S) (commutator ↥S) →
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1

theorem k332Cyc_of_k332S (h : K332S) : K332Cyc := by
  intro G _ _ hK S hS hrk Z hZS hZ3 hwc Q _ hQ φ hdisj
  haveI : CommGroup Q := IsCyclic.commGroup
  exact h G hK S hS hrk Z hZS hZ3 hwc
    (Disjoint.mono_right (Abelianization.commutator_subset_ker φ) hdisj)

end CFSG.LocalAnalysis.UniquenessCase.UCK
