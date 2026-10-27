module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def ExcNoSuzukiReeAdj (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ s : ↥(adjointGroup τ K), s ^ p = 1 →
      ∀ C : Subgroup ↥(adjointGroup τ K), IsComponentOf C (Subgroup.centralizer {s}) →
        LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True) →
          LargeEvenMarking ↥C (fun lab _ _ _ _ _ => GGChevStTag lab)

end CFSG.StandardType
