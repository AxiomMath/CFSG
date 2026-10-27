module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley

@[expose] def a1Nodes (τ : Tag) : Set (Fin τ.rank) := {i | i.val ∈ ({1, 4, 6} : Set ℕ)}

end CFSG.RankThree.PartOne.KE
