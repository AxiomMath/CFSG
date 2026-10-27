module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def GGKGPosCardStmt :
    Prop :=
  GGKGPosStep fun (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G)
      (t : StatedLieTag) (n f : ℕ) (_ : (ggU t n f).K →* G) =>
    Nat.card ↥Bs ≤ p ^ (ggU t n f).D.rank * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G))

end CFSG.StandardType

end
