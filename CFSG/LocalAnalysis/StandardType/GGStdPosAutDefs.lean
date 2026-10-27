module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

@[expose] def GGKGPosNoTrivRootStmt :
    Prop :=
  GGKGPosStep fun (G : Type) [Group G] [Finite G] (_ : ℕ) (Bs _ : Subgroup G)
      (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G) =>
    GGKGPosNoTrivRoot (ggU t n f).D ψ Bs

@[expose] def GGKGPosAutWeylStmt :
    Prop :=
  GGKGPosStep fun (G : Type) [Group G] [Finite G] (_ : ℕ) (Bs X : Subgroup G)
      (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G) =>
    ∀ ν : GGWeyl (ggU t n f).D →* (ggU t n f).K, GGWeylLift (ggU t n f).D ν →
      ∃ ε : GGWeyl (ggU t n f).D ≃* ↥(ggAutomizer X Bs), GGKGPosInduced Bs X t n f ψ ν ε

@[expose] def GGKGPosReflStmt :
    Prop :=
  GGKGPosStep fun (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G)
      (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G) =>
    ∀ (ν : GGWeyl (ggU t n f).D →* (ggU t n f).K)
      (ε : GGWeyl (ggU t n f).D ≃* ↥(ggAutomizer X Bs)),
      GGWeylLift (ggU t n f).D ν → GGKGPosInduced Bs X t n f ψ ν ε →
        ∀ i : Fin (ggU t n f).D.rank, GGIsReflection p
          ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
            MulAut ↥Bs)

end CFSG.StandardType

end
