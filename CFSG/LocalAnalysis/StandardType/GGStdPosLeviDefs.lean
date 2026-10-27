module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

@[expose] def GGKGPosLeviStmt :
    Prop :=
  GGKGPosStep fun (G : Type) [Group G] [Finite G] (_ : ℕ) (Bs X : Subgroup G)
      (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G) =>
    ∀ (ν : GGWeyl (ggU t n f).D →* (ggU t n f).K)
      (ε : GGWeyl (ggU t n f).D ≃* ↥(ggAutomizer X Bs)),
      GGWeylLift (ggU t n f).D ν → GGKGPosInduced Bs X t n f ψ ν ε →
      ∀ (w : GGWeyl (ggU t n f).D) (i : Fin (ggU t n f).D.rank),
        ggRankOneIn X Bs
            ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
              ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
          (ggRootLevi (ggU t n f).D
            (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ

end CFSG.StandardType

end
