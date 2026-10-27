module

public import CFSG.Quasithin.Background.E11Stmt
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

@[expose] def Om4PlusTensor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (H C : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V), Homogeneous H → IrrPlus H I → fixedSpace H = ⊥ →
    sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤ →
    Nat.card ↥(endOn H I) = 4 → Module.finrank (ZMod 2) V = 8 →
    FaithfulOn H I → Nonempty (↥H ≃* ↥(alternatingGroup (Fin 5))) →
    C ≤ Subgroup.centralizer (H : Set (GLV V)) →
    Nonempty (↥C ≃* ↥(alternatingGroup (Fin 5))) →
    IsNaturalMatrixModule (H ⊔ C) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2)))

end SzG11S

end G11

end CFSG.Quasithin
