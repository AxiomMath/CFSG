module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def GGNbrLSideRSExcExcl : Prop :=
  ∀ {X : Type} [Group X] {F : Type} [Field F] [Finite F], 4 ≤ Nat.card F →
    X ≃* projectiveSL 3 F → ∀ {t : StatedLieTag} {m f : ℕ},
      CFSG.Blueprint.LieModel X t m 2 f → t = .PSL ∧ m = 3 ∧ Nat.card F = 2 ^ f

end CFSG.StandardType
