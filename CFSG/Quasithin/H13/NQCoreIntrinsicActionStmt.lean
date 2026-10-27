module

public import CFSG.Quasithin.H13.NQTermPrimeResidualDefs
public import CFSG.Quasithin.H13.U3Local
public import CFSG.Quasithin.H13.NQBlockPrimeResidualCenter

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open

@[expose] def StmtIntrinsicActionExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M D X : Subgroup G) (p : ℕ),
    QTTMaxNQPrime T L M D p X → normalizer (D : Set G) ≠ M →
    U3.UniqueMaxTwoLocal (X ⊔ T) (normalizer (D : Set G)) →
    ⁅NQBlock.omegaOneCenterOf 2 (pCoreOf 2 X), X⁆ = ⊥

end CFSG.Quasithin.H13.NQCore
