module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def nonTwoConj (A H : Subgroup G) : Set G :=
  {h | h ∈ H ∧ ¬ IsPGroup 2 ↥(A ⊔ conjSubgroup A h)}

@[expose] def ClaimCE1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S A H : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥X → IsSylowTwoOf S X → A ≤ S → IsElemAbelian 2 A →
    ¬ A ≤ pCoreOf 2 X → E1.IsE 1 X S A H → A ≤ H →
    twoResidual H ≤ Subgroup.closure (nonTwoConj A H)

end CFSG.Quasithin.F7Two
