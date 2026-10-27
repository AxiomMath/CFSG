module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Input15204F112Untw : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    (Nonempty (OTwoQuot L1 ≃* DihedralGroup 5) ∨ Nonempty (OTwoQuot L1 ≃* ↥(CFSG.Open.Sz 0))) →
    Nonempty (OTwoQuot L2 ≃* ↥(alternatingGroup (Fin 5))) →
    (∀ s ∈ S, ∃ l ∈ L2, ∃ q ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S), s = l * q) → False

end CFSG.Quasithin.He9
