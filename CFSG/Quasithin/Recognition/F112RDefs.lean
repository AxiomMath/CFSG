module

public import CFSG.Quasithin.EmptyFaithful.S1422Elim
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.EmptyFaithful.S1421Surv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def F112R1StatementLegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S : Subgroup G),
    Hyp111 K1 L2 S → IsQuasithinSub (K1 ⊔ L2 ⊔ S) →
    (S.subgroupOf (S ⊔ borelOf L2 S)).Normal →
    K1 ∈ cComp (K1 ⊔ S) → Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3)) →
    Group.IsSolvable ↥(L2 ⊔ S) →
    ∀ Zs : Subgroup G, Nat.card Zs = 2 → Zs ≤ pCoreOf 2 L2 →
      Zs ≤ Subgroup.centralizer (pCoreOf 2 L2 : Set G) →
      ¬ L2 ≤ Subgroup.normalizer (Zs : Set G) → F112SurvivorLegacyBare K1 L2 S

@[expose] def F112R2bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M Y H : Subgroup G), Setting1422 T M Y H →
    (Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0))) →
    CaseTits H (Y ⊔ T) ∨ Case2F4 H (Y ⊔ T)

end CFSG.Quasithin
