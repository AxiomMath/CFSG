module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] def F112HypW (L1 L2 S : Subgroup G) : Prop :=
  Hyp111 L1 L2 S ∧
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal)

theorem F112Hyp.toW [Finite G] {L1 L2 S : Subgroup G} (h : F112Hyp L1 L2 S) :
    F112HypW L1 L2 S :=
  ⟨h.1, h.2.2⟩

theorem F112HypW.symm {L1 L2 S : Subgroup G} (h : F112HypW L1 L2 S) : F112HypW L2 L1 S :=
  ⟨h.1.symm, h.2.symm⟩

end CFSG.Quasithin
