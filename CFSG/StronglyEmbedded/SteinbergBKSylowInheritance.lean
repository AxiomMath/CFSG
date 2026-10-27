module

public import CFSG.GroupTheory.SteinbergBKStronglyEmbeddedCore

public section

namespace CFSG.StronglyEmbedded.SteinbergBK

variable {G : Type*} [Group G]

theorem strongly_embedded_sylow_inheritance [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) :
    (∀ S : Sylow 2 H, ∃ P : Sylow 2 G, (P : Subgroup G) = (S : Subgroup H).map H.subtype) ∧
      Odd H.index :=
  ⟨fun S => CFSG.OrderReductions.StrongEmbedding.sylow_inheritance H
      ((CFSG.GroupTheory.SteinbergBK.isStronglyEmbedded_iff H).mp hH) S,
    CFSG.OrderReductions.StrongEmbedding.odd_index H
      ((CFSG.GroupTheory.SteinbergBK.isStronglyEmbedded_iff H).mp hH)⟩

end CFSG.StronglyEmbedded.SteinbergBK
