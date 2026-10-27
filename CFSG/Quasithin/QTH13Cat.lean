module

public import CFSG.Open.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped MatrixGroups

structure quasithinQTH13Cat (G : Type) [Group G] [Finite G] (T L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  faithful : quasithinIsFaithfulLocal T L
  not_excluded : Nat.card G ∉ quasithinH13ExcludedOrders
  a5 : quasithinO2QuotientIso L (alternatingGroup (Fin 5)) →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      quasithinO2QuotientIso K (alternatingGroup (Fin 5))

@[expose] def QTH13MilestoneCat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G),
    quasithinQTH13Cat G T L → quasithinIsMaximalLocal T L →
      Nonempty (G ≃* Matrix.symplecticGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* quasithinPSU 4 3 1) ∨
      Nonempty (G ≃* quasithinPSU 4 2 1) ∨
      Nonempty (G ≃* PSL(4, ZMod 3)) ∨
      Nonempty (G ≃* quasithinG2 (ZMod 3)) ∨
      Nonempty (G ≃* quasithinHS) ∨
      Nonempty (G ≃* quasithinRu)

theorem quasithinQTH13Cat.qtkeCore {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (h : quasithinQTH13Cat G T L) : QuasithinUnique.QTKECore G :=
  have := h.simple
  QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke

end CFSG.Quasithin
