module

public import CFSG.Quasithin.H13.U3L14Set
public import CFSG.Quasithin.H13.A6Realize

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Set14ProducerA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) [IsMulCommutative ↥V],
    QTH13 G T L → IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ centralizer (L : Set G) = ⊥ → A6.IsV2 T V V₂ →
    AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 →
      ∃ V₃ Lp : Subgroup G, Set14 G T L V V₂ V₃ Lp

@[expose] def Set14ProducerL32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) [IsMulCommutative ↥V],
    QTH13 G T L → IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ centralizer (L : Set G) = ⊥ → A6.IsV2 T V V₂ →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
    BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1 →
      ∃ V₃ Lp : Subgroup G, Set14 G T L V V₂ V₃ Lp

@[expose] def Set14ProducerU33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) [IsMulCommutative ↥V],
    QTH13 G T L → IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
    V ⊓ centralizer (L : Set G) = ⊥ → A6.IsV2 T V V₂ →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
    G2NaturalDerived (V := ↥V) (autOn L V) ⊤ ⊥ 1 →
      ∃ V₃ Lp : Subgroup G, Set14 G T L V V₂ V₃ Lp

theorem exists_set14_of_producers (h1332 : Stmt13_3_2)
    (hA6 : Set14ProducerA6) (hL32 : Set14ProducerL32) (hU33 : Set14ProducerU33)
    {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥) (hV2 : A6.IsV2 T V V₂)
    (hA5 : IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5)))) :
    ∃ V₃ Lp : Subgroup G, Set14 G T L V V₂ V₃ Lp := by
  obtain ⟨-, -, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hab, hmod⟩ := hall V hV
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, hn, -⟩ | ⟨hu, hg, -⟩
  · exfalso
    obtain ⟨e⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) h5
    exact hA5.false e
  · exact hA6 G T L V V₂ hH hV hZV hV2 h6
  · exfalso
    rw [hZV, card_bot] at hc2
    exact absurd hc2 (by norm_num)
  · exact hL32 G T L V V₂ hH hV hZV hV2 hl hn
  · exact hU33 G T L V V₂ hH hV hZV hV2 hu hg

end CFSG.Quasithin.H13.U3
