module

public import CFSG.OddTranspositions.SixFiveWidth

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem normal_of_le_normalizer {F H K : Subgroup G} (hHK : H ⊔ K = ⊤)
    (hH : H ≤ Subgroup.normalizer (F : Set G))
    (hK : K ≤ Subgroup.normalizer (F : Set G)) : F.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hHK]
  exact sup_le hH hK

theorem commutator_zpowers_sup_eq {Q : Subgroup G} (hQ : Q.Normal) (u w : G) :
    (⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) =
      ⁅Q, Subgroup.closure ({u, w} : Set G)⁆ := by
  haveI : Q.Normal := hQ
  have huw : ({u} : Set G) ∪ {w} = {u, w} := by
    ext x
    simp [or_comm]
  rw [← Subgroup.commutator_sup_left (N := Q), Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, huw]

theorem le_normalizer_commutator_left {Q : Subgroup G} (hQ : Q.Normal) (u w : G) :
    Q ≤ Subgroup.normalizer
      ((⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G) := by
  rw [commutator_zpowers_sup_eq hQ]
  exact Subgroup.normalizer_commutator_ge_left Q _

theorem closure_pair_le_normalizer_commutator {Q : Subgroup G} (hQ : Q.Normal) (u w : G) :
    Subgroup.closure ({u, w} : Set G) ≤ Subgroup.normalizer
      ((⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G) := by
  rw [commutator_zpowers_sup_eq hQ]
  exact Subgroup.normalizer_commutator_ge_right Q _

theorem sixFive_F_normal {Q : Subgroup G} (hQ : Q.Normal) {u w : G}
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤) :
    (⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G).Normal :=
  normal_of_le_normalizer hgenQ (le_normalizer_commutator_left hQ u w)
    (closure_pair_le_normalizer_commutator hQ u w)

theorem sixFive_widthStep' (hS : Setup G D) {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G)
    {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤) :
    Q ≤ ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ :=
  sixFive_widthStep hS hQ hu hw hnc hgenQ
    (sixFive_F_normal (by rw [hQ]; exact CFSG.pCore_normal) hgenQ)

theorem sixFive_pCore_eq (hS : Setup G D) {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G)
    {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ := by
  have hQn : Q.Normal := by rw [hQ]; exact CFSG.pCore_normal
  exact le_antisymm (sixFive_widthStep' hS hQ hu hw hnc hgenQ)
    (sup_le (commutator_zpowers_le_of_normal hQn u) (commutator_zpowers_le_of_normal hQn w))

theorem sixFiveGlobal_of_inputs' (hS : Setup G D)
    {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G) {u w : G}
    (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hPR : ⁅Q, Subgroup.zpowers u⁆ ≤
      Subgroup.normalizer ((⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G))
    (hZc : (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) ≤ Subgroup.center G)
    (hZtop : Subgroup.center G ≤
      (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G))
    (hcardP : Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard *
        Nat.card (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G)) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ ∧
      Subgroup.center G = ⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ ∧
      Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
        Nat.card (Subgroup.center G) :=
  sixFiveGlobal_of_normalF hS hQ hu hw hnc hgenQ
    (sixFive_F_normal (by rw [hQ]; exact CFSG.pCore_normal) hgenQ) hPR hZc hZtop hcardP

theorem sixFive_hPR {Q : Subgroup G} (hQ : Q.Normal) (u w : G) :
    ⁅Q, Subgroup.zpowers u⁆ ≤
      Subgroup.normalizer ((⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G) :=
  (commutator_zpowers_le_of_normal hQ u).trans
    (Subgroup.normalizer_commutator_ge_left Q (Subgroup.zpowers w))

theorem sixFiveGlobal_of_center_inputs (hS : Setup G D)
    {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G) {u w : G}
    (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hZc : (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) ≤ Subgroup.center G)
    (hZtop : Subgroup.center G ≤
      (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G))
    (hcardP : Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard *
        Nat.card (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G)) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ ∧
      Subgroup.center G = ⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ ∧
      Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
        Nat.card (Subgroup.center G) :=
  sixFiveGlobal_of_inputs' hS hQ hu hw hnc hgenQ
    (sixFive_hPR (by rw [hQ]; exact CFSG.pCore_normal) u w) hZc hZtop hcardP

end CFSG.OddTranspositions
