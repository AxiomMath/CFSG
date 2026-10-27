module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
public import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenO2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.RankThree.OrthogonalInvolutions
open Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem not_centerIn_le_Q_of_Rbar_ne_bot (S : Setting z E F) {a : G}
    (hza : z ∈ QaOf a) (hR : Rbar S a ≠ ⊥) :
    ¬ centerIn (QaOf a) ≤ Q z := by
  intro h
  exact hR (rbar_eq_bot_of_centerIn_le_Q S a h)

theorem commutator_Lbar_Y_eq_one_of_Rbar_ne_bot (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (Y : Subgroup (Hbar z))
    (hO2' : ∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
      Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥)
    (hY2 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v : Additive (QbarOf S),
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        ((((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v) =
      (((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v)
    (ha_not : Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∉
      Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v})
    (hL : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)))
    (hR : Rbar S a ≠ ⊥) :
    ∀ l ∈ Lbar S a, ∀ y ∈ Y, Commute l y := by
  have hZQa : ¬ centerIn (QaOf a) ≤ Q z := not_centerIn_le_Q_of_Rbar_ne_bot S hza hR
  have hact := commutator_Lbar_span_sub_eq S haQ hconj haZ hza hZQa hR Y hY2 ha_not hL
  exact commutator_Lbar_Y_eq_one_of_O2_of_le_normalizer S haQ hconj hza Y hO2'
    (fun l hl y hy v => hact l hl _ (Submodule.subset_span ⟨y, hy, v, rfl⟩)) hL

end CFSG.RankThree.GF2n.Stroth78
