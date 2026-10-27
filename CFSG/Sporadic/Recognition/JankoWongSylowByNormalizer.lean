module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup

theorem card_eq_pow_factorization_of_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {W B : Subgroup G} (hW : IsPGroup p W) (hWB : W ≤ B)
    (hmax : ∀ R : Subgroup G, R ≤ B → IsPGroup p R → Nat.card R ≤ Nat.card W)
    (hN : Subgroup.normalizer (W : Set G) ≤ B) :
    Nat.card W = p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hWP⟩ := hW.exists_le_sylow
  by_cases hWeq : W = (P : Subgroup G)
  · rw [hWeq]
    exact P.card_eq_multiplicity
  · exfalso
    have hnil : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
    have hlt : W.subgroupOf P < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hWeq (le_antisymm hWP (subgroupOf_eq_top.mp h))
    have hgrow := Group.normalizerCondition_of_isNilpotent _ hlt
    rw [← subgroupOf_normalizer_eq hWP] at hgrow
    obtain ⟨⟨g, hgP⟩, hgN, hgW⟩ := IsConcreteLE.exists_of_lt hgrow
    have hRP : W ⊔ zpowers g ≤ P := sup_le hWP (zpowers_le.mpr hgP)
    have hRB : W ⊔ zpowers g ≤ B := sup_le hWB (zpowers_le.mpr (hN hgN))
    have hcard := hmax _ hRB (P.isPGroup'.to_le hRP)
    exact hgW (eq_of_le_of_card_ge le_sup_left hcard ▸ mem_sup_right (mem_zpowers g))

end CFSG.Sporadic.Recognition.JankoWong
