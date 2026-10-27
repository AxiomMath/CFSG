module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofIn
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)

open Res417Three Res417Five

namespace Res417Five

@[expose] def K417CoverE35 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    (Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.McL)) →
    ∃ P E₀ T₀ : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 5 ∧ E₀ ≤ P ∧
      Nat.card E₀ = 9 ∧ E₀ ⊓ Subgroup.center X = ⊥ ∧ IsPGroup 2 T₀ ∧
      E₀ ≤ Subgroup.normalizer (T₀ : Set X) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set X)

end Res417Five

section Certs


theorem item417InU43McLRest_of (hK : K417CoverE35) : Item417InU43McLRest := by
  intro G _ _ L A E c m hconf hZ hX
  obtain ⟨P, E₀, T₀, hP, hP5, hE₀P, hE₀9, hE₀Z, hT₀, hE₀T₀, hT₀E₀⟩ :=
    hK L hconf.2.2.1.1 hZ hX
  have hcC := hconf.mem_centralizer
  have hc3 : orderOf c = 3 := hconf.2.2.2.2.1.2.2.2.1
  have hPL : P.map L.subtype ≤ L := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hE₀C : E₀.map L.subtype ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have hz : x ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    have hx1 : x ∈ E₀ ⊓ Subgroup.center L := ⟨hx, hz⟩
    rw [hE₀Z, Subgroup.mem_bot] at hx1
    rw [Subgroup.mem_bot, hx1, map_one]
  refine false_of_star417 hconf.1 hconf.2.2.2.1 hcC hc3 (isElemAbelian_map L.subtype hP)
    (fun a ha => Subgroup.mem_centralizer_iff.mp hcC a (hPL ha)) (Subgroup.map_mono hE₀P)
    (by rw [Subgroup.card_map_of_injective L.subtype_injective, hE₀9]) hE₀C
    (T₀ := T₀.map L.subtype) (by rintro _ ⟨x, -, rfl⟩; exact x.2) (hT₀.map _)
    ((Subgroup.map_mono hE₀T₀).trans (Subgroup.le_normalizer_map _)) (fun hle => hT₀E₀ ?_) ?_
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    apply L.subtype_injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (hle ⟨t, ht, rfl⟩) (L.subtype e) ⟨e, he, rfl⟩
  · calc 3 ^ 5 = Nat.card (P.map L.subtype) := by
          rw [Subgroup.card_map_of_injective L.subtype_injective, hP5]
      _ ≤ Nat.card (P.map L.subtype ⊔ Subgroup.zpowers c : Subgroup G) :=
          Subgroup.card_le_of_le le_sup_left

end Certs

end CFSG.RankThree.PartTwo.Sec4
