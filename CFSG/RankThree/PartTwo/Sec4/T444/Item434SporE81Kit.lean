module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Item434Kit Item434Alt Item434Spor

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem false_of_e81 (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : P.map (MulAut.conj : X →* MulAut X) = A.map (quotConj e))
    {B E : Subgroup X} (hBP : B ≤ P) (hB9 : 9 ≤ Nat.card B)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : 81 ≤ Nat.card E)
    (hBE : ∀ b ∈ B, ∀ d ∈ E, b * d = d * b) : False := by
  set F := B.map (MulAut.conj : X →* MulAut X) with hF
  have hFA : F ≤ A.map (quotConj e) := hP ▸ Subgroup.map_mono hBP
  have hF9 : 9 ≤ Nat.card F := by
    rw [hF, Subgroup.card_map_of_injective (conj_injective_of_center_eq_bot hcen)]
    exact hB9
  refine false_of_fixed h hZ e inf_le_left (hF9.trans (card_le_card_inf_comap e hFA)) hE hE81 ?_
  intro a ha d hd
  obtain ⟨β, hβ, hβa⟩ := ha.2
  rw [← hβa, MulAut.conj_apply, hBE β hβ d hd, mul_inv_cancel_right]

theorem false_of_e27 {W : Type*} [Group W] {J : Subgroup W} [Finite J] (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* J) (hcen : Subgroup.center J = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer J))
    (hE : ∀ P : Subgroup J, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 27 →
      ∃ B E : Subgroup J, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
        81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b)
    (hZ : Subgroup.center (layer G) = ⊥) (h27 : Nat.card h.layerStar = 27) : False := by
  have h27' : Nat.card (A.map (quotConj e)) = 27 := by rw [card_map_quotConj h e]; exact h27
  set P := (A.map (quotConj e)).comap (MulAut.conj : J →* MulAut J) with hPdef
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h27']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e)
  obtain ⟨B, E, hBP, hB9, hEe, hE81, hBE⟩ := hE P hPe hP27
  exact false_of_e81 h hZ e hcen hPmap hBP hB9 hEe hE81 hBE

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
