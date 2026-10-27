module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UA312
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem a312Out_of_case (hM : FactMathieuOrders) {K Y : Type} [Group K] [Group Y] [Finite Y]
    [IsSimpleGroup Y] [Group.IsPerfect K] (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup K}
    [N.Normal] (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (ψ : K →* Y)
    (hψ : Function.Surjective ψ) {Γ : Type} [Group Γ] [Finite Γ] {B L : Subgroup Γ}
    (σ : K →* ↥B) (hσ : Function.Surjective σ) (hcase : A312Case B L) : A312Out Y := by
  set σ2 := (QuotientGroup.mk' (CFSG.pCore 2 ↥B)).comp σ with hσ2def
  have hσ2 : Function.Surjective σ2 := (QuotientGroup.mk'_surjective _).comp hσ
  unfold A312Case A312C2 A312C3 A312C4 A312C5 A312C6 A312C7 A312C8 A312C9 A312C10 A312C11
    A312C12 A312C13 A312C14 A312C15 A312C16 A312C17 A312C18 A312C19 A312C20 at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨⟨n, hn⟩, -, -⟩ := h
    exact out_psl22 hY hN hQ ψ hψ σ2 hσ2 hn
  · obtain ⟨f, hf, -, -⟩ := h
    exact out_sz hY hN hQ ψ hψ σ2 hσ2 hf
  · obtain ⟨hB, -, -⟩ := h
    exact out_card hY hN hQ ψ hψ σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)
  · obtain ⟨hB, -, -⟩ := h
    exact out_card hY hN hQ ψ hψ σ2 hσ2 (card_isPSL_four_two_one hB) (by norm_num) (by norm_num)
  · obtain ⟨hB | hB, -⟩ := h
    · exact out_alt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
    · exact out_card hY hN hQ ψ hψ σ hσ (card_isPSL_three_two_one hB) (by norm_num)
        (by norm_num)
  · rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
    · exact out_alt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
    · exact out_hatAlt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
  · rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · exact out_psl2 hY hN hQ ψ hψ σ hσ hp hp3 hB
    · exact out_alt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
  · rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · exact out_sl2 hY hN hQ ψ hψ σ hσ hp hp3 hB
    · exact out_alt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
    · exact out_hatAlt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
  · obtain ⟨p, hp, hp3, hB, -⟩ := h
    exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => out_sl2 hY hN hQ ψ hψ g' hg' hp hp3 hZ
  · obtain ⟨hB, -⟩ := h
    exact out_alt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
  · rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_hatAlt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, -⟩ := h
    · exact out_m22 hY hN hQ ψ hψ hM σ hσ hB
    · exact out_card hY hN hQ ψ hψ σ hσ (card_isPSL_three_two_two hB) (by norm_num)
        (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_four_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_hatAlt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB, -⟩ := h
    exact out_alt hY hN hQ ψ hψ σ hσ (by norm_num) (by norm_num) hB
  · obtain ⟨hB, -⟩ := h
    exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
      out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => out_hatM22 hY hN hQ ψ hψ hM g' hg' hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => out_m24 hY hN hQ ψ hψ hM g' hg' hZ
    · exact out_alt hY hN hQ ψ hψ σ2 hσ2 (by norm_num) (by norm_num) hB
    · exact out_hatAlt hY hN hQ ψ hψ σ2 hσ2 (by norm_num) (by norm_num) hB
    · exact out_card hY hN hQ ψ hψ σ2 hσ2 (card_isPSL_four_two_one hB) (by norm_num)
        (by norm_num)
    · exact out_card hY hN hQ ψ hψ σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num)
        (by norm_num)
  · obtain ⟨hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_alt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
  · obtain ⟨hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_card hY hN hQ ψ hψ g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        out_hatAlt hY hN hQ ψ hψ g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB | hB, -, -⟩ := h
    · exact out_alt hY hN hQ ψ hψ σ2 hσ2 (by norm_num) (by norm_num) hB
    · exact out_card hY hN hQ ψ hψ σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num)
        (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecB
