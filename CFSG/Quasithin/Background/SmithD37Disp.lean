module

public import CFSG.Quasithin.Background.SmithD37ClsL2
public import CFSG.Quasithin.Background.SmithD37ClsSz

public section

namespace CFSG.Quasithin.SmithD37

theorem card_mul_card_fixV_le_of_psl
    {Q : Type} [CommGroup Q]
    [Finite Q] (hQ : ∀ v : Q, v ^ 2 = 1) {G L : Subgroup (MulAut Q)} (hHyp : B4Hyp G L)
    {n : ℕ} (hL : IsPSL 2 2 n ↥L) {B : Subgroup (MulAut Q)} (hBG : B ≤ G)
    (hB : IsElemAbelian2 B) : Nat.card B * Nat.card (fixV B) ≤ Nat.card Q := by
  classical
  obtain ⟨F, _, _, hn, hF, ⟨θL⟩⟩ := exists_sl2_of_isPSL hL
  have hZ : Subgroup.center ↥L = ⊥ :=
    ClsSz.center_eq_bot hHyp.2.2.1 (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hL).2
  have hfix : fixV (⊥ : Subgroup (MulAut Q)) = ⊤ := by
    ext v
    simp only [mem_fixV, Subgroup.mem_bot, forall_eq, Subgroup.mem_top, iff_true]
    rfl
  have hbot : Nat.card (⊥ : Subgroup (MulAut Q)) * Nat.card (fixV (⊥ : Subgroup (MulAut Q))) =
      Nat.card Q := by
    rw [hfix, Subgroup.card_bot, one_mul, Subgroup.card_top]
  obtain ⟨A, ⟨hAG, hA⟩, hmax⟩ := Set.exists_max_image {A | A ≤ G ∧ IsElemAbelian2 A}
    (fun A : Subgroup (MulAut Q) => Nat.card A * Nat.card (fixV A)) (Set.toFinite _)
    ⟨B, hBG, hB⟩
  have hAQ : Nat.card A * Nat.card (fixV A) = Nat.card Q := by
    by_cases hA0 : A = ⊥
    · rw [hA0, hbot]
    · refine B42L2.weight_eq_sl2 hQ hHyp hZ hn hF θL ⟨hAG, hA0, hA, fun C hC => ?_⟩
      exact hmax C ⟨hC.trans hAG, fun a ha b hb => hA.1 a (hC ha) b (hC hb),
        fun a ha => hA.2 a (hC ha)⟩
  exact (hmax B ⟨hBG, hB⟩).trans hAQ.le

theorem cls2F_dispatch
    {Q : Type} [CommGroup Q] [Finite Q] {G L E : Subgroup (MulAut Q)}
    (h : Cls2F G L E) {q d : ℕ} (hq : 2 ≤ q) (hd : 3 ≤ d) (hend : endCard L = q)
    (hcard : Nat.card Q = q ^ d) :
    (d = 3 ∧ q = 2 ∧ IsPSL 2 7 1 ↥L) ∨
    (d = 4 ∧ Nat.card E ≤ q ^ 2 ∧ ∃ n, 2 ≤ n ∧ IsPSL 2 2 n ↥L) ∨
    (d = 4 ∧ Nat.card E ≤ q ∧ Nat.card E ^ 2 * Nat.card (fixV E) ≤ Nat.card Q) := by
  have hinj := Nat.pow_right_injective hq
  rcases h.a38 with ⟨n, hn⟩ | ⟨f, hf⟩ | hJ | ⟨p, hp, hp3, hpL⟩
  · rcases cls2F_psl2_even h hn with ⟨h1, h2⟩ | ⟨s, hs, rfl, h1, h2, h3⟩
    · have hq2 : q = 2 ^ n := hend.symm.trans h1
      have := hinj (show q ^ d = q ^ 2 by rw [← hcard, h2, hq2]; ring)
      omega
    · have hq2 : q = 2 ^ s := hend.symm.trans h1
      refine Or.inr (Or.inl ⟨hinj (show q ^ d = q ^ 4 by rw [← hcard, h2, hq2]; ring), ?_,
        2 * s, ?_, hn⟩)
      · rw [hq2, ← pow_mul, mul_comm]
        exact h3
      · omega
  · obtain ⟨h1, h2, h3, h4⟩ := cls2F_sz h hf
    have hq2 : q = 2 ^ f := hend.symm.trans h1
    exact Or.inr (Or.inr ⟨hinj (show q ^ d = q ^ 4 by rw [← hcard, h2, hq2]; ring),
      hq2 ▸ h3, h4⟩)
  · exact (cls2F_j1 h hJ).elim
  · have hp57 : p = 5 ∨ 7 ≤ p := by
      rcases Nat.lt_or_ge p 7 with h7 | h7
      · left
        interval_cases p <;> first | rfl | norm_num at hp
      · exact Or.inr h7
    rcases hp57 with rfl | hp7
    · rcases cls2F_psl2_five h hpL with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · have hq2 : q = 4 := hend.symm.trans h1
        have := hinj (show q ^ d = q ^ 2 by rw [← hcard, h2, hq2])
        omega
      · have hq2 : q = 2 := hend.symm.trans h1
        refine Or.inr (Or.inl ⟨hinj (show q ^ d = q ^ 4 by rw [← hcard, h2, hq2]),
          ?_, 2, le_rfl, isPSL_two_two_two_of_five hpL⟩)
        rw [hq2]
        exact h3
    · obtain ⟨rfl, h1, h2⟩ := cls2F_psl2_prime h hp hp7 hpL
      have hq2 : q = 2 := hend.symm.trans h1
      exact Or.inl ⟨hinj (show q ^ d = q ^ 3 by rw [← hcard, h2, hq2]), hq2, hpL⟩

end CFSG.Quasithin.SmithD37
