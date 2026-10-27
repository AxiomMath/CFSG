module

public import CFSG.Quasithin.Vol2.Ch10SecKRRf

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (two_le_pRank_three_M11 two_le_pRank_three_M24
  two_le_pRank_three_J2 two_le_pRank_three_J4 two_le_pRank_three_HS two_le_pRank_three_He
  two_le_pRank_three_Ru)
open CFSG.RankThree.ThinCatalog (two_le_pRank_three_M22_sylow two_le_pRank_three_M23_sylow)

theorem three_dvd_of_isPSL_three_two {Y : Type} [Group Y] (h : IsPSL 3 2 1 Y) :
    3 ∣ Nat.card Y := by
  rw [card_of_isPSL_three_two h]
  norm_num

theorem three_dvd_of_isPSL_four_two {Y : Type} [Group Y] (h : IsPSL 4 2 1 Y) :
    3 ∣ Nat.card Y := by
  rw [card_of_isPSL_four_two h]
  norm_num

theorem three_dvd_of_isSporadic_M22
    {Y : Type} [Group Y] (h : IsSporadic .M22 Y) : 3 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    inferInstanceAs (Finite ↥CFSG.Blueprint.NativeSporadic.M22)
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact dvd_card_of_two_le_pRank Nat.prime_three (two_le_pRank_three_M22_sylow e)

theorem three_dvd_of_isSporadic_M24 {Y : Type} [Group Y]
    (h : IsSporadic .M24 Y) : 3 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    inferInstanceAs (Finite ↥CFSG.Blueprint.NativeSporadic.M24)
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact dvd_card_of_two_le_pRank Nat.prime_three (two_le_pRank_three_M24 e)

theorem rankWit_C11 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C11 B L) :
    RankWit B L := by
  obtain ⟨hB, ⟨e⟩⟩ := h
  exact rankWit_of Nat.prime_three (by norm_num) (three_dvd_card_of_isAlt (by norm_num) hB)
    (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_M11 e))

theorem rankWit_C12 {X : Type}
    [Group X] [Finite X] {B L : Subgroup X} (h : A312C12 B L) : RankWit B L := by
  rcases h with ⟨hB, ⟨e⟩⟩ | ⟨hB, hL⟩
  · have h3 : 3 ∣ Nat.card B := by
      rcases hB with hB | hB
      · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
      · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
    exact rankWit_of Nat.prime_three (by norm_num) h3
      (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
        (two_le_pRank_three_M22_sylow e))
  · have h3 : 3 ∣ Nat.card B := by
      rcases hB with hB | hB
      · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
      · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isHat hY
    have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      inferInstanceAs (Finite ↥CFSG.Blueprint.NativeSporadic.M22)
    exact rankWit_of Nat.prime_three (by norm_num) h3
      (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
        (two_le_pRank_three_of_isHat hL (two_le_pRank_three_M22_sylow (MulEquiv.refl _))))

theorem rankWit_C13
    {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C13 B L) : RankWit B L := by
  obtain ⟨hB, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card B := by
    rcases hB with hB | hB | hB | hB | hB | hB | hB
    · exact three_dvd_of_isSporadic_M22 hB
    · rw [card_of_isPSL_three_four hB]; norm_num
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_three_two hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_three_two hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
  exact rankWit_of Nat.prime_three (by norm_num) h3
    (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
      (two_le_pRank_three_M23_sylow e))

theorem rankWit_C14 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C14 B L) : RankWit B L := by
  obtain ⟨hB, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card B := by
    rcases hB with hB | hB | hB | hB
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_four_two hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_three_two hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_three_two hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isHat hY
  exact rankWit_of Nat.prime_three (by norm_num) h3
    (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_M24 e))

theorem rankGoal_C15 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C15 B L) : RankGoal B L :=
  ⟨fun hI => (not_typeI_of_isAlt5 h.1 hI).elim,
    fun _ => Or.inr ⟨pCore_eq_bot_of_isAlt5 h.1, Or.inr h⟩⟩

theorem rankWit_C16 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C16 B L) : RankWit B L := by
  obtain ⟨hB, ⟨e⟩⟩ := h
  exact rankWit_of Nat.prime_three (by norm_num)
    (dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY)
    (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_J2 e))

theorem rankWit_C17 {X : Type}
    [Group X] [Finite X] {B L : Subgroup X} (h : A312C17 B L) : RankWit B L := by
  obtain ⟨⟨e⟩, hB⟩ := h
  have hL : 2 ≤ CFSG.Open.pRank 3 L :=
    two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_J4 e)
  rcases hB with hB | hB | hB | hB | hB | hB
  · exact rankWit_of Nat.prime_three (by norm_num)
      (dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isHat hY) hL
  · exact rankWit_of Nat.prime_three (by norm_num)
      (dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isSporadic_M24 hY) hL
  · exact ⟨3, Nat.prime_three, by norm_num, three_dvd_card_of_isAlt (by norm_num) hB, hL⟩
  · exact ⟨3, Nat.prime_three, by norm_num, three_dvd_card_of_isHat hB, hL⟩
  · exact ⟨3, Nat.prime_three, by norm_num, three_dvd_of_isPSL_four_two hB, hL⟩
  · exact ⟨3, Nat.prime_three, by norm_num, three_dvd_of_isPSL_three_two hB, hL⟩

theorem rankWit_C18 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C18 B L) : RankWit B L := by
  obtain ⟨hB, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card B := by
    rcases hB with hB | hB
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isAlt (by norm_num) hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_three_two hY
  exact rankWit_of Nat.prime_three (by norm_num) h3
    (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_HS e))

theorem rankWit_C19 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C19 B L) : RankWit B L := by
  obtain ⟨hB, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card B := by
    rcases hB with hB | hB
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_of_isPSL_three_two hY
    · exact dvd_card_of_isExt hB fun Y _ hY => three_dvd_card_of_isHat hY
  exact rankWit_of Nat.prime_three (by norm_num) h3
    (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_He e))

theorem rankWit_C20 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C20 B L) : RankWit B L := by
  obtain ⟨hB, -, ⟨e⟩⟩ := h
  have hL : 2 ≤ CFSG.Open.pRank 3 L :=
    two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _) (two_le_pRank_three_Ru e)
  rcases hB with hB | hB
  · exact ⟨3, Nat.prime_three, by norm_num, three_dvd_card_of_isAlt (by norm_num) hB, hL⟩
  · exact ⟨3, Nat.prime_three, by norm_num, three_dvd_of_isPSL_three_two hB, hL⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR
