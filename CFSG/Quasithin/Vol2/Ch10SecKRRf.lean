module

public import CFSG.Quasithin.Vol2.Ch10SecKRRe
public import CFSG.RankThree.ThinCatalog.FiveModels

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem five_dvd_card_of_isAlt {n : ℕ} {Y : Type} [Group Y] (hn : 5 ≤ n) (h : IsAlt n Y) :
    5 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_fin] at h1
  have h5 : 5 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [← h1] at h5
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5)

theorem card_of_isAlt5 {Y : Type} [Group Y] (h : IsAlt 5 Y) : Nat.card Y = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm, Nat.card_fin] at h1
  have : (5 : ℕ).factorial = 120 := rfl
  omega

theorem pCore_eq_bot_of_isAlt5 {Y : Type} [Group Y] [Finite Y] (h : IsAlt 5 Y) :
    CFSG.pCore 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h
  have : IsSimpleGroup Y := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 Y) with hb | ht
  · exact hb
  · exfalso
    have h2 : IsPGroup 2 (⊤ : Subgroup Y) := ht ▸ CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    rw [Subgroup.card_top, card_of_isAlt5 ⟨e⟩] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)

theorem card_sl3_zmod_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem not_typeI_of_isAlt5 {X : Type} [Group X] [Finite X]
    {B : Subgroup X} (hB : IsAlt 5 ↥B)
    (hI : (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (ModO2 B) 2 n) ∨
      Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) : False := by
  have h3 : 3 ∣ Nat.card (ModO2 B) :=
    dvd_card_modO2 Nat.prime_three (by norm_num) (three_dvd_card_of_isAlt (by norm_num) hB)
  rcases hI with ⟨n, hSz⟩ | ⟨⟨e⟩⟩
  · exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hSz h3
  · have h1 := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥B)
    rw [show Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 168 by
        rw [Nat.card_congr e.toEquiv, card_sl3_zmod_two],
      card_of_isAlt5 hB] at h1
    norm_num at h1

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h5
  · exact absurd (h4 ▸ hp) (by decide)
  · exact h5

theorem rankWit_C6 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C6 B L) :
    RankWit B L := by
  obtain ⟨hB, hL⟩ := h
  have h3 : 3 ∣ Nat.card B := by
    rcases hB with hB | hB
    · exact three_dvd_card_of_isAlt (by norm_num) hB
    · rw [card_of_isPSL_three_two hB]; norm_num
  refine rankWit_of Nat.prime_three (by norm_num) h3 ?_
  rcases hL with hL | hL
  · exact two_le_pRank_three_of_isAlt7 hL
  · exact two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
      (two_le_pRank_three_of_isHat hL
        (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_of_alternating (by norm_num)
          (MulEquiv.refl _)))

theorem rankWit_C7 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C7 B L) :
    RankWit B L := by
  rcases h with ⟨hB, hL⟩ | ⟨hB, hL⟩
  · exact rankWit_of Nat.prime_three (by norm_num) (three_dvd_card_of_isAlt (by norm_num) hB)
      (two_le_pRank_three_of_isAlt7 hL)
  · exact rankWit_of Nat.prime_three (by norm_num) (three_dvd_card_of_isHat hB)
      (two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
        (two_le_pRank_three_of_isHat hL
          (CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_of_alternating (by norm_num)
            (MulEquiv.refl _))))

theorem rankGoal_C8 {X : Type} [Group X] [Finite X]
    {B L : Subgroup X} (h : A312C8 B L) : RankGoal B L := by
  rcases h with ⟨p, hp, hp3, hB, hL⟩ | h8
  · exact (rankWit_of hp (by omega) (prime_dvd_card_of_isPSL_two hp (by omega) hB)
      (two_le_pRank_of_isPSL_two_sq (by omega) hL)).goal
  · have hB := h8.1
    exact ⟨fun hI => (not_typeI_of_isAlt5 hB hI).elim,
      fun _ => Or.inr ⟨pCore_eq_bot_of_isAlt5 hB, Or.inl (Or.inr h8)⟩⟩

theorem five_dvd_card_of_isHat_alt6 {Y : Type} [Group Y] [Finite Y]
    (h : IsHat Y (alternatingGroup (Fin 6))) : 5 ∣ Nat.card Y := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  rw [(Subgroup.center Y).card_eq_card_quotient_mul_card_subgroup]
  exact Dvd.dvd.mul_right (five_dvd_card_of_isAlt (by norm_num) ⟨e⟩) _

theorem rankWit_C9 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C9 B L) :
    RankWit B L := by
  rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, hL⟩ | ⟨hB, hL⟩
  · refine rankWit_of hp (by omega) (prime_dvd_card_of_isSL2 hp hB) ?_
    rcases hL with hL | hL
    · exact two_le_pRank_of_isPSLEps3 (by omega) s hL
    · exact two_le_pRank_of_isSLEps3 hp (five_le_of_prime hp hp3) s hL
  · exact rankWit_of (by norm_num) (by norm_num) (five_dvd_card_of_isAlt (by norm_num) hB)
      (two_le_pRank_of_isPSLEps3 (by norm_num) false hL)
  · exact rankWit_of (by norm_num) (by norm_num) (five_dvd_card_of_isHat_alt6 hB)
      (two_le_pRank_of_isSLEps3 (by norm_num) le_rfl false hL)

theorem rankWit_C10 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C10 B L) :
    RankWit B L := by
  obtain ⟨p, hp, hp3, hB, hL⟩ := h
  refine rankWit_of hp (by omega)
    (dvd_card_of_isExt hB fun Y _ hY => prime_dvd_card_of_isSL2 hp hY) ?_
  rcases hL with hL | hL
  · exact two_le_pRank_of_isPSLEps3 (by omega) true hL
  · exact two_le_pRank_of_isSLEps3 hp (five_le_of_prime hp hp3) true hL

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR
