module

public import CFSG.Quasithin.Vol2.Ch11SecO7z

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

variable {Y : Type} [Group Y] [Finite Y] {B L : Subgroup Y} {X : Type} [Group X]


theorem a312List11_case {n : ℕ} (e : ModO2 B ≃* X) (hIn : InLists X n) (h : A312Case B L) :
    n = 2 ∧ List11Concl L := by
  have : Finite X := Finite.of_equiv _ e.toEquiv
  obtain ⟨hXq, hXZ⟩ := lists_qs hIn
  have hcX : Nat.card X = Nat.card (ModO2 B) := (Nat.card_congr e.toEquiv).symm
  have hsm : ∀ N, Nat.card X ∣ N → 0 < N → N ≤ 1080 → ¬ 660 ∣ N → False :=
    fun N h1 h2 h3 h4 => lists_not_dvd hIn h1 h2 h3 h4
  have hB : ∀ N, Nat.card ↥B = N → 0 < N → N ≤ 1080 → ¬ 660 ∣ N → False :=
    fun N hN => hsm N (hN ▸ card_dvd_B e)
  have hE4 : ∀ (V : Type) [Group V], IsE2 4 V → IsPGroup 2 V := fun V _ hv => isPGroup_of_isE2 hv
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨m, hm⟩, -⟩ := h
    exact (not_l2two hIn m (hcX.trans (SecA.C10KH.card_of_isPSL_two_two hm).2)).elim
  ·
    exfalso
    obtain ⟨f, hf, -⟩ := h
    obtain ⟨a', -, hfa, hcard⟩ := H13.card_of_suzukiModel hf
    apply SecA.C10KH.not_three_dvd_suzuki a'
    rw [← hfa, ← hcard, ← hcX]
    exact lists_three_dvd hIn
  ·
    exact (hsm 168 (by rw [hcX, SecA.C10KH.card_of_isPSL_three_two_one h.1]) (by norm_num)
      (by norm_num) (by norm_num)).elim
  ·
    exact (not_l42 hIn (CFSG.Quasithin.isPSL_of_mulEquiv1515e e.symm h.1)).elim
  ·
    exfalso
    rcases h.1 with h1 | h1
    · exact hB 60 (card_of_isAlt5 h1) (by norm_num) (by norm_num) (by norm_num)
    · exact hB 168 (SecA.C10KH.card_of_isPSL_three_two_one h1) (by norm_num) (by norm_num)
        (by norm_num)
  ·
    exfalso
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hB 360 (card_of_isAlt6 h1) (by norm_num) (by norm_num) (by norm_num)
    · exact hB 1080 (card_of_isHatAlt6 h1) (by norm_num) (by norm_num) (by norm_num)
  ·
    rcases h with ⟨r, hr, hr3, hBr, hL⟩ | ⟨h1, -⟩
    · have hr5 := five_le_of_prime hr hr3
      have : IsSimpleGroup ↥B := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 r 1 hBr).2
      have hXc := card_modO2_of_simple e hr (by omega) (prime_dvd_card_psl2 hr (by omega) hBr)
      obtain ⟨h2, h11⟩ := psl2_case hIn hr hr5
        (by rw [hXc]; exact card_mul_two_of_psl2 hr (by omega) hBr)
      exact ⟨h2, Or.inr (Or.inr ⟨r, hr, h11, Or.inl hL⟩)⟩
    · exact (hB 60 (card_of_isAlt5 h1) (by norm_num) (by norm_num) (by norm_num)).elim
  · exact a312List11_c9 e hIn hXq hXZ h
  · exact (a312List11_c10 e hXq hXZ h).elim
  ·
    exact (hB 360 (card_of_isAlt6 h.1) (by norm_num) (by norm_num) (by norm_num)).elim
  ·
    exfalso
    rcases h with ⟨h1 | h1, -⟩ | ⟨h1 | h1, -⟩
    · exact hsm 60 (card_dvd_of_isExt e hE4 (fun Q _ hq => card_of_isAlt5 hq) h1) (by norm_num)
        (by norm_num) (by norm_num)
    · exact hsm 360 (card_dvd_of_isExt e hE4 (fun Q _ hq => card_of_isAlt6 hq) h1) (by norm_num)
        (by norm_num) (by norm_num)
    · exact hsm 60 (card_dvd_of_isExt e hE4 (fun Q _ hq => card_of_isAlt5 hq) h1) (by norm_num)
        (by norm_num) (by norm_num)
    · exact hsm 1080 (card_dvd_of_isExt e hE4 (fun Q _ hq => card_of_isHatAlt6 hq) h1)
        (by norm_num) (by norm_num) (by norm_num)
  · exact a312List11_c13_20 e hIn h

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
