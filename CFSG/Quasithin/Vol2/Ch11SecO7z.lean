module

public import CFSG.Quasithin.Vol2.Ch11SecO7y

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

variable {Y : Type} [Group Y] [Finite Y] {B L : Subgroup Y} {X : Type} [Group X]


theorem a312List11_c13_20 {n : ℕ} (e : ModO2 B ≃* X) (hIn : InLists X n)
    (h : A312C13 B L ∨ A312C14 B L ∨ A312C15 B L ∨ A312C16 B L ∨ A312C17 B L ∨ A312C18 B L ∨
      A312C19 B L ∨ A312C20 B L) : n = 2 ∧ List11Concl L := by
  have : Finite X := Finite.of_equiv _ e.toEquiv
  obtain ⟨hn, hl, -, -⟩ := id hIn
  have hcX : Nat.card X = Nat.card (ModO2 B) := (Nat.card_congr e.toEquiv).symm
  have hsm : ∀ N, Nat.card X ∣ N → 0 < N → N ≤ 1080 → ¬ 660 ∣ N → False :=
    fun N h1 h2 h3 h4 => lists_not_dvd hIn h1 h2 h3 h4
  have hn2 : ∀ N, Nat.card X ∣ N → ¬ 2 ^ 8 ∣ N → n = 2 :=
    fun N h1 h2 => n_eq_two_of_dvd hn hl h1 h2
  have hE : ∀ k, ∀ (V : Type) [Group V], IsE2 k V → IsPGroup 2 V :=
    fun k V _ hv => isPGroup_of_isE2 hv
  have hXs : ∀ m, ∀ (V : Type) [Group V], IsExtraspecial2 m V → IsPGroup 2 V :=
    fun m V _ hv => isPGroup_of_isExtraspecial2 hv
  have hL32 : ∀ (Q : Type) [Group Q], IsPSL 3 2 1 Q → Nat.card Q = 168 :=
    fun Q _ hq => SecA.C10KH.card_of_isPSL_three_two_one hq
  have hA5 : ∀ (Q : Type) [Group Q], IsAlt 5 Q → Nat.card Q = 60 := fun Q _ hq => card_of_isAlt5 hq
  have hH6 : ∀ (Q : Type) [Group Q], IsHat Q (alternatingGroup (Fin 6)) → Nat.card Q = 1080 :=
    fun Q _ hq => card_of_isHatAlt6 hq
  rcases h with h | h | h | h | h | h | h | h
  ·
    refine ⟨?_, Or.inl h.2⟩
    rcases h.1 with ⟨⟨f⟩⟩ | h1 | h1 | h1 | h1 | h1 | h1
    · exact hn2 443520 ((card_dvd_B e).trans (dvd_of_eq ((Nat.card_congr f.toEquiv).trans
        CFSG.Sporadic.Mathieu.card_M22))) (by norm_num)
    · exact hn2 20160 ((card_dvd_B e).trans (dvd_of_eq (card_of_isPSL322 h1))) (by norm_num)
    · exact hn2 2520 (card_dvd_of_isExt e (hE 4) (fun Q _ hq => card_of_isAlt7 hq) h1)
        (by norm_num)
    · exact hn2 168 (card_dvd_of_isExt e (hE 4) hL32 h1) (by norm_num)
    · exact hn2 168 (card_dvd_of_isExt e (hE 3) hL32 h1) (by norm_num)
    · exact hn2 360 (card_dvd_of_isExt e (hE 4) (fun Q _ hq => card_of_isAlt6 hq) h1)
        (by norm_num)
    · exact hn2 60 (card_dvd_of_isExt e (hE 4) hA5 h1) (by norm_num)
  ·
    exfalso
    rcases h.1 with ⟨V, hVn, hV, h42⟩ | h1 | h1 | h1
    · have : IsSimpleGroup (↥B ⧸ V) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h42).2
      have hQ : CFSG.pCore 2 (↥B ⧸ V) = ⊥ := pCore_eq_bot_of_simple Nat.prime_three (by norm_num)
        (by rw [card_of_isPSL421 h42]; norm_num)
      exact not_l42 hIn (CFSG.Quasithin.isPSL_of_mulEquiv1515e
        (e.symm.trans (modO2EquivQuot (isPGroup_of_isE2 hV) hQ)) h42)
    · exact hsm 168 (card_dvd_of_isExt e (hE 6) hL32 h1) (by norm_num) (by norm_num) (by norm_num)
    · exact hsm 168 (card_dvd_of_isExt e (hXs 3) hL32 h1) (by norm_num) (by norm_num)
        (by norm_num)
    · exact hsm 1080 (card_dvd_of_isExt e (hE 6) hH6 h1) (by norm_num) (by norm_num) (by norm_num)
  ·
    exact (hsm 60 ((card_dvd_B e).trans (dvd_of_eq (card_of_isAlt5 h.1))) (by norm_num)
      (by norm_num) (by norm_num)).elim
  ·
    exact (hsm 60 (card_dvd_of_isExt e (hXs 2) hA5 h.1) (by norm_num) (by norm_num)
      (by norm_num)).elim
  ·
    obtain ⟨hJ, h17⟩ := h
    refine ⟨?_, Or.inr (Or.inl hJ)⟩
    rcases h17 with h1 | ⟨V, hVn, hV, ⟨fM⟩⟩ | h1 | h1 | h1 | h1
    · exact hn2 1330560 (card_dvd_of_isExt e (hXs 6) (fun Q _ hq => by
        rw [SecA.C10KH.card_of_isHat hq, show Nat.card (NativeSporadic.Carrier .M22) = 443520
          from CFSG.Sporadic.Mathieu.card_M22]) h1) (by norm_num)
    · have : IsSimpleGroup (NativeSporadic.Carrier .M24) :=
        CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      have : IsSimpleGroup (↥B ⧸ V) := fM.isSimpleGroup
      have hcM : Nat.card (↥B ⧸ V) = 244823040 :=
        (Nat.card_congr fM.toEquiv).trans CFSG.Sporadic.Mathieu.card_M24
      have hQ : CFSG.pCore 2 (↥B ⧸ V) = ⊥ := pCore_eq_bot_of_simple Nat.prime_three (by norm_num)
        (by rw [hcM]; norm_num)
      have hXc : Nat.card X = 244823040 := by
        rw [hcX, Nat.card_congr (modO2EquivQuot (isPGroup_of_isE2 hV) hQ).toEquiv, hcM]
      rcases hl with h2 | ⟨hn2', -⟩
      · exfalso
        have := list2_two_adic hn h2 (A' := 10) (u' := 239085) ⟨119542, rfl⟩
          (hXc.trans (by norm_num))
        omega
      · exact hn2'
    · exact hn2 60 (dvd_of_eq (hcX.trans (card_of_isAlt5 h1))) (by norm_num)
    · exact hn2 1080 (dvd_of_eq (hcX.trans (card_of_isHatAlt6 h1))) (by norm_num)
    · exact hn2 20160 (dvd_of_eq (hcX.trans (card_of_isPSL421 h1))) (by norm_num)
    · exact hn2 168 (dvd_of_eq (hcX.trans (hL32 _ h1))) (by norm_num)
  ·
    exfalso
    rcases h.1 with h1 | h1
    · exact hsm 60 (card_dvd_of_isExt e (fun V _ hv => isPGroup_of_isZ4StarExtra2 hv) hA5 h1)
        (by norm_num) (by norm_num) (by norm_num)
    · exact hsm 168 (card_dvd_of_isExt e (fun V _ hv => isPGroup_of_isZ4Cubed hv) hL32 h1)
        (by norm_num) (by norm_num) (by norm_num)
  ·
    exfalso
    rcases h.1 with h1 | h1
    · exact hsm 168 (card_dvd_of_isExt e (hXs 3) hL32 h1) (by norm_num) (by norm_num)
        (by norm_num)
    · exact hsm 1080 (card_dvd_of_isExt e (hE 6) hH6 h1) (by norm_num) (by norm_num) (by norm_num)
  ·
    exfalso
    rcases h.1 with h1 | h1
    · exact hsm 60 (dvd_of_eq (hcX.trans (card_of_isAlt5 h1))) (by norm_num) (by norm_num)
        (by norm_num)
    · exact hsm 168 (dvd_of_eq (hcX.trans (hL32 _ h1))) (by norm_num) (by norm_num) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
