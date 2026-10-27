module

public import CFSG.Quasithin.Vol2.Ch11SecO7m
public import CFSG.Quasithin.EmptyFaithful.T1515M11
public import CFSG.Quasithin.Vol2.Ch11SecEFacts6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint


theorem a312A5Fact_holds : A312A5Fact := by
  intro Y _ _ B L F _ _ hF hφ h p hp hp7
  obtain ⟨φ, hφs, hk⟩ := hφ
  suffices hT : ¬ C10KH.InT p ↥L from
    ⟨fun h' => hT (Or.inl h'), fun h' => hT (Or.inr (Or.inl h')),
      fun h' => hT (Or.inr (Or.inr (Or.inl h'))),
      fun h' => hT (Or.inr (Or.inr (Or.inr (Or.inl h')))),
      fun h' => hT (Or.inr (Or.inr (Or.inr (Or.inr h'))))⟩
  obtain ⟨a, hBa⟩ := C10KH.card_of_sl2_four hF hφs hk
  obtain ⟨c, hMc⟩ := C10KH.card_modO2_of hBa
  have hfix := fun N => C10KH.not_T_fix (L := ↥L) hp hp7 N
  have hBd : ∀ d, Odd d → ¬ d ∣ 15 → ¬ d ∣ Nat.card ↥B := fun d hd h15 hdB =>
    h15 (C10KH.dvd_fifteen hd (hBa ▸ hdB))
  have hMd : ∀ d, Odd d → ¬ d ∣ 15 → ¬ d ∣ Nat.card (ModO2 B) := fun d hd h15 hdB =>
    h15 (C10KH.dvd_fifteen hd (hMc ▸ hdB))
  have h7 : ∀ (Q : Type) [Group Q], IsPSL 3 2 1 Q → 7 ∣ Nat.card Q := fun Q _ hq => by
    rw [SecA.C10KH.card_of_isPSL_three_two_one hq]; norm_num
  have h27 : ∀ (Q : Type) [Group Q], IsHat Q (alternatingGroup (Fin 6)) → 27 ∣ Nat.card Q :=
    fun Q _ hq => by rw [C10KH.card_of_isHatAlt6 hq]; norm_num
  rcases h with rfl | h | h
  ·
    intro hT
    refine C10KH.not_T_of_card hBa (fun q hq hq7 hq2 => ?_) p hp hp7 hT
    exfalso
    have h1 := Nat.le_of_dvd (by norm_num)
      (C10KH.dvd_fifteen ((hq.odd_of_ne_two (by omega)).pow) hq2)
    nlinarith
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact C10KH.a312A5_c2 hp hp7 hMc h
    ·
      obtain ⟨f, hf, -⟩ := h
      obtain ⟨a', -, hfa, hcard⟩ := H13.card_of_suzukiModel hf
      exfalso
      apply SecA.C10KH.not_three_dvd_suzuki a'
      rw [← hfa, ← hcard, hMc]
      exact Dvd.dvd.mul_left (by norm_num) _
    · exact absurd (h7 _ h.1) (hMd 7 ⟨3, rfl⟩ (by norm_num))
    · exact absurd (by rw [C10KH.card_of_isPSL421 h.1]; norm_num) (hMd 7 ⟨3, rfl⟩ (by norm_num))
    · rcases h.2 with hL | hL
      · exact hfix 2520 (C10KH.card_of_isAlt7 hL) (by norm_num)
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
      · exact hfix 7560 (C10KH.card_of_isHatAlt7 hL) (by norm_num)
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
    · rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
      · exact hfix 2520 (C10KH.card_of_isAlt7 hL) (by norm_num)
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
      · exact hfix 7560 (C10KH.card_of_isHatAlt7 hL) (by norm_num)
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
    ·
      rcases h with ⟨r, hr, hr3, hB, hL⟩ | ⟨-, r, hr, hL, -, h8⟩
      · rcases C10KH.eq_three_or_five hr (by omega)
          (hBa ▸ C10KH.prime_dvd_card_psl2 hr (by omega) hB) with rfl | rfl
        · omega
        · exact hfix 7800 (by rw [H13.NotLie.card_psl2 hL]; norm_num) (by norm_num)
            (by simp only [Nat.primeFactorsList_ofNat]; decide)
      · exact C10KH.not_T_of_psl2 hr (by omega) hL p hp hp7
    · exact C10KH.a312A5_c9 hp hp7 hBa h
    ·
      obtain ⟨r, hr, hr3, ⟨V, hVn, ⟨e⟩, -⟩, -⟩ := h
      have hV : Nat.card ↥V = r ^ 2 := by
        rw [Nat.card_congr e.toEquiv]
        show Nat.card (Fin 2 → ZMod r) = r ^ 2
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      have hrB : r ^ 2 ∣ Nat.card ↥B := hV ▸ Subgroup.card_subgroup_dvd_card V
      rcases C10KH.eq_three_or_five hr (by omega)
        (hBa ▸ (dvd_pow_self r two_ne_zero).trans hrB) with rfl | rfl
      · omega
      · exact (hBd 25 ⟨12, rfl⟩ (by norm_num) (by norm_num at hrB; exact hrB)).elim
    · exact absurd (by rw [C10KH.card_of_isAlt6 h.1]; norm_num) (hBd 9 ⟨4, rfl⟩ (by norm_num))
    ·
      rcases h with ⟨-, ⟨e⟩⟩ | ⟨-, hL⟩
      · exact hfix 443520 ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22)
          (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
      · exact hfix 1330560 (by rw [SecA.C10KH.card_of_isHat hL, show Nat.card
          (NativeSporadic.Carrier .M22) = 443520 from CFSG.Sporadic.Mathieu.card_M22])
          (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
    · obtain ⟨-, ⟨e⟩⟩ := h
      exact hfix 10200960 ((Nat.card_congr e.toEquiv).trans card_nativeM23_1522) (by norm_num)
        (by simp only [Nat.primeFactorsList_ofNat]; decide)
    ·
      exfalso
      rcases h.1 with h1 | h1 | h1 | h1
      · exact C10KH.not_isExt_of_odd_dvd hBa ⟨3, rfl⟩ (by norm_num)
          (fun Q _ hq => by rw [C10KH.card_of_isPSL421 hq]; norm_num) h1
      · exact C10KH.not_isExt_of_odd_dvd hBa ⟨3, rfl⟩ (by norm_num) h7 h1
      · exact C10KH.not_isExt_of_odd_dvd hBa ⟨3, rfl⟩ (by norm_num) h7 h1
      · exact C10KH.not_isExt_of_odd_dvd hBa ⟨13, rfl⟩ (by norm_num) h27 h1
    · obtain ⟨-, ⟨e⟩⟩ := h
      exact hfix 175560 ((Nat.card_congr (e.trans CFSG.Sporadic.J1.nativeEquiv).toEquiv).trans
        CFSG.Sporadic.J1.card_J) (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
    · obtain ⟨-, ⟨e⟩⟩ := h
      exact hfix 604800 ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2) (by norm_num)
        (by simp only [Nat.primeFactorsList_ofNat]; decide)
    · obtain ⟨⟨e⟩, -⟩ := h
      exact hfix 86775571046077562880 ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4)
        (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)
    · obtain ⟨-, ⟨e⟩⟩ := h
      exact hfix 44352000 ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS)
        (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
    ·
      exfalso
      rcases h.1 with h1 | h1
      · exact C10KH.not_isExt_of_odd_dvd hBa ⟨3, rfl⟩ (by norm_num) h7 h1
      · exact C10KH.not_isExt_of_odd_dvd hBa ⟨13, rfl⟩ (by norm_num) h27 h1
    · obtain ⟨-, -, ⟨e⟩⟩ := h
      exact hfix 145926144000 ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru)
        (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
  · intro hT
    exact C10KH.not_nonquasi_of_T hp hp7 hT h

end CFSG.Quasithin.Vol2.Ch11.SecE
