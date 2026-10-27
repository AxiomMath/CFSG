module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem card_alternatingGroup_six_cov : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
    rw [two_mul_card_alternatingGroup_kz3 6 (by norm_num)]
    rfl
  omega

theorem card_modO2_form_cov {G : Type} [Group G] [Finite G] {Gz Lz : Subgroup G}
    (hLzG : Lz ≤ Gz)
    (hLzq : IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6))) :
    (∃ a : ℕ, Nat.card ↥(modO2Image Gz Lz) = 2 ^ a * 1080) ∧
    Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 1080 := by
  obtain ⟨e⟩ := modO2_quot_iso_kz3 (G := G) hLzG
  have hM : Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) =
      Nat.card (↥Lz ⧸ CFSG.pCore 2 ↥Lz) := (Nat.card_congr e.toEquiv).symm
  have hM' : Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 1080 := by
    rw [hM]
    exact CFSG.Quasithin.SmithC27.card_of_isHat_alt6 hLzq
  refine ⟨?_, hM'⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.card ↥(CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 2 ^ j :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image Gz Lz))).exists_card_eq
  have hsplit : Nat.card ↥(modO2Image Gz Lz) =
      Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) *
        Nat.card ↥(CFSG.pCore 2 ↥(modO2Image Gz Lz)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  refine ⟨j, ?_⟩
  rw [hsplit, hj, hM']
  ring

theorem cov_list_match {G : Type} [Group G] [Finite G] (hloc : LocalSQTK G)
    (h312 : A312ForSQTKCat)
    {Gz T Lz K : Subgroup G} (hT : IsSylowTwoOf T Gz) (hpC : pCoreOf 2 Gz ≠ ⊥)
    (hLzG : Lz ≤ Gz) (hLzF : Lz ∈ lFamily T)
    (hLzq : IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)))
    (hK : K ∈ cComp Gz) (hLK : Lz ≤ K)
    (hne : modO2Image Gz Lz ≠ modO2Image Gz K)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hM23 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960) :
    IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7)) ∨
    IsSU3 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
    IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) ∨
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) ∨
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) := by
  obtain ⟨hQs, hMQs⟩ := card_modO2_form_cov hLzG hLzq
  have hQform : ∃ a : ℕ, Nat.card ↥(modO2Image Gz Lz) = 2 ^ a * 360 ∨
      Nat.card ↥(modO2Image Gz Lz) = 2 ^ a * 1080 := by
    obtain ⟨a, ha⟩ := hQs
    exact ⟨a, Or.inr ha⟩
  have hMQ : Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 360 ∨
      Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 1080 :=
    Or.inr hMQs
  have eK := (modO2_mulEquiv hK).some
  have hQR : modO2Image Gz Lz ≤ modO2Image Gz K := Subgroup.map_mono (fun x hx => hLK hx)
  have hdvdQR : Nat.card ↥(modO2Image Gz Lz) ∣ Nat.card ↥(modO2Image Gz K) :=
    Subgroup.card_dvd_of_le hQR
  rcases CFSG.QuasithinUnique.Vol2Native.lemma_1_2_4_list hloc h312 hpC hT hLzG hLzF hK hLK
    with hEq | hcase | hnq
  · exact absurd hEq hne
  ·
    unfold A312Case at hcase
    set Q := modO2Image Gz Lz with hQdef
    set R := modO2Image Gz K with hRdef
    rcases hcase with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 |
      h16 | h17 | h18 | h19 | h20
    ·
      unfold A312C2 at h2
      obtain ⟨⟨m, hm⟩, -, -⟩ := h2
      have hc : Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) = 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hm
      rw [hc] at hMQ
      exact (psl_two_two_ne_kz3 m hMQ).elim
    ·
      unfold A312C3 at h3
      obtain ⟨f, hf, -, -⟩ := h3
      have h29 : 29120 ≤ Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) := card_ge_of_isSz_kz3 hf
      exact (by omega : False).elim
    ·
      unfold A312C4 at h4
      obtain ⟨h1, -, -⟩ := h4
      have hc : Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) = 168 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h1
      exact (by omega : False).elim
    ·
      unfold A312C5 at h5
      obtain ⟨h1, -, -⟩ := h5
      have hc : Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) = 20160 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h1
      exact (by omega : False).elim
    ·
      unfold A312C6 at h6
      obtain ⟨h1, -⟩ := h6
      obtain ⟨a, ha⟩ := hQform
      rcases h1 with h1 | h1
      · have hc : Nat.card ↥Q = 60 := by
          rw [card_isAlt_kz3 h1, card_alternatingGroup_five_kz3]
        exact (by omega : False).elim
      · have hc : Nat.card ↥Q = 168 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h1
        exact (by omega : False).elim
    ·
      unfold A312C7 at h7
      rcases h7 with ⟨h6, -⟩ | ⟨-, h7'⟩
      · obtain ⟨a, ha⟩ := hQs
        have hc : Nat.card ↥Q = 360 := by
          rw [card_isAlt_kz3 h6, card_alternatingGroup_six_cov]
        exact (by omega : False).elim
      · exact Or.inl (IsHat.of_mulEquiv eK.symm h7')
    ·
      unfold A312C8 at h8
      rcases h8 with ⟨p, hp, hp3, hPQ, -⟩ | ⟨h1, -⟩
      · have h2p := CFSG.Open.StatedAPI.two_mul_card_of_statedClassicalModel_psl_two_prime hp
          (by omega : p ≠ 2) hPQ
        have hdvd : p ∣ 2 * Nat.card ↥Q := by
          rw [h2p]
          exact Dvd.intro _ rfl
        obtain ⟨a, ha⟩ := hQform
        have hform : ∃ b : ℕ, 2 * Nat.card ↥Q = 2 ^ b * 360 ∨ 2 * Nat.card ↥Q = 2 ^ b * 1080 := by
          refine ⟨a + 1, ?_⟩
          rcases ha with ha | ha
          · left
            rw [ha, pow_succ]
            ring
          · right
            rw [ha, pow_succ]
            ring
        rcases dvd_prime_of_card_form_kz3 hform hp hdvd with h | h | h
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · subst h
          norm_num at h2p
          exact (by omega : False).elim
      · have hc : Nat.card ↥Q = 60 := by
          rw [card_isAlt_kz3 h1, card_alternatingGroup_five_kz3]
        obtain ⟨a, ha⟩ := hQform
        exact (by omega : False).elim
    ·
      unfold A312C9 at h9
      rcases h9 with ⟨s, p, hp, hp3, hSL2, -⟩ | ⟨h6, -⟩ | ⟨-, h2'⟩
      · have hc : Nat.card ↥Q = p * (p ^ 2 - 1) :=
          CFSG.Quasithin.Ch1Four.card_of_isSL2' hp hSL2
        have hdvd : p ∣ Nat.card ↥Q := ⟨p ^ 2 - 1, hc⟩
        obtain ⟨a, ha⟩ := hQform
        rcases dvd_prime_of_card_form_kz3 ⟨a, ha⟩ hp hdvd with h | h | h
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · subst h
          norm_num at hc
          exact (by omega : False).elim
      · obtain ⟨a, ha⟩ := hQs
        have hc : Nat.card ↥Q = 360 := by
          rw [card_isAlt_kz3 h6, card_alternatingGroup_six_cov]
        exact (by omega : False).elim
      · exact Or.inr (Or.inl (IsSU3.of_mulEquiv eK.symm h2'))
    ·
      unfold A312C10 at h10
      obtain ⟨p, hp, hp3, hext, -⟩ := h10
      obtain ⟨V, hVn, hV, hY⟩ := hext
      have hcV : Nat.card V = p ^ 2 := card_isElemAbelianOfRank_kz3 hp hV
      have hcY : Nat.card (↥Q ⧸ V) = p * (p ^ 2 - 1) :=
        CFSG.Quasithin.Ch1Four.card_of_isSL2' hp hY
      have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup V
      have hdvd : p ∣ Nat.card ↥Q := ⟨(p ^ 2 - 1) * p ^ 2, by rw [hcQ, hcY, hcV]; ring⟩
      obtain ⟨a, ha⟩ := hQform
      rcases dvd_prime_of_card_form_kz3 ⟨a, ha⟩ hp hdvd with h | h | h
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · subst h
        have h3000 : Nat.card ↥Q = 3000 := by
          rw [hcQ, hcY, hcV]
          norm_num
        exact (by omega : False).elim
    ·
      unfold A312C11 at h11
      obtain ⟨h6, -⟩ := h11
      obtain ⟨a, ha⟩ := hQs
      have hc : Nat.card ↥Q = 360 := by
        rw [card_isAlt_kz3 h6, card_alternatingGroup_six_cov]
      exact (by omega : False).elim
    ·
      unfold A312C12 at h12
      rcases h12 with ⟨hext, -⟩ | ⟨-, hH22⟩
      · obtain ⟨a, ha⟩ := hQs
        rcases hext with ⟨V, hVn, hV, hA⟩ | ⟨V, hVn, hV, hA⟩
        · have hcV : Nat.card V = 16 := (card_isE2_kz3 hV).trans (by norm_num)
          have hcA : Nat.card (↥Q ⧸ V) = 60 := by
            rw [card_isAlt_kz3 hA, card_alternatingGroup_five_kz3]
          have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup V
          rw [hcA, hcV] at hcQ
          exact (by omega : False).elim
        · have hcV : Nat.card V = 16 := (card_isE2_kz3 hV).trans (by norm_num)
          have hcA : Nat.card (↥Q ⧸ V) = 360 := by
            rw [card_isAlt_kz3 hA, card_alternatingGroup_six_cov]
          have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup V
          rw [hcA, hcV] at hcQ
          exact (by omega : False).elim
      · exact Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv eK.symm hH22)))
    ·
      unfold A312C13 at h13
      obtain ⟨-, hM⟩ := h13
      obtain ⟨eM⟩ := hM
      have hcR : Nat.card ↥R = 10200960 := by
        rw [Nat.card_congr eM.toEquiv, hM23]
      obtain ⟨a, ha⟩ := hQs
      have h27 : 27 ∣ Nat.card ↥Q := ⟨2 ^ a * 40, by rw [ha]; ring⟩
      have h27' : 27 ∣ Nat.card ↥R := dvd_trans h27 hdvdQR
      rw [hcR] at h27'
      exact (by omega : False).elim
    ·
      unfold A312C14 at h14
      obtain ⟨-, hM⟩ := h14
      obtain ⟨eM⟩ := hM
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eK.trans eM⟩)))
    ·
      unfold A312C15 at h15
      obtain ⟨h1, -⟩ := h15
      have hc : Nat.card ↥Q = 60 := by
        rw [card_isAlt_kz3 h1, card_alternatingGroup_five_kz3]
      obtain ⟨a, ha⟩ := hQform
      exact (by omega : False).elim
    ·
      unfold A312C16 at h16
      obtain ⟨⟨V, hVn, hV, hA⟩, -⟩ := h16
      have hcV : Nat.card V = 32 := by
        rw [hV.2]
        norm_num
      have hcA : Nat.card (↥Q ⧸ V) = 60 := by
        rw [card_isAlt_kz3 hA, card_alternatingGroup_five_kz3]
      have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup V
      rw [hcA, hcV] at hcQ
      obtain ⟨a, ha⟩ := hQform
      exact (by omega : False).elim
    ·
      unfold A312C17 at h17
      obtain ⟨hJ, -⟩ := h17
      obtain ⟨eJ⟩ := hJ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eK.trans eJ⟩))))
    ·
      unfold A312C18 at h18
      obtain ⟨hdisj, -⟩ := h18
      rcases hdisj with ⟨V, hVn, hV, hA⟩ | ⟨V, hVn, hV, hA⟩
      · obtain ⟨k, hk⟩ := two_pow_card_isZ4StarExtra2_kz3 hV
        have hcA : Nat.card (↥Q ⧸ V) = 60 := by
          rw [card_isAlt_kz3 hA, card_alternatingGroup_five_kz3]
        have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup V
        rw [hcA, hk] at hcQ
        obtain ⟨a, ha⟩ := hQform
        have h3 : 2 ^ k % 3 = 0 := by omega
        have h3' : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h3
        have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
        norm_num at h32
      · have hcV : Nat.card V = 64 := card_isZ4Cubed_kz3 hV
        have hcA : Nat.card (↥Q ⧸ V) = 168 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hA
        have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup V
        rw [hcA, hcV] at hcQ
        obtain ⟨a, ha⟩ := hQform
        exact (by omega : False).elim
    ·
      unfold A312C19 at h19
      obtain ⟨-, hH⟩ := h19
      obtain ⟨eH⟩ := hH
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eK.trans eH⟩))))
    ·
      unfold A312C20 at h20
      obtain ⟨h1 | h1, -, -⟩ := h20
      · have hc : Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) = 60 := by
          rw [card_isAlt_kz3 h1, card_alternatingGroup_five_kz3]
        exact (by omega : False).elim
      · have hc : Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) = 168 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h1
        exact (by omega : False).elim
  ·
    exfalso
    obtain ⟨a, ha⟩ := hQs
    have h2Q : 2 ∣ Nat.card ↥(modO2Image Gz Lz) := ⟨2 ^ a * 540, by rw [ha]; ring⟩
    have hevR : Even (Nat.card ↥(modO2Image Gz K)) :=
      even_iff_two_dvd.mpr (dvd_trans h2Q hdvdQR)
    have hQ' : CFSG.IsQuasisimple ↥(modO2Image Gz K) := isQuasisimple_of_mulEquiv_kz3 eK hKq
    exact nonquasi_false_kz3 hQ' hevR hnq

end CFSG.Quasithin.H13
