module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Tail
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3ListB
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Vol2.Ch10SecA312C6
public import CFSG.Quasithin.Vol2.Ch1EightFourInit

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem kz3_h134_card {G : Type} [Group G] [Finite G] {Gz T K P : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hM11 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920)
    (hHe : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200)
    (h134 : Kz134Tail_kz Gz T K P) :
    Even (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
      (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 5616 ∨ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 7920 ∨
        Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160 ∨ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 9999360 ∨
        Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 4030387200 ∨
        17 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  unfold Kz134Tail_kz at h134
  rcases h134 with ⟨⟨t, ht, htN, -⟩, -⟩ | ⟨-, hL3⟩ | ⟨-, ⟨m, hm, hPSp⟩, -⟩ | ⟨-, hM4⟩ |
    ⟨-, hH5⟩
  · exact absurd (hTK ht.1) htN
  · have h5616 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 5616 := by
      rcases hL3 with h | hn
      · exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three h
      · rw [Nat.card_congr hn.some.toEquiv, CFSG.Quasithin.H13.card_statedSL_three_zmod_three_kz3]
    rw [h5616]
    exact ⟨by norm_num, Or.inl rfl⟩
  · obtain ⟨h2, h17⟩ := CFSG.Quasithin.H13.two_and_seventeen_dvd_card_psp_kz3 hPSp hm
    exact ⟨even_iff_two_dvd.mpr h2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h17))))⟩
  · rcases hM4 with hn | h | h
    · rw [Nat.card_congr hn.some.toEquiv, hM11]
      exact ⟨by norm_num, Or.inr (Or.inl rfl)⟩
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h]
      exact ⟨by norm_num, Or.inr (Or.inr (Or.inl rfl))⟩
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h]
      exact ⟨by norm_num, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · rw [Nat.card_congr hH5.some.toEquiv, hHe]
    exact ⟨by norm_num, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩

theorem card_isElemAbelianOfRank_kz3 {p n : ℕ} (hp : p.Prime) {V : Type} [Group V]
    (h : IsElemAbelianOfRank p n V) : Nat.card V = p ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr h.some.toEquiv]
  change Nat.card (Fin n → ZMod p) = p ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem kz3_list_match {G : Type} [Group G] [Finite G] (hloc : LocalSQTK G)
    (h312 : A312ForSQTKCat)
    {Gz T Lz K P : Subgroup G} (hT : IsSylowTwoOf T Gz) (hpC : pCoreOf 2 Gz ≠ ⊥)
    (hLzG : Lz ≤ Gz) (hLzF : Lz ∈ lFamily T) (hLzP : ⁅Lz, Lz⁆ = Lz)
    (hLzq : IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz) ∨
      IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)))
    (hK : K ∈ cComp Gz) (hLK : Lz ≤ K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (h134 : Kz134Tail_kz Gz T K P)
    (hM11 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920)
    (hHe : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200)
    (hM23 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960)
    (hM24 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040)
    (hJ4 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) = 86775571046077562880) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) ∧
        Nat.card (modO2Image Gz Lz) = 69120) := by
  obtain ⟨hevn, hnl⟩ := kz3_h134_card hTK hM11 hHe h134
  have eK := (modO2_mulEquiv hK).some
  set n := Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) with hn
  have hnR : Nat.card ↥(modO2Image Gz K) = n := (Nat.card_congr eK.toEquiv).symm
  obtain ⟨hQform, hMQ⟩ := card_modO2_form_kz3 hLzG hLzq
  rcases CFSG.QuasithinUnique.Vol2Native.lemma_1_2_4_list hloc h312 hpC hT hLzG hLzF hK hLK
    with hEq | hcase | hnq
  ·
    exfalso
    have hcard : Nat.card ↥(modO2Image Gz Lz) = n := by rw [hEq, hnR]
    have hprime : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3 ∨ p = 5 := by
      intro p hp hpn
      obtain ⟨a, ha⟩ := hQform
      exact dvd_prime_of_card_form_kz3 ⟨a, by rw [← hcard]; exact ha⟩ hp hpn
    rcases hnl with h | h | h | h | h | h
    · have := hprime 13 (by norm_num) (by rw [h]; norm_num)
      exact (by omega : False).elim
    · have := hprime 11 (by norm_num) (by rw [h]; norm_num)
      exact (by omega : False).elim
    · have := hprime 7 (by norm_num) (by rw [h]; norm_num)
      exact (by omega : False).elim
    · have := hprime 7 (by norm_num) (by rw [h]; norm_num)
      exact (by omega : False).elim
    · have := hprime 7 (by norm_num) (by rw [h]; norm_num)
      exact (by omega : False).elim
    · have := hprime 17 (by norm_num) h
      exact (by omega : False).elim
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
      rcases h7 with ⟨-, h2'⟩ | ⟨-, h2'⟩
      · have hc : Nat.card ↥R = 2520 := by
          rw [card_isAlt_kz3 h2', card_alternatingGroup_seven_kz3]
        exact (by omega : False).elim
      · have hc : Nat.card ↥R = 7560 := CFSG.Quasithin.Vol2.Ch10.A312C.card_hat7 h2'
        exact (by omega : False).elim
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
      rcases h9 with ⟨s, p, hp, hp3, hSL2, -⟩ | ⟨-, h2'⟩ | ⟨-, h2'⟩
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
      · have hc : Nat.card ↥R = 126000 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five h2'
        exact (by omega : False).elim
      · have hc : Nat.card ↥R = 378000 := CFSG.Quasithin.Vol2.Ch10.A312C.card_su35 h2'
        exact (by omega : False).elim
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
      obtain ⟨-, hM⟩ := h11
      obtain ⟨eM⟩ := hM
      exact Or.inl ⟨eK.trans eM⟩
    ·
      unfold A312C12 at h12
      rcases h12 with ⟨-, hM22⟩ | ⟨-, hH22⟩
      · obtain ⟨eM⟩ := hM22
        have hc : Nat.card ↥R = 443520 := by
          rw [Nat.card_congr eM.toEquiv]
          exact CFSG.RankThree.PartTwo.Sec4.Item426.card_M22
        exact (by omega : False).elim
      · have hc : Nat.card ↥R = 3 * 443520 := by
          rw [card_isHat_kz3 hH22]
          congr 1
          exact CFSG.RankThree.PartTwo.Sec4.Item426.card_M22
        exact (by omega : False).elim
    ·
      unfold A312C13 at h13
      obtain ⟨-, hM⟩ := h13
      obtain ⟨eM⟩ := hM
      have hc : Nat.card ↥R = 10200960 := by
        rw [Nat.card_congr eM.toEquiv, hM23]
      exact (by omega : False).elim
    ·
      unfold A312C14 at h14
      obtain ⟨-, hM⟩ := h14
      obtain ⟨eM⟩ := hM
      have hc : Nat.card ↥R = 244823040 := by
        rw [Nat.card_congr eM.toEquiv, hM24]
      exact (by omega : False).elim
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
      have hc : Nat.card ↥R = 86775571046077562880 := by
        rw [Nat.card_congr eJ.toEquiv, hJ4]
      exact (by omega : False).elim
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
      obtain ⟨hdisj, hH⟩ := h19
      obtain ⟨eH⟩ := hH
      rcases hdisj with ⟨V, hVn, hV, hA⟩ | ⟨V, hVn, hV, hA⟩
      · have hcV : Nat.card V = 128 := by
          rw [hV.2]
          norm_num
        have hcA : Nat.card (↥Q ⧸ V) = 168 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hA
        have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup V
        rw [hcA, hcV] at hcQ
        obtain ⟨a, ha⟩ := hQform
        exact (by omega : False).elim
      · have hcV : Nat.card V = 64 := card_isE2_kz3 hV
        have hcA : Nat.card (↥Q ⧸ V) = 1080 :=
          CFSG.Quasithin.SmithC27.card_of_isHat_alt6 hA
        have hcQ : Nat.card ↥Q = Nat.card (↥Q ⧸ V) * Nat.card V :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup V
        rw [hcA, hcV] at hcQ
        exact Or.inr ⟨⟨eK.trans eH⟩, by rw [hcQ]⟩
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
    have hQ' : CFSG.IsQuasisimple ↥(modO2Image Gz K) := isQuasisimple_of_mulEquiv_kz3 eK hKq
    exact nonquasi_false_kz3 hQ' (by rw [hnR]; exact hevn) hnq

end CFSG.Quasithin.H13
