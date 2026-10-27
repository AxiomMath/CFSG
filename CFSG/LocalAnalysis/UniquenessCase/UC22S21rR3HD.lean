module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5R
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HB
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HC
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3Res
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3h_three_dvd_of_isSz {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h15 : S21_15C D Ch) (h1930 : H1930 D)
    (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn : 2 < n) (hSz : IsSz (Bar2 L) n) :
    3 ∣ n := by
  by_contra h3n
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet (uc22r3h_three_mem_piSet c hn3 hpow)
  have hqL : ¬ 3 ∣ Nat.card (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hmemK : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hmemK]; exact hc2
  have hbq : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, -, -, hc⟩ :=
    u4x_bar_decomp hL hK hne hset (Or.inr hSz) Nat.prime_three h3n (b := ⟨b, c.hBM hb⟩)
      (uc22p2214_mem_normalizer_of_odd hc2 (c.hBM hb) hodd)
      (uc22p2214_mem_normalizer_of_odd hcK (c.hBM hb) hodd) (Subtype.ext (by simpa using hbq))
  obtain ⟨e₀, -⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eK⟩ := u4x_bar2_equiv hmemK
  have h0 : x₀ = 1 :=
    u4x_eq_one_of_pow hx₀ Nat.prime_three (by rwa [← Nat.card_congr e₀.toEquiv]) hx₀q
  have h1 : x₁ = 1 :=
    u4x_eq_one_of_pow hx₁ Nat.prime_three (by rwa [← Nat.card_congr (eK.trans e₁).toEquiv]) hx₁q
  subst h0 h1
  obtain ⟨-, -, -, -, hX, -, -⟩ := u4x_bar_structure hL hK hne hset (Or.inr hSz)
  have hw : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩ ∈
      centralizer ((barImage D.M (conjClosure D.M L) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
    rw [hX]
    simpa using hc
  obtain ⟨p, hp⟩ := hSg.nonempty
  have u : R3Pair D L K n p :=
    ⟨hL, hK, hne, hset, hc2, hn, hp, h15 h1930 c L hL hc2 n (Or.inl hSz) p hp⟩
  exact u4p_not_mem_centralizer h869 h1930 c hL u.pX hb Nat.prime_three (by norm_num) hbo hw

theorem s21_22R3E5_of_s21_22R3E5R {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (h211 : S21_1 D Ch)
    (h82 : F08.R82 D) (h8107 : F08.R8107 D) (h869 : F08.R869NS5 D) (h15 : S21_15C D Ch)
    (h847T : R847E3Thin D) (h16 : S21_16 D Ch) (h17 : S21_17 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hR : S21_22R3E5R D Ch) : S21_22R3E5 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hcomm hcent hsig he hpow L hL hc2 n hn hS
  have hR' := hR h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hcomm hcent hsig he hpow
  have hn3' := hn3 h1930 c
  have hSzP : ∀ {Y : Subgroup G}, Y ∈ calC D.M → (conjSetOf D.M Y).ncard = 2 → ∀ {m : ℕ},
      2 < m → IsSz (Bar2 Y) m → False := fun hY hcY m hm hSz =>
    hR' _ hY hcY m hm
      (Or.inl ⟨hSz, uc22r3h_three_dvd_of_isSz hSg h869 h15 h1930 c hn3' hpow hY hcY hm hSz⟩)
  rcases hS with hL2 | hSz
  swap
  · exact hSzP hL hc2 hn hSz
  by_cases hall : ∀ p ∈ D.sig, p ∣ n
  ·
    refine hR' L hL hc2 n hn (Or.inr ⟨hL2, ?_, hall⟩)
    rintro ⟨k, rfl⟩
    obtain ⟨p, hp⟩ := hSg.nonempty
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow (hall p hp)))
  obtain ⟨p, hp, hpn⟩ : ∃ p ∈ D.sig, ¬ p ∣ n := by
    by_contra h
    exact hall fun p hp => not_not.1 fun hpn => h ⟨p, hp, hpn⟩
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨L', hL', h₁, h₂⟩ :=
    uc22r3h_exists_other_member hSg he hL hK hne hset (Or.inl hL2) hp hpn (hcent p hp)
  have h3 := uc22r3h_not_three_dvd_card h82 he h1930 c hn3' hpow hL hK hne hset hL2 hL' h₁ h₂
  obtain ⟨a, hSz'⟩ := uc22r3h_isSz_of_not_three_dvd h16 h1930 c hL' h3
  rcases h17 h1930 c L' hL' with hN | ⟨hc2', m, hm, hS'⟩ | ⟨-, -, hc3, -⟩
  · exact uc22r3h_false_of_normal_sz hSg h13 h211 h8107 h847T h1930 c he hcent hL hK hne hset hL2
      hL' h₁ h₂ (uc22p21j_normal_of_conjClosure_eq (PartTwo.s13_le_of_mem_calC hL') hN) hSz'
  · rcases hS' with hL2' | hSz''
    · exact h3 (PartTwo.S17.three_dvd_card_of_bar_isL2Even hL2')
    · exact hSzP hL' hc2' hm hSz''
  · rw [hc3] at hpow
    exact uc22s21ru4e_not_isPowTwo_three hpow

end CFSG.LocalAnalysis.UniquenessCase.UC22
