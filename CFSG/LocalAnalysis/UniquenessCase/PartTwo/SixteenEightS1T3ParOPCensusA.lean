module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOPDef

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial

private theorem s16t3_gcd_three_pow_six_succ (k : ℕ) : Nat.gcd (3 ^ (k + 1)) 6 = 3 := by
  rw [pow_succ', show (6 : ℕ) = 3 * 2 from rfl, Nat.gcd_mul_left]
  have hcop : Nat.Coprime (3 ^ k) 2 :=
    ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow_left k
  rw [show Nat.gcd (3 ^ k) 2 = 1 from hcop, mul_one]

theorem s16t3_pow_three_of_card_dvd_six {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G ∣ 6) (g : G) (k : ℕ) (hg : g ^ 3 ^ k = 1) : g ^ 3 = 1 := by
  haveI := Fintype.ofFinite G
  have h2 : orderOf g ∣ 6 := by
    have h : orderOf g ∣ Nat.card G := by
      simpa only [Nat.card_eq_fintype_card] using orderOf_dvd_card (x := g)
    exact h.trans hcard
  rcases k with _ | k
  · have h1 : orderOf g ∣ 1 := by simpa using orderOf_dvd_of_pow_eq_one hg
    have hg1 : g = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    rw [hg1, one_pow]
  · have h1 : orderOf g ∣ 3 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hg
    have h3 : orderOf g ∣ Nat.gcd (3 ^ (k + 1)) 6 := Nat.dvd_gcd h1 h2
    rw [s16t3_gcd_three_pow_six_succ k] at h3
    exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem s16t3_range_toGL_eq_top {K : Type} [Field K] (hK : Nat.card K = 2) (k : ℕ) :
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range = ⊤ := by
  have hunit : ∀ c : Kˣ, c = 1 := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun c => Subsingleton.elim c 1
  rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
  exact (Subgroup.eq_top_iff' _).mpr fun g => MonoidHom.mem_ker.mpr (hunit _)

private theorem s16t3_card_GL (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (k : ℕ) :
    Nat.card (GL (Fin k) K) = ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  letI := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field (n := k) (𝔽 := K), hK']

theorem s16t3_card_GL_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {k : ℕ}
    (hk : k ≤ 1) : Nat.card (GL (Fin k) K) = 1 := by
  interval_cases k <;> rw [s16t3_card_GL K hK] <;> decide

theorem s16t3_card_GL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (GL (Fin 2) K) = 6 := by
  rw [s16t3_card_GL K hK]; decide

theorem s16t3_mem_plusCuts {m d : ℕ} :
    d ∈ s16t3PlusCuts m ↔ 1 ≤ d ∧ d ≤ m - 2 ∧ (d % 2 = 0 ∨ d = m - 2) := by
  simp only [s16t3PlusCuts, Finset.mem_filter, Finset.mem_Icc]
  tauto

private theorem s16t3_le_sub_two_of_even {c b : ℕ} (hc : Even c) (hb : Even b) (hcb : c < b) :
    c ≤ b - 2 := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨l, rfl⟩ := hb
  omega

private theorem s16t3_predCut_even {m b : ℕ} (hb : b ∈ s16t3PlusCuts m) (he : b % 2 = 0) :
    predCut (s16t3PlusCuts m) b = b - 2 := by
  have hb2 : b ≤ m - 2 := (s16t3_mem_plusCuts.mp hb).2.1
  have hbe : Even b := Nat.even_iff.mpr he
  have hb2' : 2 ≤ b := by
    obtain ⟨k, hk⟩ := hbe
    have h1 : 1 ≤ b := (s16t3_mem_plusCuts.mp hb).1
    omega
  rw [predCut]
  refine le_antisymm (Finset.sup_le fun c hc => ?_) ?_
  · obtain ⟨hcD, hclt⟩ := Finset.mem_filter.mp hc
    change c ≤ b - 2
    rcases (s16t3_mem_plusCuts.mp hcD).2.2 with hce | hce
    · exact s16t3_le_sub_two_of_even (Nat.even_iff.mpr hce) hbe hclt
    · omega
  · by_cases h2 : b = 2
    · omega
    · have hb3 : 2 < b := by omega
      have hmem : b - 2 ∈ s16t3PlusCuts m := by
        refine s16t3_mem_plusCuts.mpr ⟨by omega, by omega, Or.inl ?_⟩
        have hev : Even (b - 2) := by
          rw [Nat.even_sub hb2']
          exact iff_of_true hbe ⟨1, by norm_num⟩
        exact Nat.even_iff.mp hev
      exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hmem, by omega⟩)

private theorem s16t3_predCut_odd {m b : ℕ} (hb : b ∈ s16t3PlusCuts m) (ho : b % 2 ≠ 0) :
    predCut (s16t3PlusCuts m) b = b - 1 := by
  have hb1 : 1 ≤ b := (s16t3_mem_plusCuts.mp hb).1
  have hbm : b = m - 2 := by
    rcases (s16t3_mem_plusCuts.mp hb).2.2 with h | h
    · exact absurd h ho
    · exact h
  rw [predCut]
  refine le_antisymm (Finset.sup_le fun c hc => ?_) ?_
  · have hclt : c < b := (Finset.mem_filter.mp hc).2
    change c ≤ b - 1
    omega
  · by_cases h1 : b = 1
    · omega
    · have hb2 : 2 ≤ b := by omega
      have hmem : b - 1 ∈ s16t3PlusCuts m := by
        refine s16t3_mem_plusCuts.mpr ⟨by omega, by omega, Or.inl ?_⟩
        have hob : ¬ Even b := fun h => ho (Nat.even_iff.mp h)
        have hev : Even (b - 1) :=
          (Nat.even_sub hb1).mpr (iff_of_false hob Nat.not_even_one)
        exact Nat.even_iff.mp hev
      exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hmem, by omega⟩)

theorem s16t3_plus_blen_even {m b : ℕ} (hb : b ∈ s16t3PlusCuts m) (he : b % 2 = 0) :
    b - predCut (s16t3PlusCuts m) b = 2 := by
  have hbe : Even b := Nat.even_iff.mpr he
  have hb2' : 2 ≤ b := by
    obtain ⟨k, hk⟩ := hbe
    have h1 : 1 ≤ b := (s16t3_mem_plusCuts.mp hb).1
    omega
  rw [s16t3_predCut_even hb he]
  omega

theorem s16t3_plus_blen_odd {m b : ℕ} (hb : b ∈ s16t3PlusCuts m) (ho : b % 2 ≠ 0) :
    b - predCut (s16t3PlusCuts m) b = 1 := by
  have hb1 : 1 ≤ b := (s16t3_mem_plusCuts.mp hb).1
  rw [s16t3_predCut_odd hb ho]
  omega

private theorem s16t3_plus_filter_even (m : ℕ) :
    (s16t3PlusCuts m).filter (fun d => d % 2 = 0) =
      (Finset.Icc 1 ((m - 2) / 2)).image (fun i => 2 * i) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, he⟩
    have hb1 : 1 ≤ d := (s16t3_mem_plusCuts.mp hd).1
    have hb2 : d ≤ m - 2 := (s16t3_mem_plusCuts.mp hd).2.1
    have hev : Even d := Nat.even_iff.mpr he
    have hd2 : d = 2 * (d / 2) := (Nat.two_mul_div_two_of_even hev).symm
    refine ⟨d / 2, ⟨?_, ?_⟩, hd2.symm⟩
    · rcases Nat.eq_zero_or_pos (d / 2) with h | h
      · rw [h, mul_zero] at hd2
        omega
      · exact h
    · exact Nat.div_le_div_right hb2
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine ⟨s16t3_mem_plusCuts.mpr ⟨by omega, ?_, Or.inl (Nat.mul_mod_right 2 i)⟩,
      Nat.mul_mod_right 2 i⟩
    calc 2 * i ≤ 2 * ((m - 2) / 2) := Nat.mul_le_mul_left 2 hi2
      _ ≤ m - 2 := by rw [mul_comm]; exact Nat.div_mul_le_self (m - 2) 2

theorem s16t3_plus_block_card (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    Nat.card (∀ b : ↥(s16t3PlusCuts m),
      GL (Fin (b.1 - predCut (s16t3PlusCuts m) b.1)) K) = 6 ^ ((m - 2) / 2) := by
  have hstep : ∀ b ∈ s16t3PlusCuts m,
      Nat.card (GL (Fin (b - predCut (s16t3PlusCuts m) b)) K) =
        if b % 2 = 0 then 6 else 1 := by
    intro b hb
    by_cases he : b % 2 = 0
    · rw [if_pos he, s16t3_plus_blen_even hb he, s16t3_card_GL_two hK]
    · rw [if_neg he, s16t3_plus_blen_odd hb he, s16t3_card_GL_one hK le_rfl]
  rw [Nat.card_pi, Finset.prod_coe_sort (s := s16t3PlusCuts m)
    (f := fun b => Nat.card (GL (Fin (b - predCut (s16t3PlusCuts m) b)) K)),
    Finset.prod_congr rfl hstep]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
    s16t3_plus_filter_even, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have hij' : 2 * i = 2 * j := hij
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
