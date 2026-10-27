module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem SumOfNatShape.small_cases_of_not_sixteen_dvd_card
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (h16 : ¬ 16 ∣ Nat.card ↥L)
    (hs : SumOfNatShape L U Z k) :
    (IsSLn ↥L 3 1 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L U Z k) ∨
    (IsOmegaMinus ↥L 4 1 ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 1) L U Z k) ∨
    (∃ n : ℕ, UC22.IsAlt ↥L n ∧
      SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z k) := by
  obtain ⟨n, h | h | h | h | h⟩ := hs
  ·
    obtain ⟨hSL, hsum⟩ := h
    have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hq hSL
    by_cases hn4 : 4 ≤ n
    · obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hSL
      letI : Field K := hF
      letI : Finite K := hFin
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hcard : Nat.card ↥L = Nat.card (StatedSL n K) := Nat.card_congr e.toEquiv
      have h16' : (16 : ℕ) ∣ Nat.card ↥L := by
        rw [hcard, CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := n) (by omega),
          hK2]
        have hexp : 4 ≤ n * (n - 1) / 2 := by
          have h8 : 4 * 2 ≤ n * (n - 1) := by
            have h12 := Nat.mul_le_mul hn4 (by omega : 3 ≤ n - 1)
            omega
          exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h8
        exact dvd_mul_of_dvd_left (by simpa using Nat.pow_dvd_pow 2 hexp) _
      exact absurd h16' h16
    · have hn : n = 3 := by omega
      exact Or.inl ⟨by simpa [hn] using hSL, by simpa [hn] using hsum⟩
  ·
    obtain ⟨hSp, -⟩ := h
    have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hq hSp
    obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hSp
    letI : Field K := hF
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hm : 3 ≤ n / 2 := by omega
    have hcard : Nat.card ↥L = Nat.card (StatedSp (n / 2) K) := Nat.card_congr e.toEquiv
    have h16' : (16 : ℕ) ∣ Nat.card ↥L := by
      rw [hcard,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) (r := n / 2),
        hK2]
      have hexp : 4 ≤ (n / 2) ^ 2 := by
        rw [sq]
        have h9 := Nat.mul_le_mul hm hm
        omega
      exact dvd_mul_of_dvd_left (by simpa using Nat.pow_dvd_pow 2 hexp) _
    exact absurd h16' h16
  ·
    obtain ⟨hOP, -⟩ := h
    have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hq hOP
    have hOP' := hOP
    obtain ⟨hEven, K, hF, hFin, hK, ⟨e⟩⟩ := hOP
    letI : Field K := hF
    letI : Finite K := hFin
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) hK
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hcard : Nat.card ↥L =
        Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) := Nat.card_congr e.toEquiv
    rcases Nat.lt_or_ge (n / 2) 4 with hm | hm4
    · have hm3 : n / 2 = 3 := by omega
      have hn : n = 6 := by
        have h2 := Nat.two_mul_div_two_of_even hEven
        omega
      have hOP6 : IsOmegaPlus ↥L 6 1 := by simpa [hn] using hOP'
      have hcardL : Nat.card ↥L = 20160 := by
        rw [s15k_six_alt_card (s15k_omp6_isAlt8 hOP6) (by norm_num)]
        norm_num [Nat.factorial]
      have h16' : (16 : ℕ) ∣ Nat.card ↥L := by
        rw [hcardL]
        norm_num
      exact absurd h16' h16
    · have h16' : (16 : ℕ) ∣ Nat.card ↥L := by
        have hdiv : (16 : ℕ) ∣ Nat.card ↥L := by
          have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
            (K := K) (n := n / 2) hm4
          have hdivz : (16 : ℤ) ∣ (Nat.card ↥L : ℤ) := by
            rw [hcard, hz]
            simp only [hK2, Nat.cast_ofNat]
            refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ?_ _) _
            rw [show (16 : ℤ) = (2 : ℤ) ^ 4 by norm_num]
            have hmul : 4 * 3 ≤ (n / 2) * (n / 2 - 1) :=
              Nat.mul_le_mul hm4 (by omega : 3 ≤ n / 2 - 1)
            exact pow_dvd_pow 2 (by norm_num at hmul ⊢; omega)
          exact Int.natCast_dvd_natCast.mp hdivz
        exact hdiv
      exact absurd h16' h16
  ·
    obtain ⟨hOM, hsum⟩ := h
    have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hq hOM
    have hOM' := hOM
    obtain ⟨hEven, K, hF, hFin, b, c, hK, hirr, ⟨e⟩⟩ := hOM
    letI : Field K := hF
    letI : Finite K := hFin
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) hK
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hcard : Nat.card ↥L =
        Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
      Nat.card_congr e.toEquiv
    rcases Nat.lt_or_ge (n / 2) 4 with hm | hm4
    · rcases Nat.lt_or_ge (n / 2) 3 with hm3 | hm3
      · have hm2 : n / 2 = 2 := by omega
        have hn : n = 4 := by
          have h2 := Nat.two_mul_div_two_of_even hEven
          omega
        exact Or.inr (Or.inl ⟨by simpa [hn] using hOM', by simpa [hn] using hsum⟩)
      · have hm3' : n / 2 = 3 := by omega
        have hn : n = 6 := by
          have h2 := Nat.two_mul_div_two_of_even hEven
          omega
        have hOM6 : IsOmegaMinus ↥L 6 1 := by simpa [hn] using hOM'
        have hcardL : Nat.card ↥L = 25920 := (s15k_six_om6 hOM6).1
        have h16' : (16 : ℕ) ∣ Nat.card ↥L := by
          rw [hcardL]
          norm_num
        exact absurd h16' h16
    · have h16' : (16 : ℕ) ∣ Nat.card ↥L := by
        have hdiv : (16 : ℕ) ∣ Nat.card ↥L := by
          have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
            (K := K) (n := n / 2) (b := b) (c := c) hm4 hirr
          have hdivz : (16 : ℤ) ∣ (Nat.card ↥L : ℤ) := by
            rw [hcard, hz]
            simp only [hK2, Nat.cast_ofNat]
            refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ?_ _) _
            rw [show (16 : ℤ) = (2 : ℤ) ^ 4 by norm_num]
            have hmul : 4 * 3 ≤ (n / 2) * (n / 2 - 1) :=
              Nat.mul_le_mul hm4 (by omega : 3 ≤ n / 2 - 1)
            exact pow_dvd_pow 2 (by norm_num at hmul ⊢; omega)
          exact Int.natCast_dvd_natCast.mp hdivz
        exact hdiv
      exact absurd h16' h16
  ·
    exact Or.inr (Or.inr ⟨n, h.1, h.2⟩)

theorem SumOfNatShape.sl3_of_card_eq_168
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (hc : Nat.card ↥L = 168)
    (hs : SumOfNatShape L U Z k) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L U Z k := by
  have h16 : ¬ 16 ∣ Nat.card ↥L := by rw [hc]; norm_num
  rcases SumOfNatShape.small_cases_of_not_sixteen_dvd_card hq h16 hs with
    ⟨-, hsum⟩ | ⟨hOM4, -⟩ | ⟨n, hAlt, -⟩
  · exact hsum
  ·
    have hcardL : Nat.card ↥L = 60 := by
      rw [s15k_six_alt_card (s16k_isAlt_five_of_isOmegaMinus_four hOM4) (by norm_num : 2 ≤ 5)]
      norm_num [Nat.factorial]
    omega
  ·
    have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hq hAlt
    have hcard : Nat.card ↥L = n.factorial / 2 := s15k_six_alt_card hAlt (by omega)
    have h5 : (5 : ℕ) ∣ Nat.card ↥L := by
      rw [hcard]
      have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have hmul : 5 ∣ 2 * (n.factorial / 2) := by
        rw [Nat.mul_div_cancel' h2]
        exact Nat.dvd_factorial (by norm_num) hn5
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : (5 : ℕ).Coprime 2) hmul)
    rw [hc] at h5
    norm_num at h5

theorem SumOfNatShape.alt_seven_of_card_eq_2520
    {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (hc : Nat.card ↥L = 2520)
    (hs : SumOfNatShape L U Z k) :
    UC22.IsAlt ↥L 7 ∧
      SumOfNat (fun H U Z => AlternatingNatural H U Z 7) L U Z k := by
  have h16 : ¬ 16 ∣ Nat.card ↥L := by rw [hc]; norm_num
  rcases SumOfNatShape.small_cases_of_not_sixteen_dvd_card hq h16 hs with
    ⟨hSL3, -⟩ | ⟨hOM4, -⟩ | ⟨n, hAlt, hsum⟩
  ·
    obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hSL3
    letI : Field K := hF
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hcard : Nat.card ↥L = 168 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 3) (by norm_num), hK2]
      decide +kernel
    omega
  ·
    have hcardL : Nat.card ↥L = 60 := by
      rw [s15k_six_alt_card (s16k_isAlt_five_of_isOmegaMinus_four hOM4) (by norm_num : 2 ≤ 5)]
      norm_num [Nat.factorial]
    omega
  ·
    have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hq hAlt
    have hcard := s15k_six_alt_card hAlt (by omega : 2 ≤ n)
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hmul := Nat.mul_div_cancel' h2
    rw [← hcard, hc] at hmul
    have hfac : n.factorial = (7 : ℕ).factorial := by
      rw [hmul.symm]
      norm_num [Nat.factorial]
    have hn : n = 7 := (Nat.factorial_inj (by omega : 1 < n)).mp hfac
    subst n
    exact ⟨hAlt, hsum⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
