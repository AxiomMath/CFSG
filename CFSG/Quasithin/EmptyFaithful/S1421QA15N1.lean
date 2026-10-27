module

public import CFSG.Quasithin.EmptyFaithful.T1515eD
public import CFSG.Sporadic.J4

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Quasithin.A3Facts CFSG.SectionRank

theorem L3Free1515e.of_check_bound {N q₀ B : ℕ}
    (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hsl : ∀ q < B, (2 ≤ q ∧ q % 3 = 1 ∧ q ≠ q₀ ∧ q ^ 3 ∣ N) →
      N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (hsu : ∀ q < B, (2 ≤ q ∧ q % 3 = 2 ∧ q ^ 3 ∣ N) →
      N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    L3Free1515e N q₀ := by
  have hmono : ∀ q, B ≤ q →
      B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := fun q hq =>
    Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
  have hgcd : ∀ a : ℕ, N * Nat.gcd 3 a ≤ 3 * N := fun a =>
    calc N * Nat.gcd 3 a ≤ N * 3 :=
          Nat.mul_le_mul_left N (Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 a))
      _ = 3 * N := mul_comm N 3
  refine ⟨fun q hq h3 h0 hd => ?_, fun q hq h3 hd => ?_⟩
  · by_cases hqB : q < B
    · exact hsl q hqB ⟨hq, h3, h0, hd⟩
    · intro heq
      have h1 := lt_of_lt_of_le hB (hmono q (not_lt.mp hqB))
      rw [← heq] at h1
      exact absurd (hgcd (q - 1)) (not_le.mpr h1)
  · by_cases hqB : q < B
    · exact hsu q hqB ⟨hq, h3, hd⟩
    · intro heq
      have h2 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      have h1 := lt_of_lt_of_le (lt_of_lt_of_le hB (hmono q (not_lt.mp hqB))) h2
      rw [← heq] at h1
      exact absurd (hgcd (q + 1)) (not_le.mpr h1)

theorem l3Free_86775571046077562880 : L3Free1515e 86775571046077562880 0 :=
  L3Free1515e.of_check_bound (B := 400) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_44352000 : L3Free1515e 44352000 0 :=
  L3Free1515e.of_check_bound (B := 16) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_145926144000 : L3Free1515e 145926144000 0 :=
  L3Free1515e.of_check_bound (B := 32) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem two_le_pRank_J4_1515e [Finite NativeSporadic.J4] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.J4) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := J4_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_cubic (by norm_num) hxy hcard

theorem two_le_pRank_HS_1515e [Finite NativeSporadic.HS] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.HS) := by
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ := HS_sylow3_square_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_square hx hy hxy hcard

theorem two_le_pRank_Ru_1515e [Finite NativeSporadic.Ru] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.Ru) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := Ru_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_cubic (by norm_num) hxy hcard

theorem a318Exclusion_j4
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J4 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.J4.fam_j4_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .J4) hfin hs two_le_pRank_J4_1515e
    CFSG.Sporadic.J4.card_J4 l3Free_86775571046077562880 h

theorem a318Exclusion_hs
    {X : Type} [Group X] [Finite X] (h : IsSporadic .HS X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.HS.fam_hs_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .HS) hfin hs two_le_pRank_HS_1515e
    CFSG.Sporadic.HS.card_HS l3Free_44352000 h

theorem a318Exclusion_ru
    {X : Type} [Group X] [Finite X] (h : IsSporadic .Ru X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Ru.fam_ru_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .Ru) hfin hs two_le_pRank_Ru_1515e
    CFSG.Sporadic.Ru.card_Ru l3Free_145926144000 h

end CFSG.Quasithin
