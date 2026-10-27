module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowLieVac
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowLieVac2
public import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)


structure Seitz82Rest : Prop where
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → RowSOf148 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → RowSOf148 (projSU 4 p 1)
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → 3 ∣ n → RowSOf148 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → 3 ∣ n → RowSOf148 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → 3 ∣ n → RowSOf148 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → 3 ∣ q.exponent →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → RowSOf148 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  eight_SU5 : RowSOf148 (projSU 5 2 1)
  eight_SL6 : RowSOf148 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowSOf148 (projSU 6 2 1)
  eight_SL7 : RowSOf148 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowSOf148 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowSOf148 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSOf148 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSOf148 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSOf148 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSOf148 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowSOf148 (projSU 5 2 2)
  eight_SU5_8 : RowSOf148 (projSU 5 2 3)
  eight_F4 : RowSOf148 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

private theorem mod_three_of_prime {p : ℕ} [hp : Fact p.Prime] (h3 : 3 < p) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have h0 : p % 3 ≠ 0 := fun h => by
    have := hp.out.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  omega

theorem rowSOf148_projSU_three_two_one : RowSOf148 (projSU 3 2 1) := by
  intro S _ _ hs hna ⟨eS⟩
  exfalso
  haveI : Fintype S := Fintype.ofFinite S
  have hS : Fintype.card S = 2 ^ 3 * 3 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eS.toEquiv,
      Sec4.Item419ThetaProof.card_projSU_three_two_one]
    norm_num
  have hsol := CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) hS
  obtain ⟨a, b, hab⟩ := hna
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b)

section Certs


theorem Seitz82Balance.ofRest (h : Seitz82Rest) : Seitz82Balance where
  one p e _ hp2 hp3 he := rowSOf148_one_of_ne_three p e hp2 hp3 he
  two_SL p e _ hp he he2 := rowSOf148_projSL_three p e (by omega) he (by omega)
  two_SU p e _ hp he he2 :=
    rowSOf148_projSU_three p e (by omega) he
      (lt_of_lt_of_le (by omega : 2 < p) (Nat.le_self_pow (by omega) p)) (by omega)
  four_G2 := rowSOf148_four_G2
  four_Sp := rowSOf148_four_Sp
  four_SL p _ hp := by
    rcases mod_three_of_prime (p := p) hp with h3 | h3
    · exact h.four_SL p hp h3
    · exact rowSOf148_four_SL_of_mod_two p hp h3
  four_SU p _ hp := by
    rcases mod_three_of_prime (p := p) hp with h3 | h3
    · exact rowSOf148_four_SU_of_mod_one p hp h3
    · exact h.four_SU p hp h3
  seven_SL2 := rowSOf148_seven_SL2
  seven_SL3 n hn := by
    by_cases h3 : 3 ∣ n
    · exact h.seven_SL3 n hn h3
    · exact rowSOf148_projSL_three 2 n (by norm_num) hn h3
  seven_SU3 n hn := by
    by_cases h3 : 3 ∣ n
    · exact h.seven_SU3 n hn h3
    · by_cases hn1 : n = 1
      · subst hn1
        exact rowSOf148_projSU_three_two_one
      · have hn2 : 2 ≤ n := by omega
        refine rowSOf148_projSU_three 2 n (by norm_num) hn ?_ h3
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  seven_Sp4 n hn := by
    by_cases h3 : 3 ∣ n
    · exact h.seven_Sp4 n hn h3
    · exact rowSOf148_seven_Sp4_of n hn h3
  seven_SU4 := h.seven_SU4
  seven_G2 q hq2 hq := by
    by_cases h3 : 3 ∣ q.exponent
    · exact h.seven_G2 q hq2 h3 hq
    · exact rowSOf148_seven_G2_of q hq2 h3 hq
  seven_D4 := h.seven_D4
  seven_Sz := rowSOf148_seven_Sz
  seven_F4 := h.seven_F4
  seven_Tits := rowSOf148_seven_Tits
  eight_SL5 := rowSOf148_eight_SL5
  eight_SU5 := h.eight_SU5
  eight_SL6 := h.eight_SL6
  eight_SU6 := h.eight_SU6
  eight_SL7 := h.eight_SL7
  eight_Sp6 := h.eight_Sp6
  eight_Sp8 := h.eight_Sp8
  eight_OmegaPlus := h.eight_OmegaPlus
  eight_OmegaMinus := h.eight_OmegaMinus
  eight_SL4 := h.eight_SL4
  eight_Sp6_4 := h.eight_Sp6_4
  eight_SU5_4 := h.eight_SU5_4
  eight_SU5_8 := h.eight_SU5_8
  eight_F4 := h.eight_F4

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
