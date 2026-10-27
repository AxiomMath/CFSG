module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusE16Lie
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusNine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.TypeL3Two
public import CFSG.GF2Type.Smith1979.W4AsSurvL28
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusL2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Row

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.card_dvd (hcfg : OLCfg P L Q) {S : Type} [Group S] (φ : ↥L ≃* S) :
    Nat.card S ∣ 1382446517760 := by
  rw [← Nat.card_congr φ.toEquiv, ← card_X hcfg.triple]
  exact Subgroup.card_subgroup_dvd_card L

theorem olRow_L2_inner (p k : ℕ) [Fact p.Prime] (hk : k = 1 ∨ k = 2) (h4 : 4 ≤ p ^ k)
    (h9 : ¬ 9 ∣ Nat.card (projSL 2 (GaloisField p k))) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p k))) := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by omega)
  haveI : IsSimpleGroup (projSL 2 (GaloisField p k)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField p k) le_rfl
      (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega))
  have hinn : InnerThree (projSL 2 (GaloisField p k)) := by
    refine InnerThree.of_mulEquiv (Sec4.projSLEquivPSLn 2 (GaloisField p k)) fun σ hσ => ?_
    have hodd : Odd (orderOf σ) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσ) with h | h
      · rw [h]; exact odd_one
      · rw [h]; decide
    exact CFSG.ASVolI.burnsideA315x_psl2_odd_inner hp hK hk σ hodd
  exact olRow_of_innerThree _ hinn fun B V => not_innerCfg_of_not_dvd h9 B V

theorem olRow_six_L2 (n : ℕ) (hn : 1 ≤ n) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField 2 n))) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLN := hcfg.card_dvd φ
  have hc := Sec11.KSListsProof.card_projSL_two_mul (GaloisField 2 n)
  rw [hK] at hc
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have hodd : Odd (2 ^ n - 1) := by
      have : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
      rw [Nat.odd_sub (by omega)]
      simp [Nat.even_pow, show n ≠ 0 by omega]
    exact (Nat.coprime_two_left.mpr hodd)
  rw [hg, mul_one] at hc
  have h2 : 2 ^ n ∣ 1382446517760 := by
    rw [hc] at hLN; exact (dvd_mul_right _ _).trans hLN
  have hn9 := two_pow_dvd_N h2
  have hqL := hcfg.isQuasisimple
  interval_cases n
  · exact Sec13.Res5Proof.false_of_projSL_two_small (Or.inl (by rw [hK]; norm_num)) hqL φ
  · exact olRow_L2_inner 2 2 (Or.inr rfl) (by norm_num) (by rw [hc]; norm_num) X P L Q hcfg ⟨φ⟩
  · haveI : IsSimpleGroup (projSL 2 (GaloisField 2 3)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 3) le_rfl
        (Or.inr (by rw [hK]; norm_num)) (Or.inr (by rw [hK]; norm_num))
    have hZL := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hqL φ
    let e : ↥L ⧸ Subgroup.center ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
      (((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).trans φ).trans
        (Sec4.projSLEquivPSLn 2 (GaloisField 2 3))
    obtain ⟨y, hy⟩ := CFSG.GF2Type.Smith1979.W4As.Surv.exists_orderOf_nine_of_psl28 e
    exact hcfg.false_of_orderOf_nine hZL y hy
  · rw [hc] at hLN; norm_num at hLN
  · exact olRow_of_E16 _ exists_E16_projSL_two_thirtytwo X P L Q hcfg ⟨φ⟩
  all_goals (rw [hc] at hLN; norm_num at hLN)

theorem olRow_six_L3 (n : ℕ) (hn : 1 ≤ n) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 2 n))) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLN := hcfg.card_dvd φ
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
  rw [hK] at hc
  have h3 : (2 ^ n) ^ 3 ∣ Nat.card (projSL 3 (GaloisField 2 n)) := by
    have h' : (2 ^ n) ^ 3 ∣ Nat.card (projSL 3 (GaloisField 2 n)) * Nat.gcd 3 (2 ^ n - 1) := by
      rw [hc]; exact dvd_mul_right _ _
    rw [← pow_mul] at h' ⊢
    exact (coprime_pow_of_dvd Nat.prime_two (Nat.gcd_dvd_left 3 _) (by norm_num)).dvd_of_dvd_mul_right h'
  have hn3 := two_pow_dvd_N ((by rw [← pow_mul] at h3; exact h3 : 2 ^ (n * 3) ∣ _).trans hLN)
  have hn3' : n ≤ 3 := by omega
  interval_cases n
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨ψ⟩ := CFSG.AGLEmbeddingD2.Wilson.Census424Rest.nonempty_projSL_two_seven_equiv_three_two
    exact olRow_one 7 1 (by norm_num) le_rfl X P L Q hcfg ⟨φ.trans ψ.symm⟩
  · exact olRow_of_E16 _ exists_E16_projSL_three_four X P L Q hcfg ⟨φ⟩
  · norm_num at hc
    have hc' : Nat.card (projSL 3 (GaloisField 2 3)) = 16482816 := by omega
    rw [hc'] at hLN; norm_num at hLN

theorem olRow_six_U3 (n : ℕ) (hn : 1 ≤ n) :
    OLRow (fun T _ => Nonempty (T ≃* projSU 3 2 n)) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hLN := hcfg.card_dvd φ
  have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
  have h3 : (2 ^ n) ^ 3 ∣ Nat.card (projSU 3 2 n) := by
    have h' : (2 ^ n) ^ 3 ∣ Nat.card (projSU 3 2 n) * Nat.gcd 3 (2 ^ n + 1) := by
      rw [hc]; exact dvd_mul_right _ _
    rw [← pow_mul] at h' ⊢
    exact (coprime_pow_of_dvd Nat.prime_two (Nat.gcd_dvd_left 3 _) (by norm_num)).dvd_of_dvd_mul_right h'
  have hn3 := two_pow_dvd_N ((by rw [← pow_mul] at h3; exact h3 : 2 ^ (n * 3) ∣ _).trans hLN)
  have hn3' : n ≤ 3 := by omega
  have hqL := hcfg.isQuasisimple
  interval_cases n
  · have hs : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
    exact Sec4.false_of_isQuasisimple_of_isSolvable hqL
      (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
  · norm_num at hc
    have hc' : Nat.card (projSU 3 2 2) = 62400 := by omega
    rw [hc'] at hLN; norm_num at hLN
  · have hZL := Sec13.Res5Proof.center_eq_bot_of_projSU
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩ hqL φ
    obtain ⟨x, hx⟩ := exists_orderOf_nine_projSU_three_eight
    exact hcfg.false_of_orderOf_nine hZL (φ.symm x) (by rw [MulEquiv.orderOf_eq, hx])

theorem olRow_six_Sp4 (n : ℕ) (hn : 1 ≤ n) :
    OLRow (fun T _ => Nonempty (T ≃* projSp 2 (GaloisField 2 n))) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLN := hcfg.card_dvd φ
  have hc := CFSG.PGLModel.card_projSp_of_charTwo 2 (GaloisField 2 n)
  rw [hK] at hc
  have h4 : 2 ^ (n * 4) ∣ 1382446517760 := by
    have : 2 ^ (n * 4) ∣ Nat.card (projSp 2 (GaloisField 2 n)) := by
      rw [hc]
      apply Dvd.dvd.mul_right
      rw [← pow_mul]
      norm_num
    exact this.trans hLN
  have hn4 := two_pow_dvd_N h4
  have hn4' : n ≤ 2 := by omega
  have hqL := hcfg.isQuasisimple
  interval_cases n
  · exact Sec13.Res5Proof.false_of_projSp_two_two hqL φ
  · rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)] at hc
    norm_num at hc
    rw [hc] at hLN; norm_num at hLN

theorem olRow_six_U4 (n : ℕ) (hn : 1 ≤ n) :
    OLRow (fun T _ => Nonempty (T ≃* projSU 4 2 n)) := by
  intro X _ _ P L Q hcfg ⟨φ⟩
  have hLN := hcfg.card_dvd φ
  have hc := Sec11.KSListsProof.card_projSU_four_mul 2 n hn
  have h6 : (2 ^ n) ^ 6 ∣ Nat.card (projSU 4 2 n) := by
    have h' : (2 ^ n) ^ 6 ∣ Nat.card (projSU 4 2 n) * Nat.gcd 4 (2 ^ n + 1) := by
      rw [hc]; exact dvd_mul_right _ _
    have hodd : Odd (2 ^ n + 1) := by
      have : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact this.add_one
    have hg : Nat.gcd 4 (2 ^ n + 1) = 1 := by
      have h2 : Nat.Coprime 2 (2 ^ n + 1) := Nat.coprime_two_left.mpr hodd
      have : Nat.Coprime (2 ^ 2) (2 ^ n + 1) := Nat.Coprime.pow_left 2 h2
      simpa using this
    rw [hg, mul_one] at h'
    exact h'
  have hn6 := two_pow_dvd_N ((by rw [← pow_mul] at h6; exact h6 : 2 ^ (n * 6) ∣ _).trans hLN)
  obtain rfl : n = 1 := by omega
  exact olRow_of_E16 _ exists_E16_projSU_four_two X P L Q hcfg ⟨φ⟩

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
