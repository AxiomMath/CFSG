module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HA5Rows
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusChar2b

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

theorem a5Row_six_L2 (n : ℕ) (hn : 1 ≤ n) :
    A5Row (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField 2 n))) := by
  intro T _ _ hd ⟨φ⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLN : Nat.card (projSL 2 (GaloisField 2 n)) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
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
  interval_cases n
  · exact Sec13.Res5Proof.false_of_projSL_two_small (Or.inl (by rw [hK]; norm_num)) hd.qs φ
  · exact hd.false_of_iso_card_dvd_sixty φ (by rw [hc]; norm_num)
  · exact hd.false_of_iso_not_five φ (by rw [hc]; norm_num)
  · rw [hc] at hLN; norm_num at hLN
  · exact hd.false_of_iso_not_five φ (by rw [hc]; norm_num)
  all_goals (rw [hc] at hLN; norm_num at hLN)

theorem a5Row_six_L3 (n : ℕ) (hn : 1 ≤ n) :
    A5Row (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 2 n))) := by
  intro T _ _ hd ⟨φ⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLN : Nat.card (projSL 3 (GaloisField 2 n)) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
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
  · norm_num at hc
    exact hd.false_of_iso_not_five φ (by omega)
  · exact hd.false_of_iso_E16 φ exists_E16_projSL_three_four
  · norm_num at hc
    have hc' : Nat.card (projSL 3 (GaloisField 2 3)) = 16482816 := by omega
    rw [hc'] at hLN; norm_num at hLN

theorem a5Row_six_U3 (n : ℕ) (hn : 1 ≤ n) :
    A5Row (fun T _ => Nonempty (T ≃* projSU 3 2 n)) := by
  intro T _ _ hd ⟨φ⟩
  have hLN : Nat.card (projSU 3 2 n) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
  have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
  have h3 : (2 ^ n) ^ 3 ∣ Nat.card (projSU 3 2 n) := by
    have h' : (2 ^ n) ^ 3 ∣ Nat.card (projSU 3 2 n) * Nat.gcd 3 (2 ^ n + 1) := by
      rw [hc]; exact dvd_mul_right _ _
    rw [← pow_mul] at h' ⊢
    exact (coprime_pow_of_dvd Nat.prime_two (Nat.gcd_dvd_left 3 _) (by norm_num)).dvd_of_dvd_mul_right h'
  have hn3 := two_pow_dvd_N ((by rw [← pow_mul] at h3; exact h3 : 2 ^ (n * 3) ∣ _).trans hLN)
  have hn3' : n ≤ 3 := by omega
  interval_cases n
  · have hs : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
    exact Sec4.false_of_isQuasisimple_of_isSolvable hd.qs
      (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
  · norm_num at hc
    have hc' : Nat.card (projSU 3 2 2) = 62400 := by omega
    rw [hc'] at hLN; norm_num at hLN
  · norm_num at hc
    exact hd.false_of_iso_not_five φ (by omega)

theorem a5Row_six_Sp4 (n : ℕ) (hn : 1 ≤ n) :
    A5Row (fun T _ => Nonempty (T ≃* projSp 2 (GaloisField 2 n))) := by
  intro T _ _ hd ⟨φ⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hLN : Nat.card (projSp 2 (GaloisField 2 n)) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
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
  interval_cases n
  · exact Sec13.Res5Proof.false_of_projSp_two_two hd.qs φ
  · rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)] at hc
    norm_num at hc
    rw [hc] at hLN; norm_num at hLN

theorem a5Row_six_U4 (n : ℕ) (hn : 1 ≤ n) :
    A5Row (fun T _ => Nonempty (T ≃* projSU 4 2 n)) := by
  intro T _ _ hd ⟨φ⟩
  have hLN : Nat.card (projSU 4 2 n) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
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
  exact hd.false_of_iso_E16 φ exists_E16_projSU_four_two

section Model


theorem a5Row_six_model : A5Row (fun T _ => IsChevTwoRankTwoModel T) := by
  intro T _ _ hd h
  rcases h with ⟨n, hn, h | h | h | h | h⟩ | ⟨f, h | h | h | h | h⟩
  · exact a5Row_six_L2 n hn T hd h
  · exact a5Row_six_L3 n hn T hd h
  · exact a5Row_six_U3 n hn T hd h
  · exact a5Row_six_Sp4 n hn T hd h
  · exact a5Row_six_U4 n hn T hd h
  · exact a5Row_of_cardRow (cardRow_six_G2 f) T hd h
  · exact a5Row_of_cardRow (cardRow_six_D4 f) T hd h
  · exact a5Row_of_cardRow (cardRow_six_Sz f) T hd h
  · exact a5Row_of_cardRow (cardRow_six_F4 f) T hd h
  · exact a5Row_of_cardRow (cardRow_six_Tits f) T hd h

end Model

theorem a5Row_six_SL3 (n : ℕ) (hn : 1 ≤ n) :
    A5Row (fun T _ => IsSLThreeEpsAt T (2 ^ n)) := by
  intro T _ _ hd ⟨K, _, _, h⟩
  rcases h with ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩
  ·
    have hLN : Nat.card (StatedSL 3 K) ∣ 1382446517760 := by
      rw [← Nat.card_congr φ.toEquiv]
      exact hd.dvd
    have hc := CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 3) (by norm_num)
    rw [hK, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num)] at hc
    have h3 : 2 ^ (n * 3) ∣ 1382446517760 := by
      have : 2 ^ (n * 3) ∣ Nat.card (StatedSL 3 K) := by
        rw [hc, pow_mul]; exact dvd_mul_right _ _
      exact this.trans hLN
    have := two_pow_dvd_N h3
    have hn3 : n ≤ 3 := by omega
    interval_cases n
    · exact hd.false_of_iso_not_five φ (by rw [hc]; norm_num)
    · exact hd.false_of_iso_E16 φ (exists_E16_statedSL_three_four (by rw [hK]; norm_num))
    · rw [hc] at hLN; norm_num at hLN
  ·
    have hLN : Nat.card (StatedSU 3 (2 ^ n) K) ∣ 1382446517760 := by
      rw [← Nat.card_congr φ.toEquiv]
      exact hd.dvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
      ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * n)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq hu (n := 3) (by norm_num)
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)] at hc
    have h3 : 2 ^ (n * 3) ∣ 1382446517760 := by
      have : ((2 ^ (n * 3) : ℕ) : ℤ) ∣ (Nat.card (StatedSU 3 (2 ^ n) K) : ℤ) := by
        rw [hc, pow_mul]; push_cast; exact dvd_mul_right _ _
      exact (Int.natCast_dvd_natCast.mp this).trans hLN
    have := two_pow_dvd_N h3
    have hn3 : n ≤ 3 := by omega
    interval_cases n
    ·
      have h216 : Nat.card (StatedSU 3 (2 ^ 1) K) = 216 := by
        norm_num at hc; exact_mod_cast hc
      have : Fintype (StatedSU 3 (2 ^ 1) K) := Fintype.ofFinite _
      have hs : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, h216]; norm_num)
      exact Sec4.false_of_isQuasisimple_of_isSolvable hd.qs
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · have h62400 : Nat.card (StatedSU 3 (2 ^ 2) K) = 62400 := by
        norm_num at hc; exact_mod_cast hc
      rw [h62400] at hLN; norm_num at hLN
    · have h8 : Nat.card (StatedSU 3 (2 ^ 3) K) = 16547328 := by
        norm_num at hc; exact_mod_cast hc
      exact hd.false_of_iso_not_five φ (by rw [h8]; norm_num)

theorem a5Row_eight_SU3 (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    A5Row (fun T _ => Nonempty (T ≃* projSU 3 3 e)) := by
  interval_cases e
  · intro T _ _ hd ⟨φ⟩
    have hc := KFacts.KS14.card_projSU_three_mul_gcd 3 1 (by norm_num)
    norm_num at hc
    exact hd.false_of_iso_not_five φ (by omega)
  · exact a5Row_of_cardRow cardRow_eight_SU3_nine

section Census

set_option linter.unusedSectionVars false


theorem a5Row_five_spor : ∀ s ∈ sporadics46,
    A5Row (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier s)) := by
  intro s hs
  simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a5Row_spor_M11
  · exact a5Row_spor_M12
  · exact a5Row_spor_M22
  · exact a5Row_of_cardRow cardRow_spor_M23
  · exact a5Row_of_cardRow cardRow_spor_M24
  · exact a5Row_spor_J1
  · exact a5Row_of_cardRow cardRow_spor_J2
  · exact a5Row_of_cardRow cardRow_spor_J3
  · exact a5Row_of_cardRow cardRow_spor_J4
  · exact a5Row_of_cardRow cardRow_spor_McL
  · exact a5Row_of_cardRow cardRow_spor_HS
  · exact a5Row_of_cardRow cardRow_spor_He
  · exact a5Row_of_cardRow cardRow_spor_Ru

theorem a5Row_five_cover : ∀ s ∈ sporadicCovers46,
    A5Row (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) := by
  intro s hs
  simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact a5Row_cover_M22
  · exact a5Row_of_cardRow cardRow_cover_J3
  · exact a5Row_of_cardRow cardRow_cover_McL
  · exact a5Row_cover_ON

theorem a5Rows_holds : A5Rows where
  one := fun p e _ hp2 he => a5Row_one p e hp2 he
  two_eps := fun p e _ hp3 he1 he2 => a5Row_two_eps p e hp3 he1 he2
  two_SL := fun p e _ hp3 he1 he2 => a5Row_two_SL p e hp3 he1 he2
  two_SU := fun p e _ hp3 he1 _ => a5Row_of_cardRow (cardRow_two_SU p e hp3 he1)
  three_G2 := fun p _ hp3 => a5Row_of_cardRow (cardRow_three_G2 p hp3)
  three_Sp := fun p _ hp3 => a5Row_of_cardRow (cardRow_three_Sp p hp3)
  three_SU := fun p _ hp3 _ => a5Row_of_cardRow (cardRow_three_SU p hp3)
  three_SL := fun p _ hp3 _ => a5Row_of_cardRow (cardRow_three_SL p hp3)
  four_alt := a5Row_four_alt
  four_A6 := a5Row_four_A6
  four_A7 := a5Row_four_A7
  five_spor := a5Row_five_spor
  five_cover := a5Row_five_cover
  six_model := a5Row_six_model
  six_SL3 := a5Row_six_SL3
  seven_SL52 := a5Row_of_cardRow cardRow_seven_SL52
  seven_Sp62 := fun T _ _ hd ⟨φ⟩ => hd.false_of_iso_E16 φ exists_E16_projSp_three_two
  seven_SU54 := a5Row_of_cardRow cardRow_seven_SU54
  eight_SL3 := fun e he1 he2 => a5Row_of_cardRow (cardRow_eight_SL3 e he1 he2)
  eight_SU3 := a5Row_eight_SU3
  eight_SL43 := a5Row_of_cardRow cardRow_eight_SL43
  eight_cover := a5Row_of_cardRow cardRow_eight_cover

end Census

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
