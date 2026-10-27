module

public import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofU54
import CFSG.RankThree.PartTwo.Sec21.Item222ProofBar
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4
import CFSG.Sporadic.J3
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

variable {G : Type} [Group G]

namespace Item221Proof

theorem table_PSU_five_four :
    (Blueprint.Multiplier.genericOrders .PSU 5 2 2).1 *
        (Blueprint.Multiplier.genericOrders .PSU 5 2 2).2 *
        ((Blueprint.Multiplier.exceptionalOrders .PSU 5 2 2).1 *
          (Blueprint.Multiplier.exceptionalOrders .PSU 5 2 2).2) = 5 := by
  rw [KFacts.KS21Mult.exceptionalOrders_PSU_five]
  change Nat.gcd 5 (2 ^ 2 + 1) * 1 * (1 * 1) = 5
  norm_num

theorem nonempty_mulEquiv_projSU_five [Finite G]
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hU5 : SU54LocalRankFive) (hG : TheoremFourHyp G) {L : Subgroup G} (hq : IsQuasisimple L)
    (e : lBar L ≃* projSU 5 2 2) : Nonempty (L ≃* projSU 5 2 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (projSU 5 2 2) := isSimpleGroup_projSU (by norm_num) (by norm_num)
  refine nonempty_mulEquiv_of_center_eq_bot hq e fun e' => ?_
  have hadm : StatedLieAdmissible .PSU 5 2 2 := by
    refine ⟨Nat.prime_two, by norm_num, ?_⟩
    change 3 ≤ 5 ∧ (5, 2 ^ 2) ≠ (3, 2)
    exact ⟨by norm_num, by simp⟩
  have hdvd := card_center_dvd_table hGA hq.1 e' (KFacts.KS21Mult.lieModel_projSU hadm)
  rw [table_PSU_five_four] at hdvd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have h3 := hU5 L hq.1 h5 ⟨e'⟩
    have hle := localRank_subgroup_le (by norm_num : Nat.Prime 5) L
    have hlt := hG.localRank_lt 5 (by norm_num) (by norm_num)
    omega

theorem genericOrders_PSp_two {n : ℕ} (hn : 1 ≤ n) :
    Blueprint.Multiplier.genericOrders .PSp 2 2 n = (1, 1) := by
  change (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
  have hodd : Odd (2 ^ n - 1) := KFacts.KS21Mult.odd_two_pow_sub_one hn
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)]

theorem exceptionalOrders_PSp_two (n : ℕ) :
    Blueprint.Multiplier.exceptionalOrders .PSp 2 2 n = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem nonempty_mulEquiv_projSp_two [Finite G]
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {L : Subgroup G}
    (hq : IsQuasisimple L) {n : ℕ} (hn : 2 ≤ n) (e : lBar L ≃* projSp 2 (GaloisField 2 n)) :
    Nonempty (L ≃* projSp 2 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (projSp 2 (GaloisField 2 n)) := isSimpleGroup_projSp_two hn
  have hadm : StatedLieAdmissible .PSp 2 2 n := by
    refine ⟨Nat.prime_two, by omega, ?_⟩
    change 2 ≤ 2 ∧ (2, 2 ^ n) ≠ (2, 2)
    refine ⟨le_rfl, fun h => ?_⟩
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using (Prod.mk.inj h).2
    have := Nat.pow_right_injective le_rfl h2
    omega
  exact nonempty_mulEquiv_of_table hGA hq e (KFacts.KS21Mult.lieModel_projSp hadm)
    (genericOrders_PSp_two (by omega)) (exceptionalOrders_PSp_two n)

theorem exceptional_PSL_three_dvd (n : ℕ) :
    (Blueprint.Multiplier.exceptionalOrders .PSL 3 2 n).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSL 3 2 n).2 ∣ 16 := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_PSL_three {n : ℕ} (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Blueprint.Multiplier.exceptionalOrders .PSL 3 2 n = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

noncomputable def quotientCenterEquivProjSL [Finite G] {L : Subgroup G} (hq : IsQuasisimple L)
    {n : ℕ} (e : lBar L ≃* SL3 n) : L ⧸ Subgroup.center L ≃* projSL 3 (GaloisField 2 n) :=
  (quotientCenterEquiv hq).trans
    ((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (Sec4.projSLEquivPSLn 3 (GaloisField 2 n)).symm)

theorem sl3_cases [Finite G]
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {L : Subgroup G}
    (hq : IsQuasisimple L) {n : ℕ} (hn : 0 < n) (he : Even n) (e : lBar L ≃* SL3 n) :
    Nonempty (L ≃* SL3 n) ∨
      (n = 2 ∧ IsPGroup 2 (aschbacherSolvableCore 3 L) ∧ aschbacherSolvableCore 3 L ≠ ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  have hadm : StatedLieAdmissible .PSL 3 2 n := by
    refine ⟨Nat.prime_two, by omega, ?_⟩
    change 2 ≤ 3 ∧ (3, 2 ^ n) ≠ (2, 2) ∧ (3, 2 ^ n) ≠ (2, 3)
    exact ⟨by norm_num, by simp, by simp⟩
  have hdvd := card_center_dvd_table hGA hq.1 (quotientCenterEquivProjSL hq e)
    (KFacts.KS21Mult.lieModel_projSL hadm)
  have hg : Blueprint.Multiplier.genericOrders .PSL 3 2 n = (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
  rw [hg] at hdvd
  have hTZ : Nat.card T ∣ Nat.card (Subgroup.center L) :=
    Subgroup.card_dvd_of_le (theta_le_center hq)
  have hcop : Nat.Coprime (Nat.card T) 3 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3))
  have hg3 : Nat.gcd 3 (2 ^ n - 1) * 1 ∣ 3 := by
    rw [mul_one]
    exact Nat.gcd_dvd_left _ _
  have h16 : Nat.card T ∣ 16 := by
    have h48 : Nat.card T ∣ 3 * 16 :=
      hTZ.trans (hdvd.trans (Nat.mul_dvd_mul hg3 (exceptional_PSL_three_dvd n)))
    exact hcop.dvd_of_dvd_mul_left h48
  by_cases hT1 : T = ⊥
  · left
    exact ⟨(mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot hT1)).trans e⟩
  · right
    have hn2 : n = 2 := by
      by_contra hn2
      have hn1 : n ≠ 1 := by
        rintro rfl
        exact (Nat.not_even_one) he
      rw [exceptionalOrders_PSL_three hn1 hn2] at hdvd
      have h3 : Nat.card T ∣ 3 * 1 := by
        have h' : Nat.gcd 3 (2 ^ n - 1) * 1 * (1 * 1) ∣ 3 * 1 := by simpa using hg3
        exact hTZ.trans (hdvd.trans h')
      have h1 : Nat.card T ∣ 1 := hcop.dvd_of_dvd_mul_left h3
      exact hT1 (Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h1))
    refine ⟨hn2, ?_, hT1⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card T ∣ 2 ^ 4 by simpa using h16)
    exact IsPGroup.of_card hk

theorem false_of_J3 [Finite G] (h217 : Item217)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hq : IsQuasisimple L)
    (h : Nonempty (lBar L ≃* Blueprint.NativeSporadic.J3) ∨
      Sec4.IsTripleCover (lBar L) Blueprint.NativeSporadic.J3) : False := by
  have hJ : (L ⧸ Subgroup.center L ≃* Blueprint.NativeSporadic.J3) → False :=
    fun e => (h217 G A E U c L hpair).false e
  rcases h with he | ⟨-, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (lBar L) :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 e
    exact hJ ((quotientCenterEquiv hq).trans
      ((QuotientGroup.quotientMulEquivOfEq (center_lBar_eq_bot hq)).trans
        (QuotientGroup.quotientBot.trans e)))
  · exact hJ ((quotientCenterEquiv hq).trans e)

theorem item221_three
    [Finite G] (h211 : Item211)
    (h2131One : Item2131One) (h2131 : Item2131Two) (h214 : Item214)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSL : Item221SL34) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hq : IsQuasisimple L) (hA : Nat.card A = 3 ^ 3) :
    (∃ n : ℕ, 0 < n ∧ Even n ∧ (Nonempty (L ≃* projSp 2 (GaloisField 2 n)) ∨
        Nonempty (L ≃* projSU 4 2 n) ∨ Nonempty (L ≃* SL3 n))) ∨
      Nonempty (L ≃* projSU 5 2 2) ∨
      (Nonempty (lBar L ≃* SL3 2) ∧ ∀ a ∈ A, a ∉ Subgroup.zpowers c →
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≠ ⊥ →
        Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≃*
          projSL 2 (GaloisField 2 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h2131 G A E U c L hpair hA with ⟨n, hn, he, he' | he' | he'⟩ | he'
  · obtain ⟨e⟩ := he'
    have hn2 : 2 ≤ n := by
      obtain ⟨k, rfl⟩ := he
      omega
    exact Or.inl ⟨n, hn, he, Or.inl (nonempty_mulEquiv_projSp_two hGA hq hn2 e)⟩
  · obtain ⟨e⟩ := he'
    have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl hn
    have hn2 : 2 ≤ n := by
      obtain ⟨k, rfl⟩ := he
      omega
    exact Or.inl ⟨n, hn, he, Or.inr (Or.inl (nonempty_mulEquiv_of_center_eq_bot hq e fun e' =>
      Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hq.1 hn2 e'))⟩
  · obtain ⟨e⟩ := he'
    rcases sl3_cases hGA hq hn he e with h | ⟨rfl, hT2, hT1⟩
    · exact Or.inl ⟨n, hn, he, Or.inr (Or.inr h)⟩
    · obtain ⟨-, hC, -⟩ :=
        Item222Proof.star_SL3_three_bar h211 h2131One hpair hA (by norm_num) even_two e
      refine Or.inr (Or.inr ⟨⟨e⟩, hSL G A E U c L hpair hA hq ⟨e⟩ hC hT2 ?_⟩)
      refine (h214 G A E U c L hpair).mpr ?_
      rintro ⟨k, hk, ⟨eU⟩⟩
      have : IsSimpleGroup (projSU 4 2 k) := isSimpleGroup_projSU le_rfl (by
        obtain ⟨j, rfl⟩ := hk
        omega)
      exact hT1 ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
        (inSubgroup_theta_eq_bot_of_mulEquiv hq.1 eU))
  · obtain ⟨e⟩ := he'
    exact Or.inr (Or.inl
      (nonempty_mulEquiv_projSU_five hGA su54LocalRankFive hpair.standing.toTheoremFourHyp hq e))

end Item221Proof

open Item221Proof

theorem item221_of
    (h211 : Item211) (h2131One : Item2131One) (h2131 : Item2131Two) (h2116 : Item2116)
    (h213 : Item213) (h217 : Item217) (h214 : Item214)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSL : Item221SL34) : Item221 := by
  intro G _ _ A E U c L hpair
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := h213 G A E U c L hpair
  have h3 := fun hA => item221_three h211 h2131One h2131 h214 hGA hSL hpair hq hA
  rcases h211 G A E U c L hpair with ⟨-, -, hA, -⟩ | ⟨-, hA, -⟩ | ⟨-, hA, -⟩ | ⟨-, hA, -⟩ |
      ⟨-, hA, -⟩ | ⟨-, hA, -⟩ | ⟨-, hA, -⟩ | ⟨-, hA, -⟩ | ⟨-, hA, -⟩ |
      ⟨⟨n, hn, hno, ⟨e⟩⟩, hA, -⟩ | ⟨hJ, -, -⟩ | ⟨-, hA, -⟩ | ⟨hSp, -, -⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  · exact Or.inr ⟨hA, h3 hA⟩
  ·
    have : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl (by omega)
    exact Or.inl ⟨hA, n, hn, hno, nonempty_mulEquiv_of_center_eq_bot hq e fun e' =>
      Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hq.1 (by omega) e'⟩
  ·
    exact (false_of_J3 h217 hpair hq hJ).elim
  · exact Or.inr ⟨hA, h3 hA⟩
  ·
    exact (h2116 G A E U c L hpair (Or.inr (Or.inr hSp))).elim

end CFSG.RankThree.PartTwo.Sec21
