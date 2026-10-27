module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusChar2
public import CFSG.CGT.T75O.Orders
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedProj StatedScalars)

section Exc



theorem cardRow_six_G2 (f : ℕ) :
    CardRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .G2 2 f) := by
  intro T _ _ hT hd
  obtain ⟨-, hf1, h⟩ := hT.1
  change 0 = 0 ∧ 3 ≤ 2 ^ f at h
  have hc : Nat.card T = CFSG.Open.ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hT
  obtain ⟨o, -, ho⟩ := CFSG.CGT.T75O.ordG2_two_pow (f := f) (by omega)
  have h6 : 2 ^ (6 * f) ∣ 1382446517760 := by
    rw [hc, ho] at hd; exact (dvd_mul_right _ _).trans hd
  have := two_pow_dvd_N h6
  have hf2 : 2 ≤ f := by
    by_contra hf
    push Not at hf
    interval_cases f <;> norm_num at h
  omega

theorem olRow_six_G2 (f : ℕ) :
    OLRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .G2 2 f) :=
  olRow_of_card _ (cardRow_six_G2 f)

theorem cardRow_six_D4 (f : ℕ) :
    CardRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .trialityD4 2 f) := by
  intro T _ _ hT hd
  have hf1 : 1 ≤ f := hT.1.2.1
  have hc : Nat.card T = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hT
  obtain ⟨o, -, ho⟩ := CFSG.CGT.T75O.ordTrialityD4_two_pow (f := f) (by omega)
  have h12 : 2 ^ (12 * f) ∣ 1382446517760 := by
    rw [hc, ho] at hd; exact (dvd_mul_right _ _).trans hd
  have := two_pow_dvd_N h12
  omega

theorem olRow_six_D4 (f : ℕ) :
    OLRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .trialityD4 2 f) :=
  olRow_of_card _ (cardRow_six_D4 f)

theorem cardRow_six_Sz (f : ℕ) :
    CardRow (fun T _ => Blueprint.SuzukiModel T 2 f) := by
  intro T _ _ hT hd
  obtain ⟨-, a, ha, hf, hc⟩ := CFSG.GH74.card_of_suzukiModel hT
  have h2 : 2 ^ (2 * f) ∣ 1382446517760 := by
    rw [hc, CFSG.Open.ordSuzuki, ← pow_mul, mul_assoc, mul_comm f 2] at hd
    exact (dvd_mul_right _ _).trans hd
  have := two_pow_dvd_N h2
  obtain rfl : a = 1 := by omega
  subst hf
  rw [hc] at hd
  norm_num [CFSG.Open.ordSuzuki] at hd

theorem olRow_six_Sz (f : ℕ) :
    OLRow (fun T _ => Blueprint.SuzukiModel T 2 f) :=
  olRow_of_card _ (cardRow_six_Sz f)

theorem cardRow_six_F4 (f : ℕ) :
    CardRow (fun T _ => Blueprint.ReeTitsModel T .twistedF4 2 f) := by
  intro T _ _ hT hd
  have := (CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_twistedF4 hT).trans hd
  norm_num at this

theorem olRow_six_F4 (f : ℕ) :
    OLRow (fun T _ => Blueprint.ReeTitsModel T .twistedF4 2 f) :=
  olRow_of_card _ (cardRow_six_F4 f)

theorem cardRow_six_Tits (f : ℕ) :
    CardRow (fun T _ => Blueprint.ReeTitsModel T .Tits 2 f) := by
  intro T _ _ hT hd
  have := (CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_Tits hT).trans hd
  norm_num at this

theorem olRow_six_Tits (f : ℕ) :
    OLRow (fun T _ => Blueprint.ReeTitsModel T .Tits 2 f) :=
  olRow_of_card _ (cardRow_six_Tits f)

end Exc

section Row

set_option linter.unusedSectionVars false


noncomputable def statedSLEquivProjSLTwo {K : Type} [Field K] [Finite K] (hK2 : Nat.card K = 2) :
    StatedSL 3 K ≃* projSL 3 (GaloisField 2 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2 (Fin 3), Subgroup.bot_subgroupOf]
  let e1 : StatedSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
  let e2 : StatedProj (StatedSL 3 K) ≃* projSL 3 K := (CFSG.PGLModel.projSLEquivStatedProj 3 K).symm
  let ε : K ≃+* GaloisField 2 1 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 1 Nat.one_pos (by rw [hK2]; norm_num)
  let e3 : projSL 3 K ≃* projSL 3 (GaloisField 2 1) :=
    (Sec4.projSLEquivPSLn 3 K).trans
      ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) ε).trans
        (Sec4.projSLEquivPSLn 3 (GaloisField 2 1)).symm)
  exact (e1.trans e2).trans e3

theorem olRow_six_model :
    OLRow (fun T _ => IsChevTwoRankTwoModel T) := by
  intro X _ _ P L Q hcfg h
  rcases h with ⟨n, hn, h | h | h | h | h⟩ | ⟨f, h | h | h | h | h⟩
  · exact olRow_six_L2 n hn X P L Q hcfg h
  · exact olRow_six_L3 n hn X P L Q hcfg h
  · exact olRow_six_U3 n hn X P L Q hcfg h
  · exact olRow_six_Sp4 n hn X P L Q hcfg h
  · exact olRow_six_U4 n hn X P L Q hcfg h
  · exact olRow_six_G2 f X P L Q hcfg h
  · exact olRow_six_D4 f X P L Q hcfg h
  · exact olRow_six_Sz f X P L Q hcfg h
  · exact olRow_six_F4 f X P L Q hcfg h
  · exact olRow_six_Tits f X P L Q hcfg h

theorem olRow_six_SL3 (n : ℕ) (hn : 1 ≤ n) :
    OLRow (fun T _ => IsSLThreeEpsAt T (2 ^ n)) := by
  intro X _ _ P L Q hcfg ⟨K, _, _, h⟩
  have hqL := hcfg.isQuasisimple
  rcases h with ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩
  ·
    have hLN := hcfg.card_dvd φ
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
    · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨ψ⟩ := CFSG.AGLEmbeddingD2.Wilson.Census424Rest.nonempty_projSL_two_seven_equiv_three_two
      exact olRow_one 7 1 (by norm_num) le_rfl X P L Q hcfg
        ⟨(φ.trans (statedSLEquivProjSLTwo (by rw [hK]; norm_num))).trans ψ.symm⟩
    · exact olRow_of_E16 _ (exists_E16_statedSL_three_four (by rw [hK]; norm_num)) X P L Q hcfg ⟨φ⟩
    · rw [hc] at hLN; norm_num at hLN
  ·
    have hLN := hcfg.card_dvd φ
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
      exact Sec4.false_of_isQuasisimple_of_isSolvable hqL
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · have h62400 : Nat.card (StatedSU 3 (2 ^ 2) K) = 62400 := by
        norm_num at hc; exact_mod_cast hc
      rw [h62400] at hLN; norm_num at hLN
    · obtain ⟨y, hy9, hy3⟩ := exists_cube_noncentral_statedSU_three_eight (K := K) (by rw [hK]; norm_num)
      refine olRow_of_three_noncentral (StatedSU 3 8 K)
        ⟨Subgroup.zpowers y, ?_, Or.inl ⟨y, Subgroup.mem_zpowers y, hy3⟩⟩ X P L Q hcfg ⟨φ⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show orderOf y ∣ 3 ^ 2 from orderOf_dvd_of_pow_eq_one hy9)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
