module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20w
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

local notation "pRank" => CFSG.Open.pRank
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Certified


theorem pRank_le_one_of_rootLineShape_of_not_dvd (hT : LieOddRankChev) {K : Type}
    [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hZ : center K = ⊥) {n p : ℕ} (hn : 2 ≤ n)
    (hshape : IsU4 K n ∨ IsSp4 K n ∨ IsG2 K n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : ¬ p ∣ 2 ^ n - 1) (hpl : ¬ p ∣ 2 ^ n + 1) : pRank p (⊤ : Subgroup K) ≤ 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : ¬ p ∣ (2 ^ n) ^ 2 - 1 := by
    intro hd
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hfac] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hpl h
    · exact hm h
  have hQne : ((2 ^ n : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 ^ n := (ZMod.natCast_eq_zero_iff (2 ^ n) p).mp hzero
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have heMpos : 0 < CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p := by
    unfold CFSG.LocalAnalysis.RankThreeUC.S15.eM
    exact Nat.pos_of_dvd_of_pos
      (ZMod.orderOf_dvd_card_sub_one (neg_ne_zero.mpr hQne))
      (Nat.sub_pos_of_lt hp.one_lt)
  have heSpos : 0 < CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p := by
    unfold CFSG.LocalAnalysis.RankThreeUC.S15.eS
    exact Nat.pos_of_dvd_of_pos
      (ZMod.orderOf_dvd_card_sub_one (pow_ne_zero 2 hQne))
      (Nat.sub_pos_of_lt hp.one_lt)
  have heS1 : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p ≠ 1 := by
    intro h
    exact hsq ((eS_eq_one_iff (Nat.one_le_pow n 2 (by norm_num) : 1 ≤ 2 ^ n)).mp h)
  have heM1 : CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p ≠ 1 := by
    intro h
    exact hpl (eM_eq_one_iff.mp h)
  have heM2 : CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p ≠ 2 := by
    intro h
    have hord : orderOf (-((2 ^ n : ℕ) : ZMod p)) = 2 := by
      unfold CFSG.LocalAnalysis.RankThreeUC.S15.eM at h
      exact h
    have hpow : (-((2 ^ n : ℕ) : ZMod p)) ^ 2 = 1 := by
      conv_lhs =>
        arg 2
        rw [← hord]
      exact pow_orderOf_eq_one (-((2 ^ n : ℕ) : ZMod p))
    have hcast : (((2 ^ n : ℕ) : ZMod p)) ^ 2 = 1 := by
      have hneg : (-((2 ^ n : ℕ) : ZMod p)) ^ 2 = (((2 ^ n : ℕ) : ZMod p)) ^ 2 := by ring
      rwa [hneg] at hpow
    have hdvd : p ∣ (2 ^ n) ^ 2 - 1 := by
      refine (ZMod.natCast_eq_zero_iff ((2 ^ n : ℕ) ^ 2 - 1) p).mp ?_
      have h1 : 1 ≤ (2 ^ n : ℕ) ^ 2 := Nat.one_le_pow 2 (2 ^ n) (by positivity)
      rw [Nat.cast_sub h1, Nat.cast_pow]
      rw [hcast]
      ring
    exact hsq hdvd
  have heM3 : 3 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p := by omega
  have heS2 : 2 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p := by omega
  rcases hshape with hU4 | hSp4 | hG2
  · have hS : StatedClassicalModel (K ⧸ center K) .PSU 4 2 n :=
      (LieModel.classical_iff (by decide)).mp (LieModel.quotient_center hZ hU4)
    have hrank := uc22p20w_pRank_psu hT hq hS hp hp2
    have hval : rkLin 4 false (2 ^ n) p (Nat.card (center K)) =
        4 / CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p := by
      unfold rkLin
      simp [heM1]
    rw [hrank, hval]
    by_cases h4 : 4 < CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p
    · rw [Nat.div_eq_of_lt h4]
      omega
    · have he : CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p = 3 ∨
          CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p = 4 := by omega
      rcases he with h | h <;> rw [h] <;> norm_num
  · have hS : StatedClassicalModel (K ⧸ center K) .PSp 2 2 n :=
      (LieModel.classical_iff (by decide)).mp (LieModel.quotient_center hZ hSp4)
    have hrank := uc22p20w_pRank_psp hT hq hS hp hp2
    rw [hrank]
    unfold rkSp
    by_cases h2 : 2 < CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p
    · rw [Nat.div_eq_of_lt h2]
      omega
    · have he : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p = 2 := by omega
      rw [he]
  · have hG2' : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ center K) .G2 2 n :=
      ((LieModel.chevalleyExceptional_iff (by decide)).mp
        (LieModel.quotient_center hZ hG2)).2
    have hrank := uc22p20w_pRank_g2 hT hq hn hG2' hp hp2
    rw [hrank]
    unfold rkG2
    simp only [heS1, if_false]
    split_ifs <;> omega

theorem pRank_of_dvd_add_one (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hZ : center K = ⊥) {n p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ∣ 2 ^ n + 1) :
    (IsSp4 K n ∨ IsG2 K n → pRank p (⊤ : Subgroup K) = 2) ∧
      (IsU4 K n → pRank p (⊤ : Subgroup K) = 3) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2dvd : p ∣ (2 ^ n) ^ 2 - 1 := by
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hfac]
    exact dvd_mul_of_dvd_left hpl _
  have hES1 : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p = 1 :=
    (eS_eq_one_iff (Nat.one_le_pow n 2 (by norm_num) : 1 ≤ 2 ^ n)).mpr hQ2dvd
  have hEM1 : CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) p = 1 := eM_eq_one_iff.mpr hpl
  have hp4 : ¬ p ∣ 4 := by
    intro h
    have h2 : p ∣ 2 := by
      have hmul : p ∣ 2 * 2 := by simpa using h
      rcases (Nat.Prime.dvd_mul hp).mp hmul with h' | h' <;> exact h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  refine ⟨?_, ?_⟩
  · intro hsp
    rcases hsp with hSp4 | hG2
    · have hS : StatedClassicalModel (K ⧸ center K) .PSp 2 2 n :=
        (LieModel.classical_iff (by decide)).mp (LieModel.quotient_center hZ hSp4)
      have hrank := uc22p20w_pRank_psp hT hq hS hp hp2
      rw [hrank, uc22p20v_rkSp_of_eS hES1]
    · have hG2' : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ center K) .G2 2 n :=
        ((LieModel.chevalleyExceptional_iff (by decide)).mp
          (LieModel.quotient_center hZ hG2)).2
      have hrank := uc22p20w_pRank_g2 hT hq hn hG2' hp hp2
      rw [hrank, uc22p20v_rkG2_of_eS hES1]
  · intro hU4
    have hS : StatedClassicalModel (K ⧸ center K) .PSU 4 2 n :=
      (LieModel.classical_iff (by decide)).mp (LieModel.quotient_center hZ hU4)
    have hrank := uc22p20w_pRank_psu hT hq hS hp hp2
    have hval : rkLin 4 false (2 ^ n) p (Nat.card (center K)) = 3 := by
      rw [uc22p20v_rkLin_false_one_of_not_dvd hEM1 hp4]
    rw [hrank, hval]

end Certified

theorem Ctx17_42.not_dvd_two_pow_sub_one {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h51 : R17_51At D V₀ V) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) :
    ¬ p ∣ 2 ^ n - 1 := by
  intro hdvd
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.mem_calC
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns ctx.p_mem
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf p C
  exact h51 L X p n l C Dc Gamma ctx p hp hdvd R hR
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le_of_le hsp hp
      hR.isPGroup (hR.le.trans (ctx.cartan.1.trans
        (CFSG.Open.IsSubnormal.le ctx.mem_calC.1))))

theorem Ctx17_42.false_of_two_le_pRank_inf_centralizer {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h51 : R17_51At D V₀ V) (h76 : F07.R76 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {r : ℕ} {R : Subgroup G}
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hRr : 2 ≤ pRank r R) (hrank : 2 ≤ pRank p (D.M ⊓ centralizer (R : Set G))) : False := by
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.mem_calC
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns ctx.p_mem
  have hRM : R ≤ D.M :=
    hR.le.trans (ctx.cartan.1.trans (CFSG.Open.IsSubnormal.le ctx.mem_calC.1))
  have hGamma : rankThreeGamma 1 r R ≤ D.M :=
    rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp (h76 p hp hp2 hsp) hRM
      hR.isPGroup hRr hrank
  exact h51 L X p n l C Dc Gamma ctx r hr hrdvd R hR hGamma

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
