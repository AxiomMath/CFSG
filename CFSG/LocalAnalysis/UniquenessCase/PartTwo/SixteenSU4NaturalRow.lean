module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenIrreducibleQuotientCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenStarRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1SchurU4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8U42
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
public import CFSG.GroupTheory.E3Params
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import Certificates.Certificate2012
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LargeExtraspecial.S6Seven
public import CFSG.LargeExtraspecial.S6SixB
public import CFSG.LargeExtraspecial.S6SixC
public import CFSG.LargeExtraspecial.S6ThreeD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem isU4_of_isSUn_four_one {X : Type} [Group X] (h : IsSUn X 4 1) : IsU4 X 1 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hKcard
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hSUbot : (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ 1) K) = ⊥ :=
    CFSG.Quasithin.H13.F431.Un.statedScalars_inf_eq_bot (f := 1) hKcard
  have hprojSU : StatedProj (StatedSU 4 (2 ^ 1) K) ≃* ↥(StatedSU 4 (2 ^ 1) K) :=
    (QuotientGroup.quotientMulEquivOfEq hSUbot).trans QuotientGroup.quotientBot
  have hmodeliso : X ≃* StatedProj (StatedSU 4 (2 ^ 1) K) := e.trans hprojSU.symm
  have hclass : StatedClassicalModel X .PSU 4 2 1 :=
    ⟨⟨Nat.prime_two, le_refl 1, by norm_num, hnq⟩, K, inferInstance, inferInstance,
      hKcard, ⟨hmodeliso⟩⟩
  exact (CFSG.Blueprint.LieModel.classical_iff (t := .PSU) (n := 4) (p := 2) (f := 1)
    (by decide)).2 hclass

private theorem s16k_pRank_u42_top {X : Type} [Group X] [Finite X] (h : IsU4 X 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨F, hF, hFcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27 h
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤) le_top hF
    (k := 3) (by rw [hFcard]; norm_num)

private theorem s16k_pRank_aut_u42_le_one
    {X : Type} [Group X] [Finite X] (h : IsU4 X 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  have hcard := (CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 h).1
  refine (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
    (A := MulAut X) hp).trans ?_
  rw [hcard]
  have hfac : (51840 : ℕ).factorization p ≤ 1 := by
    by_cases hp5 : p = 5
    · rw [hp5]
      norm_num [Nat.factorization]
    · have hndvd : ¬ p ∣ 51840 := by
        intro hd
        have hfac5 : (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 := by norm_num
        rw [hfac5] at hd
        rcases hp.dvd_mul.mp hd with h1 | h1
        · rcases hp.dvd_mul.mp h1 with h2 | h2
          · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
          · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
              (hp.dvd_of_dvd_pow h2))
        · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h1)
      rw [Nat.factorization_eq_zero_of_not_dvd hndvd]
      omega
  exact hfac

theorem s15_eq_one_of_su4_component_at_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSU : IsSUn ↥(lBar V₀ V hV L) 4 1) :
    s15 D.M V₀ V hV L = 1 := by
  have hU4 : IsU4 ↥(lBar V₀ V hV L) 1 := isU4_of_isSUn_four_one hSU
  refine s15_eq_one_of_simple_component_of_three_rank (D := D) (V₀ := V₀) (V := V) (hV := hV)
    c hcomp (CFSG.Quasithin.H13.F431.U42.isSimpleGroup_of_lieModel_PSU_four_two hU4)
    (r := 3) (by norm_num) (s16k_pRank_u42_top hU4) ?_
  intro Q _ _ hq he
  obtain ⟨e⟩ := he
  have hU4Q : IsU4 (Q ⧸ Subgroup.center Q) 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm hU4
  have hdvd : Nat.card (Subgroup.center Q) ∣ 2 := rSchurOm6_holds Q hq hU4Q
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [h1]; norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [h1]; norm_num)

theorem case162_6_of_su4_natural
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSU : IsSUn ↥(lBar V₀ V hV L) 4 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hNat : NatSUn (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 4 1) :
    Case162_6 D V₀ V hV L := by
  classical
  have hU4 : IsU4 ↥(lBar V₀ V hV L) 1 := isU4_of_isSUn_four_one hSU
  have hs : s15 D.M V₀ V hV L = 1 := s15_eq_one_of_su4_component_at_three c hcomp hSU
  obtain ⟨K, hKfield, hKfinite, hKcard, hR⟩ := hNat
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hstar : S16kStar D V₀ V L hV := c.toS16kStar hs
  have hreal : (FFModel.nat (StatedSU 4 (2 ^ 1) K)).Realizes
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ :=
    hstar.realizes_map hR
  have hNatStar : NatSUn (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 4 1 :=
    ⟨K, hKfield, hKfinite, hKcard, hreal⟩
  have hwcard : Nat.card ↥(wStar D.M V₀ V hV L) = 2 ^ 8 := by
    have hc := s16c1610_card_of_realizes_nat (V := vStar D.M V₀ V hV L)
      (Γ := StatedSU 4 (2 ^ 1) K) (H := lStar D.M V₀ V hV L)
      (U := wStar D.M V₀ V hV L) hreal
    rw [Fintype.card_fin, hKcard] at hc
    norm_num at hc ⊢
    exact hc
  have hgamma : gamma15 D.M V₀ V hV L = 8 := by
    unfold gamma15
    exact s16c1610_rk_of_card_two_pow hwcard
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hdimtop : E3.mQuot (⊤ : Subgroup (Vtil V₀ V hV))
      (fixV (lBar V₀ V hV L)) = 8 := by
    have h := hstar.gamma15_eq_mQuot
    rw [hgamma, hcomm, top_inf_eq] at h
    exact h.symm
  have hAnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have hord : 5 ≤ (Nat.card ↥(lBar V₀ V hV L)).factorization 2 := by
      rw [(CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 hU4).2]
      norm_num [Nat.factorization]
    have hmain := pRank_le_of_normalizes_irreducible_quotient_rank_eight
      (W := Vtil V₀ V hV) (H := lBar V₀ V hV L) (A := Mbar D.M V₀ V hV)
      (s15_Infra_vtil_sq_eq_one V₀ V hV) hcomp.2.2 hcomm hirr hdimtop hord hAnorm hq hq3
    have haut := s16k_pRank_aut_u42_le_one hU4 hq hq2 hq3
    omega
  refine ⟨hSU, hNatStar, hs, hsig, ?_⟩
  exact c.std.pRank_eq_three (p := 3) (by rw [hsig]; exact Set.mem_singleton 3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
