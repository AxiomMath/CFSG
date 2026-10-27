module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest14
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YConfig
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Strong
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree
    BadNoStrongThree)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedCharY (M L : Subgroup G) : Prop :=
  ∃ p : ℕ, p ≠ 2 ∧ (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) ∧
    3 ≤ CFSG.Open.pRank p M

private theorem false_of_centralizesBar_of_charY (hGA : GriessAllModelsStatement)
    (hK35w : UCK.K35w) (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable)
    (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXor : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L)))
    (hout : ¬ p ∣ Nat.card (Outer (BarInf L)))
    (h3600 : 3600 < Nat.card (BarInf L))
    (h2Bar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)))
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1)
    {a : G} (ha : a ∈ c.B) (hpr : (orderOf a).Prime)
    (hodd : Odd (orderOf a)) (haL : CentralizesBar a L)
    (hN : ∀ q ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank q (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hpL : 2 ≤ CFSG.Open.pRank p L := by
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact h2Bar
  have hpσ : p ∉ uniqueFourSigma S.M := fun hσp => by
    have h1 := uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL hp hp2 (hN p hσp)
    omega
  have hM3 : CFSG.Open.pRank p S.M ≤ 3 := by
    by_contra h4
    exact hpσ (UC6.four_le_pRank_imp_mem_sigma hU S.maxLocal hp hp2 (by omega))
  have hMN : S.M ≤ normalizer (L : Set G) :=
    uc22s213_le_normalizer_of_not_mem_sigma hU S.maxLocal hL hp hp2 hpL hZ hpσ
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p S.M
  have hQ : IsSylowOf p (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  have hQr : CFSG.Open.pRank p (P ⊓ L) = CFSG.Open.pRank p L :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hp hQ
  have hQ2 : 2 ≤ CFSG.Open.pRank p (P ⊓ L) := hQr ▸ hpL
  have hpp : S.p.Prime := S.hp.1.1
  have hp2S : S.p ≠ 2 := S.hp.1.2.1
  haveI : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p := by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact PartOne.Section7.c76Three_of_inputs hSE hK3 hB hS hU S hσ h3 S.p S.hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 S.hp hsp
  obtain ⟨Bp, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hpS1 : CFSG.Open.pRank S.p L ≤ 1 :=
    uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL S.hp.1.1 S.hp.1.2.1 (hN S.p S.hp)
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2S
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2S hpS1)
    hBM (hBM.trans hMN) hBel hBc hp hp2 inf_le_right hQ.isPGroup
  have hΓ : CFSG.Open.rankThreeGamma 1 p (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQ2 hF
  have hspr : IsStronglyPEmbedded p S.M :=
    PartOne.Section8.isStronglyPEmbedded_of_eight73Y_lieModel hGA hK35w hKZ
      (UC6.r6_3_dataOfSetup4 hS hU S hPart.1) hp2 hL hXor hM3 hQ hΓ
  by_cases hp3 : p = 3
  ·
    subst hp3
    have h1 := hk1 hspr
    omega
  ·
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hpB : p ∣ Nat.card (BarInf L) := by
      have h1 := CFSG.GroupTheory.dvd_card_of_one_le_pRank hp
        (H := (⊤ : Subgroup (BarInf L))) (by omega)
      rwa [Subgroup.card_top] at h1
    exact uc22s213_not_centralizesBar_of_strong hS hU S hσ hPart hSE hSS hB Ch hH c hL hp hp5
      hspr hpL hpB h3600 ha hpr haL

theorem uc22s213_not_centralizesBar_of_charY (hGA : GriessAllModelsStatement)
    (hK35w : UCK.K35w) (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable)
    (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hT : S21_3ClosedCharY S.M L)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  obtain ⟨p, hp2, hXor, -⟩ := hT
  rcases hXor with hX | hX
  ·
    obtain ⟨hp, -, -⟩ := hX.admissible
    have h2Bar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
      rcases hr with ⟨-, ⟨h, -⟩ | ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · omega
      · omega
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · omega
    have hZ := uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inl rfl) hp2 hX
    have hout : ¬ p ∣ Nat.card (Outer (BarInf L)) := fun hd =>
      PartOne.Section8.not_dvd_two_mul_gcd_three_sub_one hp hp2 (hd.trans hX.card_outer_psl3_dvd)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h3600 : 3600 < Nat.card (BarInf L) :=
      hX.three_thousand_six_hundred_lt_card_psl3 (by rw [pow_one]; exact hp3)
    exact false_of_centralizesBar_of_charY hGA hK35w hKZ hS hU S hσ hPart hSE hSS hK3 hB hOut Ch
      hH c hL hp hp2 (Or.inl hX) hZ hout h3600 h2Bar hk1 ha hpr hodd haL hN
  ·
    obtain ⟨hp, -, -⟩ := hX.admissible
    have h2Bar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
      rcases hr with ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · omega
      · omega
      · exact absurd h (by decide)
      · omega
    have hZ := uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 hX
    have hout : ¬ p ∣ Nat.card (Outer (BarInf L)) := by
      rw [hX.card_outer_psu3]
      exact PartOne.Section8.not_dvd_two_mul_gcd_three_add_one hp hp2
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h3600 : 3600 < Nat.card (BarInf L) :=
      hX.three_thousand_six_hundred_lt_card_psu3 (by rw [pow_one]; exact hp3)
    exact false_of_centralizesBar_of_charY hGA hK35w hKZ hS hU S hσ hPart hSE hSS hK3 hB hOut Ch
      hH c hL hp hp2 (Or.inr hX) hZ hout h3600 h2Bar hk1 ha hpr hodd haL hN

@[expose] def S21_3Rest15 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ S21_3ClosedCharY D.M L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest14_of_rest15 (hGA : GriessAllModelsStatement) (hK35w : UCK.K35w)
    (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree)
    (hB : BadNoStrongThree) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (Ch : Choice2011 G) (h : S21_3Rest15 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest14 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs hlist hnn hU3 hTL hT4 hCh hU54 hthin h3 hk1 a ha
    hpr hN
  by_cases hY : S21_3ClosedCharY S.M L
  · exact uc22s213_not_centralizesBar_of_charY hGA hK35w hKZ hS hU S hσ hPart hSE hSS hK3 hB
      hOut Ch hH c hL hY hk1 ha hpr hN
  · exact h hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs hlist hnn hU3 hTL hT4 hCh hU54 hY hthin h3
      hk1 a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
