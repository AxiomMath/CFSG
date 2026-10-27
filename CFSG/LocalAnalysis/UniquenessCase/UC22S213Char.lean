module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Strong
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeSylow
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Torus4
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63General
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.Adapters.LieModelL4U4Sp4Torus
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

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

theorem uc22s213_inf_centralizerBar_eq_bot_of_prime {P Q L : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hQL : Q ≤ L) (hQr : IsPGroup r Q) (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) :
    Q ⊓ PartOne.Section8.centralizerBar P L = ⊥ := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 hr2 _ _ hQr (UC6S846.isPGroup_pCoreOf L)).eq_bot
  rw [eq_bot_iff]
  rintro z ⟨hzQ, hzC⟩
  have hcen : (QuotientGroup.mk (⟨z, hQL hzQ⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) :=
    CFSG.SectionRank.Ccomm.mk_mem_center_iff.mpr fun y =>
      (CFSG.mem_openPCoreOf_iff _).mp (hzC.2 y y.2)
  obtain ⟨k, hk⟩ := hQr ⟨z, hzQ⟩
  have hdvdr : orderOf (QuotientGroup.mk (⟨z, hQL hzQ⟩ : ↥L) : Bar2 L) ∣ r ^ k := by
    refine (orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) _).trans ?_
    have h := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at h ⊢
  have hcop : Nat.Coprime (r ^ k) (Nat.card (center (Bar2 L))) :=
    ((Nat.Prime.coprime_iff_not_dvd hr).2 hZ).pow_left k
  have h1 : orderOf (QuotientGroup.mk (⟨z, hQL hzQ⟩ : ↥L) : Bar2 L) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvdr (Subgroup.orderOf_dvd_natCard _ hcen)
  have hzO : z ∈ CFSG.Open.pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff (⟨z, hQL hzQ⟩ : ↥L)).mpr
      ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1))
  have hmem : z ∈ Q ⊓ CFSG.Open.pCoreOf 2 L := ⟨hzQ, hzO⟩
  rwa [hQO2] at hmem

theorem uc22s213_strong_of_pRank_le (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB : BadNoStrongThree) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    {L : Subgroup G} (hL : L ∈ calC S.M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) (hout : ¬ r ∣ Nat.card (Outer (BarInf L)))
    (h2 : 2 ≤ CFSG.Open.pRank r L) (hmr : CFSG.Open.pRank r S.M ≤ CFSG.Open.pRank r L)
    (hrσ : r ∉ uniqueFourSigma S.M) (hp : CFSG.Open.pRank S.p L ≤ 1) :
    IsStronglyPEmbedded r S.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hMN : S.M ≤ normalizer (L : Set G) :=
    uc22s213_le_normalizer_of_not_mem_sigma hU S.maxLocal hL hr hr2 h2 hZ hrσ
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf r S.M
  have hPN : P ≤ normalizer (L : Set G) := hP.le.trans hMN
  have hQ : IsSylowOf r (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  have hQr : CFSG.Open.pRank r (P ⊓ L) = CFSG.Open.pRank r L :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hr hQ
  obtain ⟨E, hEQ, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt (P ⊓ L)
  have hPQ : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hPN).trans inf_normalizer_le_normalizer_inf
  have hout2 := uc22s213_not_dvd_card_outer_bar2 hL.2.2 hout
  have hdec : P ≤ P ⊓ L ⊔ PartOne.Section8.centralizerBar P L :=
    PartOne.Section8.le_sup_centralizerBar_of_inner_prime inf_le_left inf_le_right rfl
      (normal_subgroupOf_of_le_normalizer hPQ) hQ hP.isPGroup hPN le_rfl fun y hy =>
        PartOne.Section8.exists_conj_of_not_dvd_outer y (hPN hy)
          (hP.isPGroup.to_le (zpowers_le.mpr hy)) hout2
  have hQO2 : P ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 hr2 _ _ hQ.isPGroup (UC6S846.isPGroup_pCoreOf L)).eq_bot
  have hcomm : ∀ q ∈ P ⊓ L, ∀ c ∈ PartOne.Section8.centralizerBar P L, q * c = c * q := by
    intro q hq c hc
    have h := commutator_mem_commutator hq hc
    rwa [PartOne.Section8.commutator_eq_bot_centralizerBar inf_le_right hQO2 hPQ, mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h
  have hmeet := uc22s213_inf_centralizerBar_eq_bot_of_prime (P := P) hr hr2 inf_le_right
    hQ.isPGroup hZ
  have hC1 : PartOne.Section8.centralizerBar P L = ⊥ := by
    by_contra hne
    have hCP : PartOne.Section8.centralizerBar P L ≤ P := PartOne.Section8.centralizerBar_le P L
    have hrC : r ∣ Nat.card (PartOne.Section8.centralizerBar P L) :=
      (hP.isPGroup.to_le hCP).card_eq_or_dvd.resolve_left fun h => hne (card_eq_one.mp h)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(PartOne.Section8.centralizerBar P L))
      r hrC
    have hco : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc]
    have hcQ : (c : G) ∉ P ⊓ L := fun h => by
      have hc1 : (c : G) ∈ P ⊓ L ⊓ PartOne.Section8.centralizerBar P L := ⟨h, c.2⟩
      rw [hmeet, mem_bot] at hc1
      rw [hc1, orderOf_one] at hco
      exact hr.one_lt.ne hco
    have hcE : (c : G) ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      exact fun e he => hcomm e (hEQ he) c c.2
    have hsucc := CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer hr hEel
      hEc (hco ▸ pow_orderOf_eq_one (c : G)) (fun h => hcQ (hEQ h)) hcE
      (hEQ.trans (inf_le_left.trans hP.le)) (hP.le (hCP c.2))
    omega
  have hPL : P ⊓ L = P :=
    le_antisymm inf_le_left (by simpa only [hC1, sup_bot_eq] using hdec)
  have hpp : S.p.Prime := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
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
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2 hp)
    hBM (hBM.trans hMN) hBel hBc hr hr2 inf_le_right hQ.isPGroup
  have hQ2 : 2 ≤ CFSG.Open.pRank r (P ⊓ L) := hQr ▸ h2
  have hΓ : CFSG.Open.rankThreeGamma 1 r (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQ2 hF
  rw [hPL] at hΓ hQ2
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    have h0 : CFSG.Open.pRank r (⊥ : Subgroup G) = 0 := by
      obtain ⟨E', hE', -, hE'c⟩ := CFSG.SectionRank.exists_pRank hr.one_lt (⊥ : Subgroup G)
      rw [le_bot_iff.mp hE', card_bot] at hE'c
      exact (Nat.pow_eq_one.mp hE'c.symm).resolve_left hr.one_lt.ne'
    omega
  exact CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le
    (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hP hP1
    ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore le_rfl
      (le_trans (by norm_num) hQ2)).trans hΓ)
    fun y hy hyo => CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ hy hyo

@[expose] def S21_3ClosedChar (M L : Subgroup G) : Prop :=
  ∃ p : ℕ, 5 ≤ p ∧ (LieModel (BarInf L) .PSp 2 p 1 ∨
    ((LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) ∧
      CFSG.Open.pRank p M ≤ 2))

theorem uc22s213_not_centralizesBar_of_char (hGA : GriessAllModelsStatement)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable)
    (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hT : S21_3ClosedChar S.M L) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have key : ∀ {p : ℕ}, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (center (Bar2 L)) →
      ¬ p ∣ Nat.card (Outer (BarInf L)) → 3600 < Nat.card (BarInf L) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) →
      (p ∉ uniqueFourSigma S.M → CFSG.Open.pRank p S.M ≤ CFSG.Open.pRank p L) → False := by
    intro p hp hp5 hZ hout h3600 h2 hmr
    have hp2 : p ≠ 2 := by omega
    have hpL : 2 ≤ CFSG.Open.pRank p L := uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ ▸ h2
    have hpσ : p ∉ uniqueFourSigma S.M := fun h => by
      have := uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL hp hp2 (hN p h)
      omega
    have hspr : IsStronglyPEmbedded p S.M :=
      uc22s213_strong_of_pRank_le hS hU S hσ hSE hK3 hB hOut hL hp hp2 hZ hout hpL (hmr hpσ) hpσ
        (uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL S.hp.1.1 S.hp.1.2.1
          (hN S.p S.hp))
    have hpB : p ∣ Nat.card (BarInf L) := by
      have h1 := CFSG.GroupTheory.dvd_card_of_one_le_pRank hp
        (H := (⊤ : Subgroup (BarInf L))) (by omega)
      rwa [Subgroup.card_top] at h1
    exact uc22s213_not_centralizesBar_of_strong hS hU S hσ hPart hSE hSS hB Ch hH c hL hp hp5 hspr
      hpL hpB h3600 ha hpr haL
  obtain ⟨p, hp5, hX | ⟨hX | hX, hmp⟩⟩ := hT
  ·
    obtain ⟨hp, -, -⟩ := hX.admissible
    have hp2 : p ≠ 2 := by omega
    have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
      rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · omega
      · omega
      · omega
    have hZ := uc22s213_not_dvd_card_center_of_four hGA hL (.inr (.inr ⟨rfl, rfl⟩)) hX hp hp5
    refine key hp hp5 hZ (hX.not_dvd_card_outer_psp4 hp hp5 (Nat.not_dvd_of_pos_of_lt one_pos
      (by omega))) hX.three_thousand_six_hundred_lt_card_psp4 (by omega) fun hpσ => ?_
    have hM3 : CFSG.Open.pRank p S.M ≤ 3 := by
      by_contra h4
      exact hpσ (UC6.four_le_pRank_imp_mem_sigma hU S.maxLocal hp hp2 (by omega))
    rw [uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ] at h3
    omega
  ·
    obtain ⟨hp, -, -⟩ := hX.admissible
    have hp2 : p ≠ 2 := by omega
    have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
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
    refine key hp hp5 hZ (hX.not_dvd_card_outer_psl3 hp hp5 (Nat.not_dvd_of_pos_of_lt one_pos
      (by omega))) (hX.three_thousand_six_hundred_lt_card_psl3 (by rw [pow_one]; omega)) h2
      fun _ => ?_
    rw [uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ] at h2
    omega
  ·
    obtain ⟨hp, -, -⟩ := hX.admissible
    have hp2 : p ≠ 2 := by omega
    have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
      rcases hr with ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · omega
      · omega
      · exact absurd h (by decide)
      · omega
    have hZ := uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 hX
    refine key hp hp5 hZ (hX.not_dvd_card_outer_psu3 hp hp5 (Nat.not_dvd_of_pos_of_lt one_pos
      (by omega))) (hX.three_thousand_six_hundred_lt_card_psu3 (by rw [pow_one]; omega)) h2
      fun _ => ?_
    rw [uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ] at h2
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
