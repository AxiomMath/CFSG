module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Gamma614Application
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_not_three_dvd_card_solvableRadical {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L))) :
    ¬ 3 ∣ Nat.card (CFSG.solvableRadical ↥L) := by
  intro h3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.solvableRadical ↥L)) 3 h3
  have hx' : orderOf (x : ↥L) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (x : ↥L) ∈ center (Bar2 L) := by
    rw [← uc22p21k_map_solvableRadical_eq_center hq]
    exact mem_map_of_mem _ x.2
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (x : ↥L)) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, ← hx', pow_orderOf_eq_one, map_one]) fun h1 => ?_
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      Nat.prime_three (by norm_num) (hx' ▸ Subgroup.orderOf_dvd_natCard _ h1)
  exact hZ (hord ▸ Subgroup.orderOf_dvd_natCard _ hmem)

theorem uc22s213_pRank_three_barInf {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L))) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) = CFSG.Open.pRank 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  exact CFSG.SectionRank.pRank_quotient_eq (CFSG.solvableRadical ↥L)
    (uc22s213_not_three_dvd_card_solvableRadical hq hZ)

theorem uc22s213_isElemAbelian_of_isSylowOf {L Q : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (h27 : ¬ 27 ∣ Nat.card (BarInf L))
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L))) (hQ : IsSylowOf 3 Q L) :
    IsElemAbelian 3 Q ∧ Nat.card Q = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := uc22s213_not_three_dvd_card_solvableRadical hq hZ
  have hrank : 2 ≤ CFSG.Open.pRank 3 Q := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf Nat.prime_three hQ]
    exact uc22s213_pRank_three_barInf hq hZ ▸ h2
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hrank
  have hQ9 : Nat.card Q ≤ 9 := by
    obtain ⟨k, hk⟩ := hQ.isPGroup.exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra hk2
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num] at h27
      have h27L : 3 ^ 3 ∣ Nat.card (BarInf L) * Nat.card (CFSG.solvableRadical ↥L) := by
        rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
        exact (pow_dvd_pow 3 (by omega)).trans (hk ▸ Subgroup.card_dvd_of_le hQ.le)
      have hcop := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hR).pow_left 3
      exact h27 (hcop.dvd_of_dvd_mul_right h27L)
    rw [hk]
    exact (Nat.pow_le_pow_right (by norm_num) hk2).trans (by norm_num)
  have hEQ' : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (hQ9.trans (by rw [hEcard]; norm_num))
  subst hEQ'
  exact ⟨hEel, by rw [hEcard]; norm_num⟩

theorem uc22s213_le_centralizer_of_inner {L P : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hinn : ∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
      σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hP3 : IsPGroup 3 P) (hPN : P ≤ normalizer (L : Set G)) (hQ : IsSylowOf 3 (P ⊓ L) L)
    (hQab : IsMulCommutative ↥(P ⊓ L)) : P ⊓ L ≤ centralizer (P : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hInner : ∀ x ∈ P, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx
    have hx3 : Odd (orderOf x) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP3) ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hk
      exact hk ▸ Odd.pow (by decide)
    have hodd : Odd (orderOf (inducedBarInfAutHom L ⟨x, hPN hx⟩)) := by
      refine hx3.of_dvd_nat ?_
      have h := orderOf_map_dvd (inducedBarInfAutHom L) ⟨x, hPN hx⟩
      rwa [Subgroup.orderOf_mk] at h
    obtain ⟨lbar, hl⟩ := MonoidHom.mem_range.mp (hinn _ hodd)
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lbar
    refine ⟨(l : G), l.2, fun y hy => ?_⟩
    have hlN : (l : G) ∈ normalizer (L : Set G) := le_normalizer l.2
    have hcN : x * (l : G)⁻¹ ∈ normalizer (L : Set G) := mul_mem (hPN hx) (inv_mem hlN)
    have h1 : inducedBarInfAutHom L ⟨x * (l : G)⁻¹, hcN⟩ = 1 := by
      have he : (⟨x * (l : G)⁻¹, hcN⟩ : ↥(normalizer (L : Set G))) =
          ⟨x, hPN hx⟩ * (⟨(l : G), hlN⟩)⁻¹ := rfl
      rw [he, map_mul, map_inv, ← hl, uc22s2113_inducedBarInfAutHom_of_mem l.2]
      exact mul_inv_cancel _
    have hm := (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hq hcN h1).2
      ((l : G) * y * (l : G)⁻¹) (L.mul_mem (L.mul_mem l.2 hy) (L.inv_mem l.2))
    have heq : (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ =
        x * (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * (x * (l : G)⁻¹)⁻¹ *
          ((l : G) * y * (l : G)⁻¹)⁻¹ := by group
    exact heq ▸ hm
  have hPQ : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hPN).trans inf_normalizer_le_normalizer_inf
  have hQO2 : P ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hQ.isPGroup
      (UC6S846.isPGroup_pCoreOf L)).eq_bot
  have hdec : P ≤ P ⊓ L ⊔ PartOne.Section8.centralizerBar P L :=
    PartOne.Section8.le_sup_centralizerBar_of_inner inf_le_left inf_le_right rfl
      (normal_subgroupOf_of_le_normalizer hPQ) hQ hP3 hPN le_rfl hInner
  have hcomm := PartOne.Section8.commutator_eq_bot_centralizerBar inf_le_right hQO2 hPQ
  have hPC : P ≤ centralizer ((P ⊓ L : Subgroup G) : Set G) :=
    hdec.trans (sup_le (le_centralizer_iff_isMulCommutative.mpr hQab)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((Subgroup.commutator_comm _ _).trans hcomm)))
  exact le_centralizer_iff.mp hPC

theorem uc22s213_strong_of_inner (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hinn : ∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
      σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (h27 : ¬ 27 ∣ Nat.card (BarInf L))
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)))
    (hp : CFSG.Open.pRank S.p L ≤ 1) : IsStronglyPEmbedded 3 S.M := by
  by_contra hnot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hL3 : 2 ≤ CFSG.Open.pRank 3 L := uc22s213_pRank_three_barInf hL.2.2 hZ ▸ h2
  have hMN : S.M ≤ normalizer (L : Set G) := by
    by_contra hMN
    exact hZ (PartOne.Section8.three_dvd_center_bar2_of_calC_of_not_normal hS hU S hσ hnot hL
      (PartOne.Section8.pRank_three_eq_two_of_mem_calC_of_list880 hS S hPart hnot hL hL3) hMN)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 S.M
  have hQ : IsSylowOf 3 (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  obtain ⟨hQel, hQ9⟩ := uc22s213_isElemAbelian_of_isSylowOf hL.2.2 hZ h27 h2 hQ
  have hQC : P ⊓ L ≤ centralizer (P : Set G) :=
    uc22s213_le_centralizer_of_inner hL.2.2 hinn hP.isPGroup (hP.le.trans hMN) hQ hQel.1
  have h3β : 3 ∉ uniqueFourBeta G := fun h =>
    hnot (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h)
  have hpp : S.p.Prime := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  haveI : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p := UC6.conclusion76_dataOfSetup4 hSE hS hU S h3β S.hp hsp
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2 hp)
    hBM (hBM.trans hMN) hBel hBc Nat.prime_three (by norm_num) inf_le_right hQ.isPGroup
  have hQr : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQel (by rw [hQ9]; norm_num)
  have hΓ : CFSG.Open.rankThreeGamma 1 3 (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQr hF
  have hsub : uniqueFourSigma S.M ⊆ SigmaOne4 G := fun q hq =>
    ⟨hq.1, S.M, S.maxLocal, hq,
      PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL hq⟩
  exact hnot (PartOne.Section8.stronglyPEmbedded_of_e9_le_center_sylow hS hU S hPart.2.1 hsub
    (fun h => h3β h.1) hP (le_inf inf_le_left hQC) hQel hQ9 hΓ)

theorem uc22s213_pRank_le_one_of_centralizesBar {M L : Subgroup G} (hLM : L ≤ M) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime) (haL : CentralizesBar a L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ M) ≤ 1) :
    CFSG.Open.pRank p L ≤ 1 := by
  have hr2 : orderOf a ≠ 2 := fun h => Nat.not_odd_iff_even.mpr even_two (h ▸ hodd)
  have hY := uc22p21d_sup_pCore_eq hpr hr2 (Nat.card_zpowers a) fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers haL hg
  refine ((UC6.R869S.pRank_le_of_sup_pCore inf_le_left hY hp hp2).trans
    (CFSG.SectionRank.pRank_mono hp.one_lt (le_inf ?_ (inf_le_left.trans hLM)))).trans hN
  exact inf_le_right.trans (centralizer_le_normalizer _)

theorem uc22s213_not_centralizesBar_of_inner (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hinn : ∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
      σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (h27 : ¬ 27 ∣ Nat.card (BarInf L))
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)))
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  have hp := uc22s213_pRank_le_one_of_centralizesBar (CFSG.Quasithin.A3.subnormal_le hL.1) hodd
    hpr haL S.hp.1.1 S.hp.1.2.1 hN
  have h1 := hk1 (uc22s213_strong_of_inner hS hU S hσ hPart hSE hOut hL hZ hinn h27 h2 hp)
  have hb := uc22s213_pRank_three_barInf hL.2.2 hZ
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
