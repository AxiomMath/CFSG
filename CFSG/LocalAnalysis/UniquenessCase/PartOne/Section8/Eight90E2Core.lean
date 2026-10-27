module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90E2Act
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90E2Comp
import CFSG.GroupTheory.LocalCores.ComponentCentralizer
import CFSG.GroupTheory.QuasisimpleCenterDivisibility
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec16.Steps166 (NoSzSection)

@[expose] def NoSzSectionAutRankOne : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S → CFSG.pRank 3 S = 1 → NoSzSection (MulAut S)

structure Cfg5e2 (H : Type) [Group H] [Finite H] (Y K : Subgroup H) (n : ℕ) : Prop where
  kGroup : CFSG.Open.IsKGroup H
  normal_Y : Y.Normal
  card_Y : Nat.card Y = 3
  three_part : (Nat.card H).factorization 3 = 2
  pCore_eq_bot : CFSG.pCore 2 H = ⊥
  perfect : ⁅K, K⁆ = K
  pCoreOf_ne_bot : pCoreOf 2 K ≠ ⊥
  sz : IsSz (Bar2 K) n
  comm_oddCore : ⁅K, CFSG.oddCore H⁆ = ⊥
  rank_five : ∀ s : H, orderOf s = 2 → CFSG.Open.pRank 5 (centralizer ({s} : Set H)) ≤ 3

theorem cfg5e2_pCoreOf_le_centralizer_component
    (hKSch : UCK.KSch)
    (hK3 : PartTwo.Inputs1719.K_CatalogueThreePrimeSz) (hNo : NoSzSectionAutRankOne)
    {H : Type} [Group H] [Finite H] {Y K : Subgroup H} {n : ℕ} (h : Cfg5e2 H Y K n) :
    ∀ C : Subgroup H, CFSG.IsComponent C → pCoreOf 2 K ≤ centralizer (C : Set H) := by
  have htp : (Nat.card H).factorization 3 = 2 := h.three_part
  have h27 : ¬ 27 ∣ Nat.card H := by
    intro hd
    have hne : Nat.card H ≠ 0 := by
      rintro h0
      rw [h0] at htp
      simp at htp
    have hle : 3 ≤ (Nat.card H).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp (by simpa using hd)
    omega
  intro C hC
  have hKC : K ≤ normalizer (C : Set H) :=
    le_normalizer_of_isComponent hK3 h.kGroup h27 h.rank_five h.perfect hC
  have hleK : pCoreOf 2 K ≤ K := CFSG.openPCoreOf_le 2 K
  by_cases h3C : 3 ∣ Nat.card C
  · have h3dvd : 3 ∣ Nat.card (↥C ⧸ center ↥C) :=
      CFSG.dvd_card_quotient_center_of_quasisimple hC.1 Nat.prime_three h3C
    have hsimple : IsSimpleGroup (↥C ⧸ center ↥C) := hC.1.2.1
    have hcat : CFSG.Open.IsCatalogGroup (↥C ⧸ center ↥C) :=
      (h.kGroup.subgroup C).isCatalogGroup_of_surjective (⊤ : Subgroup ↥C) hC.1.2.2
        ((QuotientGroup.mk' (center ↥C)).comp
          (Subgroup.topEquiv (G := ↥C)).toMonoidHom)
        ((QuotientGroup.mk'_surjective _).comp
          (Subgroup.topEquiv (G := ↥C)).surjective)
    have hge : 1 ≤ CFSG.pRank 3 (↥C ⧸ center ↥C) := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three h3dvd
    have hle : CFSG.pRank 3 (↥C ⧸ center ↥C) ≤ 1 :=
      CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd (by
        have h9 := not_nine_dvd_card_quotient_center h.normal_Y h.card_Y h27 hC
        simpa using h9)
    have hpr : CFSG.pRank 3 (↥C ⧸ center ↥C) = 1 := le_antisymm hle hge
    exact hleK.trans (le_centralizer_of_noSzSection h.perfect h.sz hC.1 hKC
      (hNo (↥C ⧸ center ↥C) hC.1.2.2 hcat hpr))
  · obtain ⟨m, hSzC⟩ := exists_isSz_quotient_center hK3 h.kGroup hC h3C
    have hCK : CFSG.Open.IsKGroup (↥C ⧸ center ↥C) :=
      (h.kGroup.subgroup C).quotient (center ↥C)
    exact pCoreOf_le_centralizer_of_isSz hKSch h.perfect hC.1 hCK hSzC hKC

theorem false_of_cfg5e2
    (hKSch : UCK.KSch) (hK3 : PartTwo.Inputs1719.K_CatalogueThreePrimeSz)
    (hNo : NoSzSectionAutRankOne) {H : Type} [Group H] [Finite H] {Y K : Subgroup H} {n : ℕ}
    (h : Cfg5e2 H Y K n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp := cfg5e2_pCoreOf_le_centralizer_component hKSch hK3 hNo h
  have hF : K ≤ centralizer (CFSG.fittingSubgroup H : Set H) := by
    have hFO : CFSG.fittingSubgroup H ≤ CFSG.oddCore H :=
      CFSG.RankThree.PartTwo.Sec4.Census.fittingSubgroup_le_oddCore h.pCore_eq_bot
    have hcent : K ≤ centralizer (CFSG.oddCore H : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.comm_oddCore
    exact hcent.trans (Subgroup.centralizer_le hFO)
  have hgen : pCoreOf 2 K ≤ centralizer (CFSG.generalizedFitting H : Set H) :=
    CFSG.LocalCores.le_centralizer_generalizedFitting
      ((CFSG.openPCoreOf_le 2 K).trans hF) hcomp
  exact h.pCoreOf_ne_bot
    (CFSG.LocalCores.eq_bot_of_isPGroup_of_le_centralizer_generalizedFitting
      (p := 2) h.pCore_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hgen)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
