module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3POdd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YConfig
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Ident
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

private theorem three_dvd_mul_sq_sub_one (p : ℕ) : 3 ∣ p * (p ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have h1 : 1 ≤ p := hp
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp
  have h : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    zify [h1, h2]
    ring
  rw [h]
  rcases (by omega : 3 ∣ p ∨ 3 ∣ p - 1 ∨ 3 ∣ p + 1) with h3 | h3 | h3
  · exact dvd_mul_of_dvd_left h3 _
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h3 _) _
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h3 _) _

private theorem pRank_top_le_one_of_lieModel {X : Type} [Group X] [Finite X] {p q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hX : LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1) (hd : ¬ q ∣ p ^ 2 - 1) :
    Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hpm : ∀ ε : ℤ, ε = 1 ∨ ε = -1 → 1 ≤ p → ¬ (q : ℤ) ∣ p - ε := fun ε hε hp h => hd <| by
    have hcast : ((p ^ 2 - 1 : ℕ) : ℤ) = ((p : ℤ) - ε) * ((p : ℤ) + ε) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp)]
      rcases hε with rfl | rfl <;> push_cast <;> ring
    exact Int.natCast_dvd_natCast.1 (hcast ▸ dvd_mul_of_dvd_left h _)
  have key : ∀ {H : Type} [Group H] [Finite H] (f : H →* X), Function.Surjective f →
      (∀ S : Sylow q H, IsCyclic (S : Subgroup H)) → ∀ P : Sylow q X, IsCyclic (P : Subgroup X) := by
    intro H _ _ f hf hH P
    obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf q P
    have := hH S
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hcyc : ∀ P : Sylow q X, IsCyclic (P : Subgroup X) := by
    rcases hX with hX | hX
    · obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel_of_ne_zero (by norm_num)
      rw [pow_one] at hK
      exact key (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
        (e.symm.surjective.comp (QuotientGroup.mk'_surjective _))
        ((CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hp (ε := 1)
          (H := StatedSL 3 K) (Or.inl ⟨rfl, hK, rfl⟩)).1 q hq2 hqp
          (hpm 1 (.inl rfl) hp.one_lt.le))
    · obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel_of_ne_zero (by norm_num)
      rw [pow_one] at hK
      exact key (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
        (e.symm.surjective.comp (QuotientGroup.mk'_surjective _))
        ((CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hp (ε := -1)
          (H := StatedSU 3 (p ^ 1) K) (Or.inr ⟨rfl, hK, by rw [pow_one]⟩)).1 q hq2 hqp
          (hpm (-1) (.inr rfl) hp.one_lt.le))
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q X))
  exact CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow hq P (hcyc P)

theorem uc22s2112l3p_r149_setup4 (hGA : GriessAllModelsStatement)
    (hK35w : UCK.K35w) (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) :
    R149L3P (UC6.dataOfSetup4 hS hU S) := by
  classical
  intro L hL p hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ S.M := hL.1.le
  by_cases hpσ : p ∈ uniqueFourSigma S.M
  · exact ⟨p, hp, dvd_mul_right p _,
      PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL hpσ⟩
  have hpp : S.p.Prime := S.hp.1.1
  have hp2S : S.p ≠ 2 := S.hp.1.2.1
  have : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  by_cases hpS : 2 ≤ Open.pRank S.p L
  ·
    refine ⟨S.p, hpp, ?_, hsp⟩
    by_cases h3 : S.p = 3
    · rw [h3]
      exact three_dvd_mul_sq_sub_one p
    have hpS5 : 5 ≤ S.p := hpp.five_le_of_ne_two_of_ne_three hp2S h3
    refine dvd_mul_of_dvd_right ?_ p
    by_contra hd
    have hZ3 : Nat.card (center (Bar2 L)) ∣ 3 := by
      rcases hX with h | h
      · exact uc22s213_card_center_bar2_dvd_three hGA hL (Or.inl rfl) h
      · exact uc22s213_card_center_bar2_dvd_three hGA hL (Or.inr rfl) h
    have hZS : ¬ S.p ∣ Nat.card (center (Bar2 L)) := fun h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans hZ3)
      omega
    have h1 := pRank_top_le_one_of_lieModel hpp hp2S (fun h : S.p = p => hpσ (h ▸ S.hp)) hX hd
    rw [uc22s213_pRank_barInf_of_prime hL.2.2 hpp hp2S hZS] at h1
    omega
  have hZ : ¬ p ∣ Nat.card (center (Bar2 L)) := by
    rcases hX with h | h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inl rfl) hp2 h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 h
  have hpL : 2 ≤ Open.pRank p L := by
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2
      (hX.imp (·.statedClassicalModel_of_ne_zero (by norm_num))
        (·.statedClassicalModel_of_ne_zero (by norm_num)))
  have hM3 : Open.pRank p S.M ≤ 3 := by
    by_contra h4
    exact hpσ (UC6.four_le_pRank_imp_mem_sigma hU S.maxLocal hp hp2 (by omega))
  have hMN : S.M ≤ normalizer (L : Set G) :=
    uc22s213_le_normalizer_of_not_mem_sigma hU S.maxLocal hL hp hp2 hpL hZ hpσ
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p S.M
  have hQ : IsSylowOf p (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  have hQ2 : 2 ≤ Open.pRank p (P ⊓ L) :=
    (CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hp hQ) ▸ hpL
  have h76 : Conclusion76 S.M S.p := by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact PartOne.Section7.c76Three_of_inputs hSE hK3 hB hS hU S hσ h3 S.p S.hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 S.hp hsp
  obtain ⟨Bp, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2S
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2S
      (by omega)) hBM (hBM.trans hMN) hBel hBc hp hp2 inf_le_right hQ.isPGroup
  have hΓ : rankThreeGamma 1 p (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQ2 hF
  exact ⟨p, hp, dvd_mul_right p _, PartOne.Section8.isStronglyPEmbedded_of_eight73Y_lieModel hGA
    hK35w hKZ (UC6.r6_3_dataOfSetup4 hS hU S hPart.1) hp2 hL hX hM3 hQ hΓ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
