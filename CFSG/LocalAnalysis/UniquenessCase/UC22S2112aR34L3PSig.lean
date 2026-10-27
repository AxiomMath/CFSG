module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3POdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YConfig
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.Quasithin.Background.A3FactsA134

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

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

theorem uc22s2112l3p_pRank_top_le_one {X : Type} [Group X] [Finite X] {p q : ℕ}
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
      (∀ S : Sylow q H, IsCyclic (S : Subgroup H)) →
        ∀ P : Sylow q X, IsCyclic (P : Subgroup X) := by
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

theorem uc22s2112l3p_pRank_mulAut_bar2_le_one {M L : Subgroup G} (hL : L ∈ calC M) {p s : ℕ}
    (hs : s.Prime) (hs5 : 5 ≤ s) (hsp : s ≠ p)
    (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1)
    (hd : ¬ s ∣ p ^ 2 - 1) :
    Open.pRank s (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1 := by
  have hq := hL.2.2
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  have hXS : LieModel (Bar2 L ⧸ center (Bar2 L)) .PSL 3 p 1 ∨
      LieModel (Bar2 L ⧸ center (Bar2 L)) .PSU 3 p 1 :=
    hX.imp (LieModel.of_mulEquiv e) (LieModel.of_mulEquiv e)
  have hsimple : IsSimpleGroup (Bar2 L ⧸ center (Bar2 L)) := hq.2
  have hZ := CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_of_nonabelian hsimple
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (Bar2 L) hq)
  have h1 : ¬ s ∣ 1 := fun h => by
    have := Nat.le_of_dvd one_pos h
    omega
  have hOut : ¬ s ∣ Nat.card (Outer (Bar2 L ⧸ center (Bar2 L))) := by
    rcases hXS with h | h
    · exact h.not_dvd_card_outer_psl3 hs hs5 h1
    · exact h.not_dvd_card_outer_psu3 hs hs5 h1
  exact (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_mulAut_le_of_quasisimple
    hs.one_lt hq).trans ((CFSG.AGLEmbedding.pRank_top_mulAut_le_of_not_dvd hs hZ hOut).trans
      (uc22s2112l3p_pRank_top_le_one hs (by omega) hsp hXS hd))

theorem uc22s2112l3p_r149_of_sigmaStd
    (hGA : GriessAllModelsStatement) (hK35w : UCK.K35w)
    (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree) {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76Sig D) (h63 : UC6.R6_3 D) : R149L3P D := by
  classical
  intro L hL p hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ D.M := hL.1.le
  have hns := UC6S846.not_solvable_of_mem_calC hL
  by_cases hpσ : p ∈ D.sig
  · exact ⟨p, hp, dvd_mul_right p _, UC6S846.sp_of_mem_sig hSg hns hpσ⟩
  obtain ⟨s, hsσ⟩ := hSg.nonempty
  obtain ⟨hs, hs2⟩ := D.sig_prime s hsσ
  have : Fact s.Prime := ⟨hs⟩
  have hsp := UC6S846.sp_of_mem_sig hSg hns hsσ
  by_cases h3 : s = 3
  · exact ⟨s, hs, h3 ▸ three_dvd_mul_sq_sub_one p, hsp⟩
  by_cases hd : s ∣ p ^ 2 - 1
  · exact ⟨s, hs, dvd_mul_of_dvd_right hd p, hsp⟩
  have hs5 : 5 ≤ s := hs.five_le_of_ne_two_of_ne_three hs2 h3
  have hsp' : s ≠ p := fun h => hpσ (h ▸ hsσ)
  have hZ : ¬ p ∣ Nat.card (center (Bar2 L)) := by
    rcases hX with h | h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inl rfl) hp2 h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 h
  have hpL : 2 ≤ Open.pRank p L := by
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2
      (hX.imp (·.statedClassicalModel_of_ne_zero (by norm_num))
        (·.statedClassicalModel_of_ne_zero (by norm_num)))
  have hM3 : Open.pRank p D.M ≤ 3 := by
    by_contra h4
    exact hpσ (hSg.four_mem p hp hp2 (by omega))
  have hMN : D.M ≤ normalizer (L : Set G) := by
    intro g hg
    by_contra hgN
    have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
      hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
    exact hpσ (hSg.four_mem p hp hp2
      (uc22s213_four_le_pRank_of_two_conj hL (PartOne.Section8.mem_conjSetOf_self D.M L)
        ⟨g, hg, rfl⟩ hne hp hp2 hpL hZ))
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p D.M
  have hQ : IsSylowOf p (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  have hQ2 : 2 ≤ Open.pRank p (P ⊓ L) :=
    (CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hp hQ) ▸ hpL
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hs (hSg.three_le s hsσ)
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut_le hLM hs hs2 (k := 1)
    (uc22s2112l3p_pRank_mulAut_bar2_le_one hL hs hs5 hsp' hX hd) hBM (hBM.trans hMN) hBel hBc
    hp hp2 inf_le_right hQ.isPGroup
  have hΓ : rankThreeGamma 1 p (P ⊓ L) ≤ D.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp
      (h76 s hsσ hs2 hsp) (inf_le_right.trans hLM) hQ.isPGroup hQ2 hF
  exact ⟨p, hp, dvd_mul_right p _, PartOne.Section8.isStronglyPEmbedded_of_eight73Y_lieModel hGA
    hK35w hKZ h63 hp2 hL hX hM3 hQ hΓ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
