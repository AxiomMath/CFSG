module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5U3
public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
public import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElemAbelianProjection
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_isU3_of_dvd {K : Subgroup G} {n q : ℕ} (hU : IsU3 (Bar2 K) n)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1) : CFSG.Open.pRank q K ≤ 1 := by
  obtain ⟨hSU, hZ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.U3Loss.isSU3_of_isU3 hU
  have hqn' : ¬ q ∣ 2 ^ n + 1 := by
    intro h
    have h2 : q ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h hqn
    have hsub : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [hsub] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
  have hZ' : ¬ q ∣ Nat.card (center (Bar2 K)) := by
    rw [hZ, Subgroup.card_bot]
    exact hq.not_dvd_one
  have h := uc22ine229_pRank_le_one_of_isSU3 hSU hq hq2 hqn' hZ'
  rwa [pRank_bar2_eq_of_odd (Y := K) hq hq2] at h

section Certificates

theorem gap19_20b_at (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h3 : S17.R17_3At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (hj4 : S17.jM D p = 4 →
      ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
        IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
        (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
        IsPowTwo (S17.nOf L) ∧ 2 < S17.nOf L)
    (heven : Even (S17.nOf L)) :
    ∃ E : Subgroup G, E ≤ A ∧ E ≠ ⊥ ∧ ¬ 3 ∣ Nat.card E ∧ normalizer (E : Set G) ≤ D.M := by
  obtain ⟨q, hq, hq2, hq3, hqn⟩ :=
    CFSG.exists_prime_ne_two_ne_three_dvd_two_pow_sub_one (three_le_nOf_of_setting1910 h.h1910)
  have hqA : q ∣ Nat.card A := by
    rw [card_eq_of_isZModSq h.hAcard]
    exact dvd_mul_of_dvd_left hqn _
  obtain ⟨E, hEA, hEel, hEcard⟩ := exists_isElemAbelian_card_prime_sq_of_isZModSq h.hAcard hq hqA
  have key : ∀ L₁ L₂ : Subgroup G, L₁ ∈ calC D.M → F08.Thin8 L₁ →
      L₂ ≤ normalizer (L₁ : Set G) → CFSG.Open.pRank q L₂ ≤ 1 → A ≤ L₁ ⊔ L₂ →
      ∃ E : Subgroup G, E ≤ A ∧ E ≠ ⊥ ∧ ¬ 3 ∣ Nat.card E ∧ normalizer (E : Set G) ≤ D.M := by
    intro L₁ L₂ hL₁ hthin hnorm hrk hA
    obtain ⟨F, hFle, hFcard⟩ := CFSG.GroupTheory.exists_card_prime_le_inf_of_le_sup hq hq2
      hnorm hrk (hEA.trans hA) hEel hEcard
    refine ⟨F, hFle.trans (inf_le_left.trans hEA), ?_, ?_, ?_⟩
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hFcard
      exact hq.one_lt.ne hFcard
    · rw [hFcard]
      intro h3q
      exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3q).symm
    · exact h3 L₁ hL₁ hthin F ⟨q, hq, hq2, hFcard, hFle.trans inf_le_right⟩
  by_cases hj : S17.jM D p = 4
  · obtain ⟨K₁, K₂, hK₁, hK₂, hne, hIOfeq, hL₂K₁, hL₂K₂, -, -⟩ := hj4 hj
    have hrk : CFSG.Open.pRank q K₂ ≤ 1 := by
      rcases hL₂K₂ with hL₂ | hU₃
      · exact S17.thin8_of_isL2 hL₂ q hq hq2
      · exact pRank_le_one_of_isU3_of_dvd hU₃ hq hq2 hqn
    exact key K₁ K₂ hK₁ (S17.thin8_of_isL2 hL₂K₁) (uc22p22u_calC_normalizes hK₁ hK₂ hne) hrk
      (hIOfeq ▸ h.hA)
  · have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
    have h1910 := h.h1910
    simp only [Setting1910] at h1910
    have hXne : conjClosure D.M L ≠ L := by
      obtain ⟨-, h1 | h2 | h3alt⟩ := h1910
      · exact absurd heven (Nat.not_even_iff_odd.mpr h1.2.1)
      · exact h2.2.1
      · intro hXL
        have hq' : CFSG.Open.IsQuasisimple (Bar2 (IOf D p L)) := by
          rw [hI, hXL]
          exact h.hyp.hL.1.2.2
        rcases h3alt.1 with ⟨A', B', gA, gB, ⟨f⟩, hA', hB'⟩ |
            ⟨A', B', gA, gB, ⟨f⟩, hA', hB'⟩
        · have : IsSimpleGroup A' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA'
          have : IsSimpleGroup B' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB'
          exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
            (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq')).false f
        · have : IsSimpleGroup A' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA'
          have : IsSimpleGroup B' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB'
          exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
            (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq')).false f
    obtain ⟨m, x, hxM, hXsup, -, hshape, -⟩ :=
      S17.p42_alt2_of_ne h42 h.hyp.hp h.hyp.hL.1 hXne
    let L₂ : Subgroup G := CFSG.Quasithin.conjSubgroup L x
    have hcal : L₂ ∈ calC D.M :=
      (S17.conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsup hXne).1
    have hne : L ≠ L₂ :=
      (S17.conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsup hXne).2.symm
    have hshape' : IsL2 (Bar2 L) m ∨ IsSz (Bar2 L) m := hshape.imp (·.1) (·.1)
    have hshape₂ : IsL2 (Bar2 L₂) m ∨ IsSz (Bar2 L₂) m := by
      change IsL2 (Bar2 (L.map (MulAut.conj x⁻¹).toMonoidHom)) m ∨
        IsSz (Bar2 (L.map (MulAut.conj x⁻¹).toMonoidHom)) m
      obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
      exact hshape'.imp (LieModel.of_mulEquiv e) (LieModel.of_mulEquiv e)
    exact key L L₂ h.hyp.hL.1 (uc22s13a_thin8_of_isL2_or_isSz hshape')
      (uc22p22u_calC_normalizes h.hyp.hL.1 hcal hne)
      (uc22s13a_thin8_of_isL2_or_isSz hshape₂ q hq hq2)
      (by rw [← hXsup, ← hI]; exact h.hA)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
