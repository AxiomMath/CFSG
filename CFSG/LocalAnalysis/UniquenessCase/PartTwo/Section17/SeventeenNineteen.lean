module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineteenDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


@[expose] def B17_19Bound (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (hV : Hyp125 D V₀ V) (L : Subgroup G), Ctx17_17 D V₀ V L → IsJ1 (Bar2 L) →
    (∀ g : G, g ∉ D.M → ¬ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g)) →
    UniqueMax D.M L →
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian + 4 <
        mBar D.M V₀ V hV.isElemAbelian

@[expose] def Gap17_19Delta (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) → IsJ1 (Bar2 L) →
    (∀ g : G, g ∉ D.M → ¬ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g)) → V₀ ≠ ⊥ →
      ¬ D.T ≤ Subgroup.normalizer (L : Set G) →
        ∃ Δ : Finset (Subgroup G),
          (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
            (∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H) ∧
              (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g)

theorem three_dvd_card_of_isJ1_bar2 {L : Subgroup G} (hJ : IsJ1 (Bar2 L)) :
    3 ∣ Nat.card L := by
  have h : 3 ∣ Nat.card (Bar2 L) := UC22.three_dvd_card_of_isJ1 hJ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
  exact h.mul_right _

theorem pRank_three_eq_one_of_isJ1_bar2 {L : Subgroup G} (hJ : IsJ1 (Bar2 L)) :
    CFSG.Open.pRank 3 L = 1 :=
  pRank_three_eq_one_of_thin_of_dvd (UC22.thin8_of_isJ1_bar2 hJ)
    (three_dvd_card_of_isJ1_bar2 hJ)

theorem exists_second_of_isJ1 (D : Data G) {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (hJ : IsJ1 (Bar2 L)) (hthin : F08.Thin8 L)
    (hpos : ∃ g : G, g ∉ D.M ∧ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g)) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ K ≠ L ∧
      ((F08.Thin8 K ∧ CFSG.Open.pRank 3 K = 1) ∨ ∃ n : ℕ, IsU3 (Bar2 K) (2 * n)) := by
  have hp3O : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isJ1_bar2 hJ
  have hp3 : CFSG.pRank 3 ↥L = 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥L,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hp3O
  have hnot : ¬ ((∀ K ∈ calC D.M, F08.Thin8 K → CFSG.pRank 3 ↥K = 1 → K = L) ∧
      (∀ K ∈ calC D.M, ∀ n : ℕ, ¬ IsU3 (Bar2 K) (2 * n))) := by
    intro hcon
    exact c.counter ⟨hJ, ⟨hthin, hp3, hcon.1⟩, hcon.2, hpos⟩
  rw [not_and_or] at hnot
  rcases hnot with hnot | hnot
  · push Not at hnot
    obtain ⟨K, hK, hthinK, hp3Kty, hKL⟩ := hnot
    have hp3K' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 1 := by
      rwa [CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥K] at hp3Kty
    have hp3K : CFSG.Open.pRank 3 K = 1 := by
      rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at hp3K'
    exact ⟨K, hK, hKL, Or.inl ⟨hthinK, hp3K⟩⟩
  · push Not at hnot
    obtain ⟨K, hK, n, hU⟩ := hnot
    refine ⟨K, hK, ?_, Or.inr ⟨n, hU⟩⟩
    rintro rfl
    exact (not_thin8_of_isU3 hU) hthin

theorem mem_uniqueSet_of_card_three_of_isJ1 (D : Data G) {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hJ : IsJ1 (Bar2 L)) (h8107 : F08.R8107 D)
    (hU3 : Inputs1719.K_U3FourPowThreeRankOne) :
    ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 → A ∈ uniqueSet D.M := by
  intro A hAL hA3
  have hthin : F08.Thin8 L := UC22.thin8_of_isJ1_bar2 hJ
  have hp3L : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isJ1_bar2 hJ
  by_cases hpos : ∃ g : G, g ∉ D.M ∧ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g)
  · obtain ⟨K, hKcal, hKL, hcase⟩ := exists_second_of_isJ1 D c hJ hthin hpos
    obtain ⟨A₂, hA₂K, -, hA₂card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
    have hp3K : CFSG.Open.pRank 3 K = 1 := by
      rcases hcase with ⟨-, h⟩ | ⟨n, hU⟩
      · exact h
      · have hn1 : 1 ≤ n := by
          have hf : 1 ≤ 2 * n := hU.admissible.2.1
          omega
        rw [← UC22.pRank_bar2_eq_of_odd (Y := K) Nat.prime_three (by norm_num)]
        exact hU3 (Bar2 K) n hn1 hU
    rw [hp3K, pow_one] at hA₂card
    rcases hcase with ⟨hthinK, -⟩ | ⟨n, hU⟩
    · exact (h8107 L c.mem_calC K hKcal (Ne.symm hKL) hp3L hp3K (Or.inl hthin)
        (Or.inl hthinK) A A₂ hAL hA3 hA₂K hA₂card).1
    · exact (h8107 L c.mem_calC K hKcal (Ne.symm hKL) hp3L hp3K (Or.inl hthin)
        (Or.inr ⟨2 * n, hU⟩) A A₂ hAL hA3 hA₂K hA₂card).1
  · refine ⟨hAL.trans c.mem_calC.1.le, ?_⟩
    intro g hAg
    by_cases hg : g ∈ D.M
    · refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
      rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
    · have hAg' : A ≤ conjSubgroup D.M g⁻¹ := by
        simpa [conjSubgroup, inv_inv] using hAg
      have hAK : A ≤ L ⊓ conjSubgroup D.M g⁻¹ := le_inf hAL hAg'
      have hdvd : Nat.card A ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g⁻¹) := by
        have h1 : Nat.card ↥(A.subgroupOf (L ⊓ conjSubgroup D.M g⁻¹)) ∣
            Nat.card ↥(L ⊓ conjSubgroup D.M g⁻¹) := Subgroup.card_subgroup_dvd_card _
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv] at h1
      exact absurd ⟨g⁻¹, by simpa using hg, hA3 ▸ hdvd⟩ hpos

theorem uniqueMax_of_isJ1 (D : Data G) {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (hJ : IsJ1 (Bar2 L))
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D)
    (hAuniq : ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 → A ∈ uniqueSet D.M) :
    UniqueMax D.M L := by
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_isJ1_bar2 hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hxG : orderOf ((x : ↥L) : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  set A : Subgroup G := Subgroup.zpowers ((x : ↥L) : G) with hAdef
  have hA3 : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hxG]
  have hAL : A ≤ L := Subgroup.zpowers_le.mpr x.2
  have hAuniq' : A ∈ uniqueSet D.M := hAuniq A hAL hA3
  unfold UniqueMax
  ext H
  simp only [calMOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hH, hLH⟩
    by_contra hne
    have : IsSimpleGroup G := D.standing.simple
    have htop : H ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hH.1
    have hnotle : ¬ H ≤ D.M := fun hle => hne (hH.2 D.M D.maxLocal.1 hle).symm
    have hhyp : Hyp919c D L A L H :=
      ⟨c.mem_calC, hAL, hA3, hAuniq', hLM,
        by rw [inf_idem]
           exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm,
        by simp, ⟨0, by simp⟩, htop, hLH, hnotle⟩
    exact h920 L A L H hhyp le_rfl hJ
  · rintro rfl
    exact ⟨D.maxLocal, hLM⟩

theorem seventeen_nineteen (D : Data G) (V₀ V : Subgroup G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (h111 : W3Thm111 G) (h117 : C117 D V₀ V)
    (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D)
    (hU3 : Inputs1719.K_U3FourPowThreeRankOne)
    (hB : B17_19Bound D V₀ V) (hDelta : Gap17_19Delta D V₀ V)
    (hKJ1 : Inputs1719.K_J1A5Gen) (hKc : Inputs1719.K_L2SzAutRank) :
    R17_19At D V₀ V := by
  intro L c hJ
  have hAuniq := mem_uniqueSet_of_card_three_of_isJ1 D c hJ h8107 hU3
  have hU : UniqueMax D.M L := uniqueMax_of_isJ1 D c hJ h920 hAuniq
  have h3' : ∀ g : G, g ∉ D.M → ¬ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) := by
    intro g hg h3
    by_cases hb : L ⊓ conjSubgroup D.M g = ⊥
    · rw [hb] at h3
      norm_num at h3
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(L ⊓ conjSubgroup D.M g)) 3 h3
      set A : Subgroup G := Subgroup.zpowers ((y : ↥(L ⊓ conjSubgroup D.M g)) : G)
        with hAdef
      have hyG : orderOf ((y : ↥(L ⊓ conjSubgroup D.M g)) : G) = 3 := by
        rw [Subgroup.orderOf_coe]; exact hy
      have hA3 : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hyG]
      have hAle : A ≤ L ⊓ conjSubgroup D.M g := Subgroup.zpowers_le.mpr y.2
      have hmem := hAuniq A (hAle.trans inf_le_left) hA3
      have hleConj : A ≤ conjSubgroup D.M g := hAle.trans inf_le_right
      have hconj := hmem.2 g⁻¹ (by simpa [conjSubgroup, inv_inv] using hleConj)
      have hnorm : g⁻¹ ∈ Subgroup.normalizer (D.M : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
      rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
        at hnorm
      exact hg (by simpa using D.M.inv_mem hnorm)
  have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le c.mem_calC.1.le) hU
  have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 c.hyp125 h117 c.mem_calC hU
  have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hconf : V₀ ≠ ⊥ → ∃ Δ : Finset (Subgroup G),
      (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
      (∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H) ∧
      (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g) := by
    intro hV0
    by_cases hT : D.T ≤ Subgroup.normalizer (L : Set G)
    · exact exists_delta_of_normal D c hJ hT h3' hU hKJ1 hKc
    · exact hDelta L c hJ h3' hV0 hT
  have hm := mBar_le_bBar_add_of_delta D hx h61 h127 h1114 h162 hTor h1482 h126 h111
    c.hyp125 2 c.mem_calC.1 c.mem_calC.2.2 hL1 hUc hconf hk
  have hb := hB c.hyp125 L c hJ h3' hU
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
