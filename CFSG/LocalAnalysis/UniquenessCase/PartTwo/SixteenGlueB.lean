module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Cover
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem centralizer_cClos_le_of_commutator_eq_bot (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {i : ℕ} (hW : ⁅E3.wClos V i D.T, V⁆ = ⊥) :
    centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
  have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D h.inCalV
  have hW' : E3.wClos V i D.T ≤ centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW
  have hVc : V ≤ E3.cClos V i D.T := le_inf hVT (Subgroup.le_centralizer_iff.1 hW')
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVc)).trans
    (centralizer_le_of_inCalV D h.inCalV)

theorem mem_cClos_of_mem_center (D : Data G) (V : Subgroup G) (i : ℕ) {z : G} (hz : z ∈ D.T)
    (hc : ∀ t ∈ D.T, z * t = t * z) : z ∈ E3.cClos V i D.T := by
  refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (hc w (E3.wClos_le i D.T hw)).symm

theorem centralizer_cClos_le_of_ne_bot (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) (i : ℕ) : centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
  have hCU : CentralizersUnique D.M D.T := by
    rcases h.1 with ⟨-, h0⟩ | ⟨-, hCU, -⟩
    · exact absurd h0 hV₀
    · exact hCU
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hTne : D.T ≠ ⊥ := fun hb =>
    h.pairFacts.ne_bot (le_bot_iff.1 (hb ▸ uc22p22p_le_T_of_inCalV D h.inCalV))
  haveI : Nontrivial ↥D.T := (Subgroup.nontrivial_iff_ne_bot D.T).2 hTne
  haveI : Nontrivial ↥(Subgroup.center ↥D.T) := hT2.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥D.T))
  have hzc : ∀ t ∈ D.T, ((z : ↥D.T) : G) * t = t * ((z : ↥D.T) : G) := fun t ht =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨t, ht⟩).symm
  have hzne : ((z : ↥D.T) : G) ≠ 1 := fun hz =>
    hz1 (Subtype.ext (Subtype.ext hz))
  have hzT : ((z : ↥D.T) : G) ∈ D.T := (z : ↥D.T).2
  have hzM := (hCU _ hzT hzc hzne).1
  refine le_trans ?_ hzM
  refine Subgroup.centralizer_le ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact mem_cClos_of_mem_center D V i hzT hzc

theorem Data.k_eq_one_of_isStronglyPEmbedded (D : Data G)
    (h : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) : D.k = 1 := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  rw [if_pos h]

theorem Data.k_eq_one_of_three_mem (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h3 : 3 ∈ D.sig) : D.k = 1 :=
  Data.k_eq_one_of_isStronglyPEmbedded D (hSg.sig1_sp 3 (h1219 ▸ h3))

theorem v0_eq_bot_and_not_le_of_trichotomy (D : Data G) {V₀ V : Subgroup G}
    (h24 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
      ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M ∨ (calO2 D.k D.M V₀ V).Nonempty)
    (h : Hyp16 D V₀ V) {i : ℕ} (hk : D.k = i)
    (hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) (hO : calO2 i D.M V₀ V = ∅) :
    V₀ = ⊥ ∧ ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
  have hC : ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
    rcases h24 with h1 | h1 | h1
    · exact absurd hN h1
    · rwa [hk] at h1
    · rw [hk, hO] at h1
      exact absurd h1 (Set.not_nonempty_empty)
  exact ⟨by_contra fun hV0 => hC (centralizer_cClos_le_of_ne_bot D h.hyp125 hV0 i), hC⟩

theorem calO2_subset_calO (n : ℕ) (M V₀ V : Subgroup G) : calO2 n M V₀ V ⊆ calO n M V₀ V := by
  rintro X ⟨g, rfl, h, -⟩
  exact ⟨g, rfl, h⟩

private theorem s16b_three_le (D : Data G) (hSg : UC6S846.SigmaStd D) :
    ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p ↥D.M := fun p hp => by
  rw [UC6.groupPRank_eq_pRank]
  exact hSg.three_le p hp

theorem sixteen_twentyFive (D : Data G) (h31 : R16_31 D) (h32 : R16_32 D) : R16_25 D := by
  intro V₀ V L hV hS h8
  exact (h31 V₀ V L hV hS h8).2
    (centralizer_cClos_le_of_commutator_eq_bot D hS.setting.hyp16.hyp125
      (h32 V₀ V L hV hS h8))

theorem sixteen_fortyEight (D : Data G) (h55 : R16_55 D) (h56 : R16_56 D) : R16_48 D := by
  intro V₀ V L hV hS h4
  exact (h55 V₀ V L hV hS h4).2
    (centralizer_cClos_le_of_commutator_eq_bot D hS.setting.hyp16.hyp125
      (h56 V₀ V L hV hS h4 (h55 V₀ V L hV hS h4).1))

theorem sixteen_thirtyThree (D : Data G) (h38 : R16_38 D) (h39 : R16_39 D)
    (hcl : R16_33_close D) : R16_33 D := by
  intro V₀ V L hV hS
  have key : ∀ m : ℕ, Case1633 D V₀ V hV L m → False := by
    intro m hm
    obtain ⟨hm2, hV0, hC⟩ := h39 V₀ V L hV hS m hm
    have hne := hcl V₀ V L hV hS m hm hm2 hV0 hC
    have hemp := h38 V₀ V L hV hS m hm 0 (by omega)
    subst hm2
    rw [hemp] at hne
    exact absurd hne Set.not_nonempty_empty
  exact ⟨fun h5 => key 2 (Or.inl ⟨h5, rfl⟩), fun h6 => key 3 (Or.inr ⟨h6, rfl⟩)⟩

theorem sixteen_thirtyOne (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h24 : R16_24c D) (h29 : R16_29 D) (h30 : R16_30 D) : R16_31 D := by
  intro V₀ V L hV hS h8
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hSg h1219 (by rw [h8.2.2.1]; exact Set.mem_singleton 3)
  exact v0_eq_bot_and_not_le_of_trichotomy D (h24 V₀ V L hV hS (Or.inr (Or.inr (Or.inr h8))))
    hS.setting.hyp16 hk (h29 V₀ V L hV hS h8).2
    (Set.eq_empty_of_subset_empty
      ((calO2_subset_calO 1 D.M V₀ V).trans (h30 V₀ V L hV hS h8).le))

theorem sixteen_fiftyFive (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h129 : R129_1 D) (h61 : UC6.R6_1 D) (h24 : R16_24c D) (h53 : R16_53 D) (h54 : R16_54 D) :
    R16_55 D := by
  intro V₀ V L hV hS h4
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hSg h1219 (by rw [h4.2.2]; exact Set.mem_singleton 3)
  have hW := h53 V₀ V L hV hS h4
  have hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fifteen_thirteen_a D h129 h61 hSg.nonempty (s16b_three_le D hSg)
      hS.setting.hyp16.hyp125
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW)
  exact v0_eq_bot_and_not_le_of_trichotomy D (h24 V₀ V L hV hS (Or.inr (Or.inl h4)))
    hS.setting.hyp16 hk hN (h54 V₀ V L hV hS h4)

theorem sixteen_sixtyThree (D : Data G) (hSg : UC6S846.SigmaStd D) (h129 : R129_1 D)
    (h61 : UC6.R6_1 D) (h159 : R15_9Small D) : R16_63 D := by
  intro V₀ V L hV hS hsit
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    (E3.wClos_mono D.sylowM.le).trans
      (h159 V₀ V L hsit.2 hS.setting.hyp16.small hS.ne_bot)
  exact ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.2 hW,
    fifteen_thirteen_a D h129 h61 hSg.nonempty (s16b_three_le D hSg)
      hS.setting.hyp16.hyp125 hW⟩

theorem sixteen_sixtySeven (D : Data G) (hpre : R16_67_pre D) (ha : R16_67a D) : R16_67 D := by
  intro V₀ V L hV hS hsit
  refine Set.eq_empty_of_forall_notMem fun X hX => ?_
  obtain ⟨g, rfl, hg⟩ := hX
  exact ha V₀ V L hV hS hsit g ⟨g, rfl, hg⟩ (hpre V₀ V L hV hS hsit g ⟨g, rfl, hg⟩)

theorem sixteen_sixtyEight_k (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) :
    R16_68_k D := by
  intro V₀ V L hV hS hsit
  exact hSg.sig1_sp 3 (h1219 ▸ (by rw [hsit.1.2.2.2]; exact Set.mem_singleton 3))

theorem sixteen_sixtyEight (D : Data G) (hk : R16_68_k D) (h24 : R16_24c D) (h63 : R16_63 D)
    (h67 : R16_67 D) : R16_68 D := by
  intro V₀ V L hV hS hsit
  have hk1 : D.k = 1 :=
    Data.k_eq_one_of_isStronglyPEmbedded D (hk V₀ V L hV hS hsit)
  have hsit3 : Sit1663 D V₀ V hV L := ⟨Or.inr hsit.1, hsit.2⟩
  exact v0_eq_bot_and_not_le_of_trichotomy D (h24 V₀ V L hV hS (Or.inl hsit.1))
    hS.setting.hyp16 hk1
    (h63 V₀ V L hV hS hsit3).2
    (Set.eq_empty_of_subset_empty
      ((calO2_subset_calO 1 D.M V₀ V).trans (h67 V₀ V L hV hS hsit).le))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
