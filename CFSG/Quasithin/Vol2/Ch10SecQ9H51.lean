module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H50
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.Quasithin.Vol2.Ch10SecE21A
public import CFSG.Quasithin.Vol2.Ch10SecQ34B0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem b0_le_normalizer_of_mem_cComp (hLoc : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {T L M₁ J : Subgroup G} (hO : pCoreOf 2 M₁ ≠ ⊥)
    (hJ : J ∈ cComp M₁) (hB : B0 T L ≤ M₁) : B0 T L ≤ Subgroup.normalizer (J : Set G) := by
  have hJM : J ≤ M₁ := le_of_mem_cComp hJ
  have h121 : (J.subgroupOf M₁).Normal ∨ (conjSubgroupsBy M₁ J).ncard = 2 := by
    rcases Vol2Native.lemma_1_2_1_three hLoc h37 h38 hO hJ with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  have hself : J ∈ conjSubgroupsBy M₁ J := ⟨1, M₁.one_mem, by ext x; simp⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxX, hxo⟩
  have hxM : x ∈ M₁ := hB (Subgroup.subset_closure ⟨hxX, hxo⟩)
  exact odd_mem_normalizer_conjSubgroupsBy1516 hJM h121 hxM hxo hself

theorem exists_b0KConfig (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h1022 : Stmt10_2_2) {T L I H K : Subgroup G} {n m : ℕ} (hyp : Hyp10 G T L I)
    (h1 : Case10_1_1One T L I n) (hH : IsHStar T (fsuM T L) H) (hn : 1 < E1.nParam H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) (hK : K ∈ cComp H)
    (hHK : oTwoUpper H = conjClosure K T)
    (hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ M₁ J : Subgroup G, B0KConfig G T L I H K M₁ J n m ∧ B0 T L ≤ M₁ := by
  have := hyp.fsu.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  obtain ⟨-, h2⟩ := h1022 G T L I hyp H hH hZH
  obtain ⟨-, h3, hO⟩ := h2 (Or.inl ⟨n, h1⟩)
  obtain ⟨hB0S, -⟩ := h3 ⟨n, h1⟩
  obtain ⟨M₁, hM₁⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hTM₁ : T ≤ M₁ := (SecE.le_normalizer_baum T).trans (le_sup_left.trans hM₁.2)
  have hTS : IsSylowTwoOf T M₁ :=
    ⟨hTM₁, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow hTM₁⟩
  have hHM₁ : H ≤ M₁ := le_sup_right.trans hM₁.2
  have hKM₁ : K ≤ M₁ := (le_of_mem_cComp hK).trans hHM₁
  have hKl : K ∈ lFamily T := cComp_subset_lFamily hH.1.1 hK
  have hO₁ : pCoreOf 2 M₁ ≠ ⊥ := (inH_of_inM hM₁).2
  obtain ⟨J, hJ, hKJ⟩ := Vol2Native.lemma_1_2_4_exists hLoc h37 h39 hO₁ hTS hKM₁ hKl
  exact ⟨M₁, J, ⟨hyp, h1, hH, hn, hZH, hK, hHK, hKF, hM₁, hJ, hKJ⟩,
    hB0S.trans (le_sup_left.trans hM₁.2)⟩

theorem obl10_2_3B0K_of (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h1022 : Stmt10_2_2) (hC : B0KCases) (hA7 : B0KA7)
    (hB : B0KLie) (hD : B0KNonquasi) : Obl10_2_3B0K := by
  intro G _ _ T L I hyp n h1 H hH hn hZH K m hK hHK hKF
  obtain ⟨M₁, J, cfg, hB0M⟩ := exists_b0KConfig h37 h39 h1022 hyp h1 hH hn hZH hK hHK hKF
  rcases hC G T L I H K M₁ J n m cfg with rfl | hb | hc | hd
  · have := hyp.fsu.simple
    have hLoc : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
    exact b0_le_normalizer_of_mem_cComp hLoc h37 h38 (inH_of_inM cfg.hM₁).2 cfg.hJ hB0M
  · exact hB G T L I H K M₁ J n m cfg hb
  · exact hA7 G T L I H K M₁ J n m cfg hc
  · exact hD G T L I H K M₁ J n m cfg hd

end CFSG.Quasithin.Vol2.Ch10.SecB
