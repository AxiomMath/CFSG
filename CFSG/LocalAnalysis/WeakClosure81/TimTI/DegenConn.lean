module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenBasic
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.SpGlue
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.SUGlue
public import CFSG.RankThree.GF2n.Tim79aTransvectionHyp
public import CFSG.RankThree.GF2n.Tim79aRootTransportSU
public import CFSG.RankThree.GF2n.Tim81.Cited.OddTranspRootL2
public import CFSG.Timmesfeld.Transvection.OddBC2Rel
public import CFSG.Timmesfeld.Bridge.OddRootL2Assembly
public import CFSG.Timmesfeld.Bridge.OddRootPair
public import CFSG.Timmesfeld.Bridge.OddRootSzMainFinal
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Quot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

private theorem timti_eq_one_of_mk_eq_one (h : Hyp X S) {s w : X} (hs : s ∈ dSet S)
    (hw : w ∈ CFSG.Timmesfeld.rootGroup (dSet S) s)
    (h1 : QuotientGroup.mk' (Subgroup.center X) w = 1) : w = 1 := by
  have hw2 : w * w = 1 := CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup h.root hs hw
  have hwZ : w ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff w]
    exact h1
  have hdvd2 : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hw2)
  have hdvdC : orderOf w ∣ Nat.card (Subgroup.center X) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center X) hwZ
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with hord | hord
  · exact orderOf_eq_one_iff.mp hord
  · exfalso
    rw [hord] at hdvdC
    exact (Nat.not_even_iff_odd.mpr h.odd_card_center) (even_iff_two_dvd.mpr hdvdC)

namespace Hyp

theorem conn_rootGroupShape
    (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4)
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S))
    {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ f ∧
      IsRootGroupShape X f (CFSG.Timmesfeld.rootGroup (dSet S) s) := by
  classical
  have hP : CFSG.pCore 2 (X ⧸ Subgroup.center X) = ⊥ := by
    haveI : Group.IsNilpotent (CFSG.pCore 2 (X ⧸ Subgroup.center X)) :=
      CFSG.pCore_isPGroup.isNilpotent
    exact h.eq_bot_of_normal_isSolvable_quot _ CFSG.pCore_normal inferInstance
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    h.eq_bot_of_normal_isSolvable_quot _ inferInstance inferInstance
  have hsD : s ∈ dSet S := mem_dSet_of_mem hs hs1
  have hS : CFSG.Timmesfeld.Bridge.Asc72.Setup (X ⧸ Subgroup.center X)
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) := h.setup_quot hdeg
  have hΔ : CFSG.Timmesfeld.Transvection.TransvectionHyp (X ⧸ Subgroup.center X)
      {A | ∃ d ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S,
        A = Subgroup.closure (CFSG.Timmesfeld.rootSet
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d)} :=
    CFSG.RankThree.GF2n.Tim79a.transvectionHyp_of_connected
      CFSG.RankThree.GF2n.Tim81.oddTranspRootL2 hS hP hZ h.meetsSq_quot hconn
  obtain ⟨f, hf, hcard, hconcl⟩ :=
    CFSG.Timmesfeld.Transvection.transvectionStatement_of_oddUnitary
      CFSG.Timmesfeld.Transvection.oddUnitaryStatement_holds (X ⧸ Subgroup.center X)
      {A | ∃ d ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S,
        A = Subgroup.closure (CFSG.Timmesfeld.rootSet
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d)} hΔ
  have hWΔ : CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s) ∈
      {A | ∃ d ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S,
        A = Subgroup.closure (CFSG.Timmesfeld.rootSet
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d)} :=
    ⟨QuotientGroup.mk' (Subgroup.center X) s, ⟨s, hsD, rfl⟩, rfl⟩
  have hWcard : Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ f := by
    rw [← card_map_rootGroup h hsD, map_rootGroup h hsD]
    exact hcard _ hWΔ
  have h4 : 4 ≤ Nat.card (CFSG.Timmesfeld.rootGroup
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
      (QuotientGroup.mk' (Subgroup.center X) s)) :=
    CFSG.RankThree.GF2n.Tim79a.four_le_card_closure_rootSet hS h.meetsSq_quot
      (QuotientGroup.mk' (Subgroup.center X) s) ⟨s, hsD, rfl⟩
  rw [hcard _ hWΔ] at h4
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hfl : f = 0 ∨ f = 1 := by omega
    rcases hfl with rfl | rfl <;> norm_num at h4
  have hf0 : f ≠ 0 := by omega
  refine ⟨f, hf2, hWcard, ?_⟩
  rw [CFSG.RankThree.GF2n.Tim79a.transvectionConclusion_iff] at hconcl
  rcases hconcl with hSp | hSU
  · obtain ⟨n, Φ, a, T, hΦ, ha, hTa, hWT⟩ :=
      CFSG.RankThree.GF2n.Tim79a.exists_isTransGroup_of_transvConclusionSp hf hSp hWΔ
    obtain ⟨e, he⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.TimTI.exists_equiv_sp_of_isTransGroup Φ hΦ ha hTa
    refine Or.inl ⟨2 * n, ?_, ?_⟩
    · exact ⟨n, rfl, GaloisField 2 f, inferInstance, inferInstance,
        GaloisField.card 2 f hf0, ⟨e⟩⟩
    · refine ⟨hWcard, n, rfl, GaloisField 2 f, inferInstance, inferInstance,
        GaloisField.card 2 f hf0, e, ?_⟩
      intro w hw hw1
      have hπw : QuotientGroup.mk' (Subgroup.center X) w ∈
          (CFSG.Timmesfeld.rootGroup (dSet S) s).map
            (QuotientGroup.mk' (Subgroup.center X)) :=
        Subgroup.mem_map_of_mem _ hw
      rw [map_rootGroup h hsD] at hπw
      rw [hWT] at hπw
      obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.mp hπw
      have ht1 : t ≠ 1 := by
        intro ht1
        refine hw1 (timti_eq_one_of_mk_eq_one h hsD hw ?_)
        rw [← ht, ht1, map_one]
      have hΦw : Φ t = QuotientGroup.mk w := ht
      rw [← hΦw]
      exact he t htT ht1
  · obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, -, hTa, hWT⟩ :=
      CFSG.RankThree.GF2n.Tim79a.exists_isUTransGroup_of_transvConclusionSU hf hSU hWΔ
    obtain ⟨hLie, e, he⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.TimTI.exists_equiv_psu_of_isUTransGroup
        hf2 hm Φ hΦ hker ha hTa
    refine Or.inr (Or.inl ⟨m, hLie, ?_⟩)
    refine ⟨hWcard, GaloisField 2 (2 * f), inferInstance, inferInstance,
      CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf, e, ?_⟩
    intro w hw hw1
    have hπw : QuotientGroup.mk' (Subgroup.center X) w ∈
        (CFSG.Timmesfeld.rootGroup (dSet S) s).map
          (QuotientGroup.mk' (Subgroup.center X)) :=
      Subgroup.mem_map_of_mem _ hw
    rw [map_rootGroup h hsD] at hπw
    rw [hWT] at hπw
    obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.mp hπw
    have ht1 : t ≠ 1 := by
      intro ht1
      refine hw1 (timti_eq_one_of_mk_eq_one h hsD hw ?_)
      rw [← ht, ht1, map_one]
    have hΦw : Φ t = QuotientGroup.mk w := ht
    rw [← hΦw]
    exact he t htT ht1

theorem conn_rootGroup_sub
    (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4)
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S))
    {s : X} (hs : s ∈ dSet S) :
    ∀ w ∈ CFSG.Timmesfeld.rootGroup (dSet S) s, w ≠ 1 → w ∈ dSet S := by
  classical
  have hP : CFSG.pCore 2 (X ⧸ Subgroup.center X) = ⊥ := by
    haveI : Group.IsNilpotent (CFSG.pCore 2 (X ⧸ Subgroup.center X)) :=
      CFSG.pCore_isPGroup.isNilpotent
    exact h.eq_bot_of_normal_isSolvable_quot _ CFSG.pCore_normal inferInstance
  have hOR : CFSG.Timmesfeld.Bridge.OddRoot.Hyp (X ⧸ Subgroup.center X)
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) :=
    ⟨h.setup_quot hdeg, hP, h.meetsSq_quot, hconn⟩
  have hall : ∀ d ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S,
      ∀ x ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S, ¬ Commute d x →
        CFSG.Timmesfeld.Bridge.OddRoot.PSL2Pair
          (QuotientGroup.mk' (Subgroup.center X) '' dSet S) d x := by
    intro d hd x hx hdx
    exact CFSG.Timmesfeld.Bridge.OddRoot.psl2Pair_of_not_sqOut hOR hd hx hdx
      (CFSG.Timmesfeld.Bridge.OddRoot.noSzBelow_of
        CFSG.Timmesfeld.Bridge.OddRoot.szMainStmt (Nat.card (X ⧸ Subgroup.center X) + 1)
        (X ⧸ Subgroup.center X) (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (Nat.lt_succ_self _) hOR d hd x hx hdx)
  have hc : CFSG.Timmesfeld.RootClosure
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S) :=
    CFSG.Timmesfeld.Bridge.OddRoot.rootClosure_of_allPSL2 hOR hall
  intro w hw hw1
  have hw2 : w * w = 1 := CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup h.root hs hw
  have hπw : QuotientGroup.mk' (Subgroup.center X) w ∈
      (CFSG.Timmesfeld.rootGroup (dSet S) s).map
        (QuotientGroup.mk' (Subgroup.center X)) :=
    Subgroup.mem_map_of_mem _ hw
  rw [map_rootGroup h hs] at hπw
  have hπw1 : QuotientGroup.mk' (Subgroup.center X) w ≠ 1 :=
    fun h1 => hw1 (timti_eq_one_of_mk_eq_one h hs hw h1)
  have hπwroot : QuotientGroup.mk' (Subgroup.center X) w ∈
      CFSG.Timmesfeld.rootSet (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
        (QuotientGroup.mk' (Subgroup.center X) s) := by
    have hmem : QuotientGroup.mk' (Subgroup.center X) w ∈
        (CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
          (QuotientGroup.mk' (Subgroup.center X) s) : Set _) := hπw
    rw [CFSG.Timmesfeld.coe_rootGroup_of_rootClosure h.isRootInvolutionSet_image hc
      ⟨s, hs, rfl⟩, Set.mem_insert_iff] at hmem
    rcases hmem with h | h
    · exact absurd h hπw1
    · exact h
  exact h.mem_dSet_of_mk_mem hw2 (CFSG.Timmesfeld.rootSet_subset _ _ hπwroot)

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
