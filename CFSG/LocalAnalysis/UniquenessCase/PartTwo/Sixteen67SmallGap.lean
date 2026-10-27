module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallLoc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallVtil
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified


theorem k67ThreeIndex_holds : Small.K67ThreeIndex :=
  Small.k67ThreeIndex_of_split
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S.kFactSylowSplit_holds

theorem r16_67aGap_holds (D : Data G) (hBP : Small.K67BPrimeOne) : R16_67aGap D := by
  intro hSg h1219 h61 h1217 h129 h159 V₀ V L hV hS hs h0 g hg hpre z hz2 hz
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  have hc := s1667_cfg D hSg h1219 h61 h1217 h129 h159 hS hs h0 hxM hxn
  have hg' : InCalO 1 D.M ⊥ V g := inCalO_bot_of_mem_calO hc.normalizer_eq (h0 ▸ hg)
  have hzV : z ∈ V := by
    have hzm : z ∈ V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) := by
      rw [hz]
      exact Subgroup.mem_zpowers z
    exact hzm.1.1
  have hVH : V ≤ centralizer ({z} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.2 (Small.comm_of_isElemAbelian hV hv hzV)
  have hnot := hc.not_centralizer_le hg' hz
  have hrank := s1667_pRank_centralizer D hSg h1219 h61 h1217 hS hs h0 hzV hz2 hnot
  have hse := s1667_isStronglyPEmbedded D hSg h1219 h1217 hS hs h0 hzV hnot
  obtain ⟨S, -, hSM, hSyl⟩ := s1667_exists_sylow D hSg h61 h129 h159 hS hs hzV
  have hnsup := hc.not_le_sup_relPPrimeCore hg' hz
  have hVK : ¬ V ≤ V₀ ⊔ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
    rw [h0, bot_sup_eq]
    exact hc.not_le_relPPrimeCore hg' hz
  obtain ⟨c, hcM, hcV, hc3⟩ := s1667_exists_orderOf_three D hSg h1217 hS hs h0
  have hcH : c ∈ centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV) hcV
  have hcV' : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀ := by
    intro v hv
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hcV v hv
    rw [h0, Subgroup.mem_bot, ← h1]
    group
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) := by
    intro m _
    rw [h0, Subgroup.mem_normalizer_iff]
    intro n
    simp only [Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left]
  have hL := Small.loc67_of_amb D.standing.kProper D.standing.charTwo D.standing.simple
    D.standing.nonab hz2 hV hzV (h0 ▸ bot_le) (by simp [hc.card_V, h0]) (by simp [h0])
    hc.normalizer_eq hMV₀ hrank.le hse hSyl hSM hnsup hVK hcH hcM hc3 hcV'
  have hbound := Small.coreBot hL (by rw [h0, Subgroup.bot_subgroupOf]) hBP k67ThreeIndex_holds
  rw [Small.relIndex_relPPrimeCore_eq hVH]
  exact hbound

section Ne


theorem r16_67aNeGap_holds (D : Data G) (hBP : Small.K67BPrimeOne) (hIII : Small.K67CaseIII) :
    R16_67aNeGap D := by
  intro hSg h1219 h21 h61 h1217 h129 h159 V₀ V L hV hS hsit h0 g hg hpre z hz2 hz
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D hS.setting.hyp151 hV hsit.1.2.2.1
  have hc := s1667ne_cfg D hSg h1219 h21 h61 h1217 h129 h159 hS hsit h0 hxM hxn
  have hg' : InCalO 1 D.M V₀ V g := inCalO_of_mem_calO hc.normalizer_eq hc.le_normalizer₀ hg
  have hs : InCalOStar 1 D.M V₀ V g := hc.inCalOStar hg'
  have hs' : InCalOStar 1 (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ :=
    hc.inCalOStar_conj hg'
  have hzV : z ∈ V := by
    have hzm : z ∈ V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) := by
      rw [hz]
      exact Subgroup.mem_zpowers z
    exact hzm.1.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hVH : V ≤ centralizer ({z} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.2 (Small.comm_of_isElemAbelian hV hv hzV)
  have hnot := hc.not_centralizer_le hg' hz
  have hrank := s1667ne_pRank_centralizer D hSg h1219 h21 h61 hS hsit hzV hz2 hnot
  have hse := s1667ne_isStronglyPEmbedded D hSg h1219 h21 hS hsit hzV hz1 hnot
  obtain ⟨S, -, hSM, hSyl⟩ := s1667_exists_sylow D hSg h61 h129 h159 hS hsit hzV
  have hnsup := hc.not_le_sup_relPPrimeCore hs hs' hz
  have hVK := hc.not_le_sup_V₀ hs hs' hz
  obtain ⟨c, hcH, hcM, hc3⟩ := Small.exists_orderOf_three_of_stronglyPEmbedded hse
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcH
  have hcV := hc.commutator_mem_V₀ hzV hz1 hnot hcM hc3' hcz
  have hcard₀ : Nat.card V₀ ≤ 4 :=
    Small.card_le_four_of_mSub_le_two
      (IsElemAbelian.isPGroup (Small.isElemAbelian_of_le hV hc.V₀_le))
      hS.setting.hyp16.small
  have hL := Small.loc67_of_amb D.standing.kProper D.standing.charTwo D.standing.simple
    D.standing.nonab hz2 hV hzV hc.V₀_le hc.card_V hcard₀ hc.normalizer_eq hc.le_normalizer₀
    hrank.le hse hSyl hSM hnsup hVK hcH hcM hc3 hcV
  have hbound := Small.coreC hL hBP hIII k67ThreeIndex_holds
  rw [Small.relIndex_relPPrimeCore_eq hVH]
  exact hbound

end Ne

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
