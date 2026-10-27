module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourStruct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.WClosNormalizerGen
public import CFSG.GroupTheory.E3Params
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement
open CFSG.GroupTheory (aSet_aParam_nonempty)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}

structure A5Pair18 (D : Data G) (V₀ V L K : Subgroup G) : Prop where
  data : A5Data18 D V₀ V L
  mem_calC : K ∈ calC D.M
  ne_L : K ≠ L
  alt_K : IsAlt (Bar2 K) 5
  mem_calLp : K ∈ S17.calLp D 5
  conjClosure_mem : UC22.conjClosure D.M K ∈ S17.calL0Star D 5
  calC_eq : ∀ J ∈ calC D.M, J = L ∨ J = K
  commutator_le : ⁅L, K⁆ ≤ pCoreOf 2 D.M
  dichotomy : (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
    (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal)
  three_not_mem_sig : 3 ∉ D.sig

theorem isAlt_barSub_of_isAlt_bar2 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥) (hAlt : IsAlt (Bar2 L) 5) :
    IsAlt ↥(barSub V₀ V hV.isElemAbelian L) 5 := by
  obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup hV hL hL1
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five hAlt)
  exact ⟨e.symm.trans hAlt.some⟩

theorem mBarGT_three_of_hyp18 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) : MBarGT D.M V₀ V 3 := by
  apply h1669
  have h2 : Nat.card V₀ ≤ 2 := (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
  omega

namespace A5Pair18

abbrev elemAbelian (c : A5Pair18 D V₀ V L K) : IsElemAbelian 2 V :=
  c.data.hyp.hyp125.isElemAbelian

theorem mem_calC_L (c : A5Pair18 D V₀ V L K) : L ∈ calC D.M := c.data.hyp.hL.1

theorem wOne_commute (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h111 : W3Thm111 G) (ha2 : aBar D.M ⊥ V c.elemAbelian ≤ 2) :
    ⁅E3.wClos V 1 D.T, V⁆ = ⊥ := by
  subst hV₀
  have h3 : MBarGT D.M ⊥ V 3 :=
    mBarGT_three_of_hyp18 D c.data.hyp h1669
  have hm4 : 3 < mBar D.M ⊥ V c.elemAbelian := (c.data.hyp.hyp125.mBarGT_iff_lt_mBar 3).1 h3
  have hm2 : MBarGT D.M ⊥ V 2 := (c.data.hyp.hyp125.mBarGT_iff_lt_mBar 2).2 (by omega)
  exact commutator_wClos_eq_bot_of_lt D h111 c.data.hyp.hyp125 hm2 (by omega)

theorem normalizer_wi_one (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) (hx : DataExt D)
    (h127 : R127 D) (h61 : UC6.R6_1 D) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h111 : W3Thm111 G)
    (ha2 : aBar D.M ⊥ V c.elemAbelian ≤ 2) :
    normalizer (F12.Wi 1 D.T V : Set G) ≤ D.M ∧
      UniqueMax D.M (D.M ⊓ normalizer (F12.Wi 1 D.T V : Set G)) := by
  subst hV₀
  have hW : E3.wClos V 1 D.T ≤ centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (c.wOne_commute rfl h1669 h111 ha2)
  have hWne : E3.wClos V 1 D.T ≠ ⊥ := by
    have hd : Nat.card V = 2 ^ rk ↥V :=
      card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian c.elemAbelian)
    have h4 : 4 ≤ Nat.card V := four_le_card_V_of_hyp125 D c.data.hyp.hyp125
    have hrk : 1 < rk ↥V := by
      rw [hd] at h4
      by_contra hcon
      have h2 : 2 ^ rk ↥V ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact E3.wClos_ne_bot c.elemAbelian (s15_13A_le_T c.data.hyp.hyp125) hrk
  have hrk : ∀ q ∈ D.sig, 3 ≤ CFSG.pRank q ↥D.M := by
    intro q hq
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hx.three_le q hq
  have h := normalizer_wClos_le_of_le_centralizer D (r129_1_of_r127 D h127) h61
    hx.sig_nonempty hrk c.data.hyp.hyp125 1 hW hWne
  rwa [S17.Wi_eq_wClos 1 D.T V c.elemAbelian]

theorem le_cClos_of_commutator_eq_bot (c : A5Pair18 D V₀ V L K) {i : ℕ}
    (hW : ⁅E3.wClos V i D.T, V⁆ = ⊥) : V ≤ E3.cClos V i D.T :=
  le_inf (s15_13A_le_T c.data.hyp.hyp125)
    (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW))

theorem numerics (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) (hx : DataExt D)
    (h127 : R127 D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h111 : W3Thm111 G) (ha2 : aBar D.M ⊥ V c.elemAbelian ≤ 2) :
    mBar D.M ⊥ V c.elemAbelian = 4 ∧ aBar D.M ⊥ V c.elemAbelian = 2 ∧ D.k = 2 ∧
      ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M := by
  subst hV₀
  have hp := c.data.hyp.hyp125
  have hrk : ∀ q ∈ D.sig, 3 ≤ CFSG.pRank q ↥D.M := by
    intro q hq
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hx.three_le q hq
  have h3 : MBarGT D.M ⊥ V 3 :=
    mBarGT_three_of_hyp18 D c.data.hyp h1669
  have hm4 : 3 < mBar D.M ⊥ V c.elemAbelian := (hp.mBarGT_iff_lt_mBar 3).1 h3
  have hm2 : MBarGT D.M ⊥ V 2 := (hp.mBarGT_iff_lt_mBar 2).2 (by omega)
  have hW0 : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ :=
    commutator_wClos_eq_bot_of_lt D h111 hp hm2 (by omega)
  have hNW0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
    have hW0' : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW0
    have hne : E3.wClos V 0 D.T ≠ ⊥ := fun hb =>
      hp.pairFacts.ne_bot (le_bot_iff.1 (hb ▸ s15_13A_le_wClos hp))
    exact (normalizer_wClos_le_of_le_centralizer D (r129_1_of_r127 D h127) h61
      hx.sig_nonempty hrk hp 0 hW0' hne).1
  have hmk : MBarGT D.M ⊥ V D.k := by
    refine (hp.mBarGT_iff_lt_mBar D.k).2 ?_
    have := TwelveSeven.k_le_two D
    omega
  have hle : mBar D.M ⊥ V c.elemAbelian ≤ aBar D.M ⊥ V c.elemAbelian + 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have hW2 : ⁅E3.wClos V 2 D.T, V⁆ = ⊥ :=
      commutator_wClos_eq_bot_of_lt D h111 hp hm2 (by omega)
    have hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥ :=
      commutator_wClos_eq_bot_of_lt D h111 hp hm2 (by omega)
    have hCk : centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := by
      rcases Nat.lt_or_ge D.k 2 with hk | hk
      · have hk1 : D.k = 1 := by have := TwelveShort.one_le_k D; omega
        rw [hk1]
        exact (Subgroup.centralizer_le (c.le_cClos_of_commutator_eq_bot hW1)).trans
          (centralizer_le_of_inCalV D hp.inCalV)
      · have hk2 : D.k = 2 := by have := TwelveSeven.k_le_two D; omega
        rw [hk2]
        exact centralizer_cClos_le_of_commutator_eq_bot D hp hW2
    rcases twelve_ten_two D hx h61 h126 h111 hp rfl (i := 0) (by simpa using hmk) with h | h
    · exact h hNW0
    · exact h hCk
  have hmeq : mBar D.M ⊥ V c.elemAbelian = 4 := by omega
  have haeq : aBar D.M ⊥ V c.elemAbelian = 2 := by omega
  have hkeq : D.k = 2 := by
    rcases Nat.lt_or_ge D.k 2 with hk | hk
    · exfalso
      have hk1 : D.k = 1 := by have := TwelveShort.one_le_k D; omega
      rcases twelve_ten_two D hx h61 h126 h111 hp rfl (i := 0) (by simpa using hmk) with h | h
      · exact h hNW0
      · refine h ?_
        rw [hk1]
        exact (Subgroup.centralizer_le (c.le_cClos_of_commutator_eq_bot
          (commutator_wClos_eq_bot_of_lt D h111 hp hm2 (by omega)))).trans
          (centralizer_le_of_inCalV D hp.inCalV)
    · have := TwelveSeven.k_le_two D; omega
  refine ⟨hmeq, haeq, hkeq, ?_⟩
  rcases twelve_ten_two D hx h61 h126 h111 hp rfl (i := 0) (by simpa using hmk) with h | h
  · exact absurd hNW0 h
  · simpa [hkeq] using h

theorem barSub_ne_bot (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) (h127 : R127 D)
    (hU : UniqueMax D.M (L ⊔ F12.Wi 1 D.T V) ∧ UniqueMax D.M (K ⊔ F12.Wi 1 D.T V))
    (hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥) :
    barSub ⊥ V c.elemAbelian L ≠ ⊥ ∧ barSub ⊥ V c.elemAbelian K ≠ ⊥ := by
  subst hV₀
  have hp := c.data.hyp.hyp125
  have hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V := (twelve_nine D h127 hp).1
  have hW1c : F12.Wi 1 D.T V ≤ centralizer (V : Set G) := by
    rw [S17.Wi_eq_wClos 1 D.T V c.elemAbelian]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW1
  have key : ∀ X : Subgroup G, X ≤ D.M → UniqueMax D.M (X ⊔ F12.Wi 1 D.T V) →
      barSub ⊥ V c.elemAbelian X ≠ ⊥ := by
    intro X hXM hXU hb
    apply hTI
    have hXC : X ≤ centralizer (V : Set G) := by
      have h := (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff c.elemAbelian
        hp.pairFacts.le_normalizer hp.pairFacts.le_normalizer₀ hXM).1 hb
      rw [uc22p22u_cTilde_bot] at h
      exact h.trans inf_le_right
    exact uc22p22u_isTI_of_uniqueMax D c.elemAbelian hp.pairFacts.le_normalizer
      (sup_le hXC hW1c) hXU
  exact ⟨key L c.mem_calC_L.1.le hU.1, key K c.mem_calC.1.le hU.2⟩

theorem sup_normal (c : A5Pair18 D V₀ V L K) : ((L ⊔ K).subgroupOf D.M).Normal := by
  have hLKM : L ⊔ K ≤ D.M := sup_le c.mem_calC_L.1.le c.mem_calC.1.le
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hLKM).mpr ?_
  rcases c.dichotomy with ⟨hX, -⟩ | ⟨-, hLn, hKn⟩
  · rw [← hX]
    exact (conjSetOf_subset_calC_conjClosure c.mem_calC_L).2.1
  · refine (le_inf ?_ ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup L K)
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC_L.1.le).mp hLn
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).mp hKn

end A5Pair18

namespace A5Data18

theorem aBar_le_two_of_isAlt {D : Data G} {V L K : Subgroup G}
    (c : A5Data18 D ⊥ V L)
    (hV : IsElemAbelian 2 V) (hMV : D.M ≤ normalizer (V : Set G))
    (hH : F11.Hyp11 D ⊥ V) (h119 : R119W D)
    (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hLalt : IsAlt (Bar2 L) 5) (hKalt : IsAlt (Bar2 K) 5)
    (hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1)
    (hO2 : Inputs1719.O2Trivial (Mbar D.M ⊥ V hV))
    (h77 : Inputs1719.W4Lem7_7) :
    aBar D.M ⊥ V hV ≤ 2 := by
  have hcomp := c.compBar_subset rfl hV hMV hH h119 hK hKne
  rw [aBar]
  refine (aParam_le_of_components hW h77 hO2 (by norm_num) ?_).1
  intro K' hK' k hk
  rcases hcomp K' hK' with h | h
  · rw [h] at hk
    have hne : barSub ⊥ V hV L ≠ ⊥ := by
      rw [← h]
      exact ne_bot_of_mem_compBar hK'
    exact aCandidate_le_two_of_isAlt_five
      (isAlt_barSub_of_isAlt_bar2 c.hyp.hyp125 c.hyp.hL.1 hne hLalt) k hk
  · rw [h] at hk
    have hne : barSub ⊥ V hV K ≠ ⊥ := by
      rw [← h]
      exact ne_bot_of_mem_compBar hK'
    exact aCandidate_le_two_of_isAlt_five
      (isAlt_barSub_of_isAlt_bar2 c.hyp.hyp125 hK hne hKalt) k hk

theorem aBar_eq_max_of_isAlt {D : Data G} {V L K : Subgroup G}
    (c : A5Data18 D ⊥ V L)
    (hV : IsElemAbelian 2 V) (hMV : D.M ≤ normalizer (V : Set G))
    (hH : F11.Hyp11 D ⊥ V) (h119 : R119W D)
    (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hLalt : IsAlt (Bar2 L) 5) (hKalt : IsAlt (Bar2 K) 5)
    (hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1)
    (hO2 : Inputs1719.O2Trivial (Mbar D.M ⊥ V hV))
    (h77 : Inputs1719.W4Lem7_7)
    (ha : aBar D.M ⊥ V hV = 2) :
    aBar D.M ⊥ V hV = max (bBar L D.M ⊥ V hV) (bBar K D.M ⊥ V hV) := by
  have hcomp := c.compBar_subset rfl hV hMV hH h119 hK hKne
  have hn : ∀ K' : Subgroup (MulAut (Vtil ⊥ V hV)),
      CFSG.Open.IsComponentOf K' (Mbar D.M ⊥ V hV) →
      ∀ k, Nonempty (Inputs1719.ACandidate ↥K' k) → k ≤ 2 := by
    intro K' hK' k hk
    rcases hcomp K' hK' with h | h
    · rw [h] at hk
      have hne : barSub ⊥ V hV L ≠ ⊥ := by
        rw [← h]
        exact ne_bot_of_mem_compBar hK'
      exact aCandidate_le_two_of_isAlt_five
        (isAlt_barSub_of_isAlt_bar2 c.hyp.hyp125 c.hyp.hL.1 hne hLalt) k hk
    · rw [h] at hk
      have hne : barSub ⊥ V hV K ≠ ⊥ := by
        rw [← h]
        exact ne_bot_of_mem_compBar hK'
      exact aCandidate_le_two_of_isAlt_five
        (isAlt_barSub_of_isAlt_bar2 c.hyp.hyp125 hK hne hKalt) k hk
  have hle2 : aBar D.M ⊥ V hV ≤ 2 :=
    c.aBar_le_two_of_isAlt hV hMV hH h119 hK hKne hLalt hKalt hW hO2 h77
  apply le_antisymm
  · have hpos : 0 < E3.aParam (Mbar D.M ⊥ V hV) := by
      unfold aBar at ha
      omega
    have hne := aSet_aParam_nonempty (X := Mbar D.M ⊥ V hV) hpos
    have hA2 : ∃ A, A ∈ E3.aSet 2 (Mbar D.M ⊥ V hV) := by
      obtain ⟨A, hA⟩ := hne
      refine ⟨A, ?_⟩
      unfold aBar at ha
      rwa [ha] at hA
    obtain ⟨A, hA2⟩ := hA2
    have hAne : A ≠ ⊥ := hA2.2.1
    obtain ⟨K', hK'comp, hK'comm⟩ :=
      (aParam_le_of_components hW h77 hO2 (by norm_num : 2 ≤ 2) hn).2 A hA2 hAne
    have hb : 2 ≤ max (bBar L D.M ⊥ V hV) (bBar K D.M ⊥ V hV) := by
      rcases hcomp K' hK'comp with h | h
      · rw [h] at hK'comm
        rw [Subgroup.commutator_comm] at hK'comm
        have h2 : 2 ≤ bBar L D.M ⊥ V hV := by
          rw [bBar]
          exact le_bParam (by norm_num : 0 < 2) hA2 hK'comm
        exact h2.trans (le_max_left _ _)
      · rw [h] at hK'comm
        rw [Subgroup.commutator_comm] at hK'comm
        have h2 : 2 ≤ bBar K D.M ⊥ V hV := by
          rw [bBar]
          exact le_bParam (by norm_num : 0 < 2) hA2 hK'comm
        exact h2.trans (le_max_right _ _)
    rw [ha]
    exact hb
  · apply max_le
    · rw [bBar]
      exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.bParam_le_aParam
        (X := barSub ⊥ V hV L) (Y := Mbar D.M ⊥ V hV)
    · rw [bBar]
      exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.bParam_le_aParam
        (X := barSub ⊥ V hV K) (Y := Mbar D.M ⊥ V hV)

theorem xCond1218_conjClosure_of_data (c : A5Data18 D V₀ V L) (hV₀ : V₀ ≠ ⊥) (j : ℕ) :
    XCond1218 D.M V₀ V c.hyp.hyp125.isElemAbelian j (UC22.conjClosure D.M L) :=
  TwelveTwentyThree.xCond1218_conjClosure c.hyp.hyp125 hV₀ c.hyp.hL.1.1 c.hyp.hL.1.2.2 j

theorem conjClosure_normal (c : A5Data18 D V₀ V L) :
    ((UC22.conjClosure D.M L).subgroupOf D.M).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp.X_le_M).mpr ?_
  exact (conjSetOf_subset_calC_conjClosure c.hyp.hL.1).2.1

theorem inFSq_conjClosure_sup (c : A5Data18 D V₀ V L) (h43c : W3Lem45_2Chief)
    (hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L))
    (hgen : orbitClosure (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) L)
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T) ⊔
      imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T = ⊤)
    (hcf : ∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T') :
    CFSG.LocalAnalysis.WeakClosure81.InFSq (S17.nOf L)
      (UC22.conjClosure D.M L ⊔ D.T) :=
  inFSq_conjClosure_sup_of_components c.hyp.hL.1 h43c hL2 hgen hcf

end A5Data18

theorem inFSq_sup_T_of_normal {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M)
    (hLn : (L.subgroupOf D.M).Normal) (hAlt : IsAlt (Bar2 L) 5)
    (hKc : K_L2SzAutRank) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 2 (L ⊔ D.T) := by
  have hLH : L ≤ L ⊔ D.T := le_sup_left
  have hHM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hNM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).mp hLn
  have hKn : (L.subgroupOf (L ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr (hHM.trans hNM)
  have hTsyl : IsSylowIn 2 D.T (L ⊔ D.T) := TwelveShort.isSylowIn_of_le D le_sup_right
  have hperf : ⁅L, L⁆ = L := hL.2.1
  have hL2 : IsL2 (Bar2 L) 2 := by
    obtain ⟨e⟩ := hAlt
    exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e
  exact inFSq_of_isL2_of_normal_sup hLH hKn hTsyl rfl hperf hL2 hKc

theorem pRank_five_sup_eq_two_of_calC {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hLalt : IsAlt (Bar2 L) 5) (hKalt : IsAlt (Bar2 K) 5)
    (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M) :
    CFSG.Open.pRank 5 (L ⊔ K) = 2 := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hA5 : S17.IsA5xA5 ↥(barImage D.M (L ⊔ K)) :=
    isA5xA5_barImage_sup_of_calC hL hK hKne hLalt hKalt
      (CFSG.Quasithin.modO2Image_commute hcomm)
  rw [← s13_pRank_barImage (p := 5) Nat.prime_five (by norm_num) (sup_le hLM hKM),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact S17.pRank_eq_two_of_isA5xA5 hA5 (Or.inr rfl)

@[expose] def Gap_18_4_Delta (D : Data G) (V₀ V L : Subgroup G)
    (c : A5Data18 D V₀ V L) : Prop :=
  V₀ ≠ ⊥ → ∃ (j : ℕ) (Δ : Set (Subgroup G)), Hyp1222 D V₀ V L j Δ ∧
    (UC22.conjClosure D.M L ⊔ D.T ∈ Δ) ∧
    (∀ H ∈ Δ, ((S17.oUpperTwo H).subgroupOf D.M).Normal) ∧
    (∀ K : Subgroup G, D.T ≤ K → K ≤ ⨆ H ∈ Δ, H →
      barSub V₀ V c.hyp.hyp125.isElemAbelian K =
        ⨆ H ∈ Δ, barSub V₀ V c.hyp.hyp125.isElemAbelian H →
      calMOf K = {D.M}) ∧
    fIndexMax Δ ≤ 2

namespace A5Data18

theorem v0_eq_bot (c : A5Data18 D V₀ V L) (h182 : R18_2At D V₀ V 5 L c.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c) : V₀ = ⊥ := by
  by_contra hV₀
  obtain ⟨j, Δ, h12, hXT, hO2, hcl, hidx⟩ := hg hV₀
  have h3 : MBarGT D.M V₀ V 3 :=
    mBarGT_three_of_hyp18 D c.hyp h1669
  have hm4 : 3 < mBar D.M V₀ V c.hyp.hyp125.isElemAbelian :=
    (c.hyp.hyp125.mBarGT_iff_lt_mBar 3).1 h3
  have hle : (mBar D.M V₀ V c.hyp.hyp125.isElemAbelian : ℕ∞) ≤ fIndexMax Δ + 1 :=
    h182 hV₀ j Δ h12 hXT hO2 hcl
  have h2 : fIndexMax Δ ≤ (2 : ℕ∞) := hidx
  have hchain : (mBar D.M V₀ V c.hyp.hyp125.isElemAbelian : ℕ∞) ≤ (3 : ℕ∞) := by
    calc (mBar D.M V₀ V c.hyp.hyp125.isElemAbelian : ℕ∞) ≤ fIndexMax Δ + 1 := hle
      _ ≤ 2 + 1 := by gcongr
      _ = 3 := by norm_num
  have h4 : (4 : ℕ∞) ≤ (mBar D.M V₀ V c.hyp.hyp125.isElemAbelian : ℕ∞) := by
    exact_mod_cast (show 4 ≤ mBar D.M V₀ V c.hyp.hyp125.isElemAbelian by omega)
  have : (4 : ℕ∞) ≤ (3 : ℕ∞) := h4.trans hchain
  norm_num at this

end A5Data18

namespace A5Pair18

theorem fixV_eq_bot (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) (h61 : UC6.R6_1 D)
    (hU : UniqueMax D.M (L ⊔ F12.Wi 1 D.T V))
    (hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥)
    (hnum : ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M) :
    fixV (barSub ⊥ V c.elemAbelian (L ⊔ K)) = ⊥ := by
  subst hV₀
  have hp := c.data.hyp.hyp125
  have hpF := hp.pairFacts
  have hVT : V ≤ D.T := s15_13A_le_T hp
  have hLKM : L ⊔ K ≤ D.M := sup_le c.mem_calC_L.1.le c.mem_calC.1.le
  have hNK : D.M ≤ normalizer (((L ⊔ K) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLKM).mp c.sup_normal
  have hE : L ⊔ K ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil (hLKM.trans hpF.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hCe : preTil ⊥ V c.elemAbelian (fixV (barSub ⊥ V c.elemAbelian (L ⊔ K))) =
      V ⊓ centralizer (((L ⊔ K) : Subgroup G) : Set G) := by
    ext w
    constructor
    · intro hw
      have hwV : w ∈ V := preTil_le ⊥ V c.elemAbelian _ hw
      refine Subgroup.mem_inf.2 ⟨hwV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hall := (s15_Glue_mem_preTil_fixV_iff ⊥ V (L ⊔ K) c.elemAbelian hE hwV).1 hw e he
      rw [Subgroup.mem_bot] at hall
      have h1 : e * w * e⁻¹ = w := mul_inv_eq_one.1 hall
      calc e * w = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [h1]
    · rintro hw
      obtain ⟨hwV, hwc⟩ := Subgroup.mem_inf.1 hw
      refine (s15_Glue_mem_preTil_fixV_iff ⊥ V (L ⊔ K) c.elemAbelian hE hwV).2 fun e he => ?_
      rw [Subgroup.mem_bot]
      have hcomm : e * w = w * e := Subgroup.mem_centralizer_iff.1 hwc e he
      calc e * w * e⁻¹ * w⁻¹ = (e * w) * (w * e)⁻¹ := by rw [mul_inv_rev]; group
        _ = (e * w) * (e * w)⁻¹ := by rw [hcomm]
        _ = 1 := mul_inv_cancel _
  by_contra hfix
  have hCne : V ⊓ centralizer (((L ⊔ K) : Subgroup G) : Set G) ≠ ⊥ := by
    rw [← hCe]
    intro h
    apply hfix
    have h2 := congrArg (imgTil ⊥ V c.elemAbelian) h
    rw [imgTil_preTil] at h2
    have hbot : imgTil ⊥ V c.elemAbelian (⊥ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V c.elemAbelian (⊥ : Subgroup G) q).1 hq
      have hx1 : x = 1 := IntMod.val_injective (by simpa using hx)
      rw [hx1, map_one]
      exact Subgroup.one_mem _
    rw [hbot] at h2
    exact h2
  set Cc : Subgroup G := V ⊓ centralizer (((L ⊔ K) : Subgroup G) : Set G) with hCc
  have hCcT : Cc ≤ D.T := fun x hx => hVT (Subgroup.mem_inf.1 hx).1
  have hCcN : (Cc.subgroupOf D.T).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCcT).mpr ?_
    rw [hCc]
    exact D.sylowM.le.trans (A1a.le_normalizer_inf hpF.le_normalizer
      (A1a.le_normalizer_centralizer hNK))
  have hCcne : Cc.subgroupOf D.T ≠ ⊥ := by
    intro h
    apply hCne
    have h' := congrArg (Subgroup.map (D.T).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hCcT, Subgroup.map_bot] at h'
  have : Group.IsNilpotent ↥D.T := IsPGroup.isNilpotent D.sylowM.isPGroup
  have : (Cc.subgroupOf D.T).Normal := hCcN
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hCcne)
  have hzCc : (z : G) ∈ Cc := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 z.2).1
  have hzC : (z : G) ∈ centralizer (((L ⊔ K) : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.1 hzCc).2
  have hzV : (z : G) ∈ V := (Subgroup.mem_inf.1 hzCc).1
  have hzc : ∀ t ∈ D.T, (z : G) * t = t * (z : G) := by
    intro t ht
    have h1 := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2 (⟨t, ht⟩ : ↥D.T)
    exact (congrArg Subtype.val h1).symm
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hz2 : (z : G) ^ 2 = 1 := hpF.elemAbelian.2 _ hzV
  have hLKz : L ⊔ F12.Wi 1 D.T V ≤ centralizer ({(z : G)} : Set G) := by
    have hLz : L ≤ centralizer ({(z : G)} : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact (Subgroup.mem_centralizer_iff.1 hzC e (Subgroup.mem_sup_left he)).symm
    have hWz : F12.Wi 1 D.T V ≤ centralizer ({(z : G)} : Set G) := by
      have hWV : F12.Wi 1 D.T V ≤ centralizer (V : Set G) := by
        rw [S17.Wi_eq_wClos 1 D.T V c.elemAbelian]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW1
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact Subgroup.mem_centralizer_iff.1 (hWV hw) z hzV
    exact sup_le hLz hWz
  have hCGz : centralizer ({(z : G)} : Set G) ≤ D.M :=
    uc22p22p_le_of_uniqueMax hU (uc22p22u_isTwoLocal_centralizer hz1 hz2) hLKz
  refine hnum ?_
  refine (Subgroup.centralizer_le ?_).trans hCGz
  refine Set.singleton_subset_iff.2 ?_
  exact mem_cClos_of_mem_center D V 2 (z : ↥D.T).2 hzc

theorem fixV_barSub_eq_bot_of_normal (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥)
    {J : Subgroup G} (hJM : J ≤ D.M) (hJn : (J.subgroupOf D.M).Normal)
    (hU : UniqueMax D.M (J ⊔ F12.Wi 1 D.T V))
    (hnum : ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M) :
    fixV (barSub ⊥ V c.elemAbelian J) = ⊥ := by
  subst hV₀
  have hp := c.data.hyp.hyp125
  have hpF := hp.pairFacts
  have hVT : V ≤ D.T := s15_13A_le_T hp
  have hNK : D.M ≤ normalizer ((J : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJM).mp hJn
  have hE : J ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil (hJM.trans hpF.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hCe : preTil ⊥ V c.elemAbelian (fixV (barSub ⊥ V c.elemAbelian J)) =
      V ⊓ centralizer ((J : Subgroup G) : Set G) := by
    ext w
    constructor
    · intro hw
      have hwV : w ∈ V := preTil_le ⊥ V c.elemAbelian _ hw
      refine Subgroup.mem_inf.2 ⟨hwV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hall := (s15_Glue_mem_preTil_fixV_iff ⊥ V J c.elemAbelian hE hwV).1 hw e he
      rw [Subgroup.mem_bot] at hall
      have h1 : e * w * e⁻¹ = w := mul_inv_eq_one.1 hall
      calc e * w = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [h1]
    · rintro hw
      obtain ⟨hwV, hwc⟩ := Subgroup.mem_inf.1 hw
      refine (s15_Glue_mem_preTil_fixV_iff ⊥ V J c.elemAbelian hE hwV).2 fun e he => ?_
      rw [Subgroup.mem_bot]
      have hcomm : e * w = w * e := Subgroup.mem_centralizer_iff.1 hwc e he
      calc e * w * e⁻¹ * w⁻¹ = (e * w) * (w * e)⁻¹ := by rw [mul_inv_rev]; group
        _ = (e * w) * (e * w)⁻¹ := by rw [hcomm]
        _ = 1 := mul_inv_cancel _
  by_contra hfix
  have hCne : V ⊓ centralizer ((J : Subgroup G) : Set G) ≠ ⊥ := by
    rw [← hCe]
    intro h
    apply hfix
    have h2 := congrArg (imgTil ⊥ V c.elemAbelian) h
    rw [imgTil_preTil] at h2
    have hbot : imgTil ⊥ V c.elemAbelian (⊥ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V c.elemAbelian (⊥ : Subgroup G) q).1 hq
      have hx1 : x = 1 := IntMod.val_injective (by simpa using hx)
      rw [hx1, map_one]
      exact Subgroup.one_mem _
    rw [hbot] at h2
    exact h2
  set Cc : Subgroup G := V ⊓ centralizer ((J : Subgroup G) : Set G) with hCc
  have hCcT : Cc ≤ D.T := fun x hx => hVT (Subgroup.mem_inf.1 hx).1
  have hCcN : (Cc.subgroupOf D.T).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCcT).mpr ?_
    rw [hCc]
    exact D.sylowM.le.trans (A1a.le_normalizer_inf hpF.le_normalizer
      (A1a.le_normalizer_centralizer hNK))
  have hCcne : Cc.subgroupOf D.T ≠ ⊥ := by
    intro h
    apply hCne
    have h' := congrArg (Subgroup.map (D.T).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hCcT, Subgroup.map_bot] at h'
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (@Group.IsNilpotent.inf_center_ne_bot_of_normal ↥D.T _
      (IsPGroup.isNilpotent D.sylowM.isPGroup) (Cc.subgroupOf D.T) hCcN hCcne)
  have hzCc : (z : G) ∈ Cc := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 z.2).1
  have hzC : (z : G) ∈ centralizer ((J : Subgroup G) : Set G) := (Subgroup.mem_inf.1 hzCc).2
  have hzV : (z : G) ∈ V := (Subgroup.mem_inf.1 hzCc).1
  have hzc : ∀ t ∈ D.T, (z : G) * t = t * (z : G) := by
    intro t ht
    have h1 := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2 (⟨t, ht⟩ : ↥D.T)
    exact (congrArg Subtype.val h1).symm
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hz2 : (z : G) ^ 2 = 1 := hpF.elemAbelian.2 _ hzV
  have hJz : J ⊔ F12.Wi 1 D.T V ≤ centralizer ({(z : G)} : Set G) := by
    have hLz : J ≤ centralizer ({(z : G)} : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact (Subgroup.mem_centralizer_iff.1 hzC e he).symm
    have hWz : F12.Wi 1 D.T V ≤ centralizer ({(z : G)} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hzc w ((S17.Wi_eq_wClos 1 D.T V c.elemAbelian).le.trans (E3.wClos_le 1 D.T) hw)
    exact sup_le hLz hWz
  have hCGz : centralizer ({(z : G)} : Set G) ≤ D.M :=
    uc22p22p_le_of_uniqueMax hU (uc22p22u_isTwoLocal_centralizer hz1 hz2) hJz
  refine hnum ?_
  refine (Subgroup.centralizer_le ?_).trans hCGz
  refine Set.singleton_subset_iff.2 ?_
  exact mem_cClos_of_mem_center D V 2 (z : ↥D.T).2 hzc

end A5Pair18

namespace A5Pair18

theorem v0_eq_bot (c : A5Pair18 D V₀ V L K) (h182 : R18_2At D V₀ V 5 L c.data.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c.data) : V₀ = ⊥ :=
  A5Data18.v0_eq_bot c.data h182 h1669 hg

theorem aBar_le_two_gen (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) (h127 : R127 D)
    (h119 : R119W D) (h77 : W4Lem7_7) :
    aBar D.M ⊥ V c.elemAbelian ≤ 2 := by
  subst hV₀
  exact c.data.aBar_le_two_of_isAlt c.elemAbelian
    c.data.hyp.hyp125.pairFacts.le_normalizer (Hyp125.hyp11 h127 c.data.hyp.hyp125)
    h119 c.mem_calC c.ne_L c.data.alt c.alt_K
    (s15_Infra_vtil_sq_eq_one ⊥ V c.elemAbelian)
    (fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.data.hyp.hyp125 hP hN h2)
    h77

theorem bBar_le_two_gen (c : A5Pair18 D V₀ V L K) (ha : aBar D.M ⊥ V c.elemAbelian ≤ 2) :
    bBar L D.M ⊥ V c.elemAbelian ≤ 2 ∧ bBar K D.M ⊥ V c.elemAbelian ≤ 2 := by
  rw [aBar] at ha
  exact ⟨by rw [bBar]; exact bParam_le_aParam.trans ha,
    by rw [bBar]; exact bParam_le_aParam.trans ha⟩

theorem aBar_eq_max_gen (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) (h127 : R127 D)
    (h119 : R119W D) (h77 : W4Lem7_7) (ha : aBar D.M ⊥ V c.elemAbelian = 2) :
    aBar D.M ⊥ V c.elemAbelian =
      max (bBar L D.M ⊥ V c.elemAbelian) (bBar K D.M ⊥ V c.elemAbelian) := by
  subst hV₀
  exact c.data.aBar_eq_max_of_isAlt c.elemAbelian
    c.data.hyp.hyp125.pairFacts.le_normalizer (Hyp125.hyp11 h127 c.data.hyp.hyp125)
    h119 c.mem_calC c.ne_L c.data.alt c.alt_K
    (s15_Infra_vtil_sq_eq_one ⊥ V c.elemAbelian)
    (fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.data.hyp.hyp125 hP hN h2)
    h77 ha

theorem wOne_commute_gen (c : A5Pair18 D V₀ V L K)
    (h182 : R18_2At D V₀ V 5 L c.data.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c.data) (h111 : W3Thm111 G) (h127 : R127 D)
    (h119 : R119W D) (h77 : W4Lem7_7) :
    ⁅E3.wClos V 1 D.T, V⁆ = ⊥ := by
  have hV₀ := c.v0_eq_bot h182 h1669 hg
  exact c.wOne_commute hV₀ h1669 h111 (c.aBar_le_two_gen hV₀ h127 h119 h77)

theorem normalizer_wi_one_gen (c : A5Pair18 D V₀ V L K)
    (h182 : R18_2At D V₀ V 5 L c.data.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c.data) (hx : DataExt D) (h127 : R127 D)
    (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) (h119 : R119W D) (h77 : W4Lem7_7) :
    normalizer (F12.Wi 1 D.T V : Set G) ≤ D.M ∧
      UniqueMax D.M (D.M ⊓ normalizer (F12.Wi 1 D.T V : Set G)) := by
  have hV₀ := c.v0_eq_bot h182 h1669 hg
  exact c.normalizer_wi_one hV₀ hx h127 h61 h1669 h111
    (c.aBar_le_two_gen hV₀ h127 h119 h77)

theorem numerics_gen (c : A5Pair18 D V₀ V L K)
    (h182 : R18_2At D V₀ V 5 L c.data.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c.data) (hx : DataExt D) (h127 : R127 D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G) (h119 : R119W D)
    (h77 : W4Lem7_7) :
    mBar D.M ⊥ V c.elemAbelian = 4 ∧ aBar D.M ⊥ V c.elemAbelian = 2 ∧ D.k = 2 ∧
      ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M := by
  have hV₀ := c.v0_eq_bot h182 h1669 hg
  exact c.numerics hV₀ hx h127 h61 h126 h1669 h111 (c.aBar_le_two_gen hV₀ h127 h119 h77)

theorem barSub_ne_bot_gen (c : A5Pair18 D V₀ V L K)
    (h182 : R18_2At D V₀ V 5 L c.data.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c.data) (h127 : R127 D)
    (hU : UniqueMax D.M (L ⊔ F12.Wi 1 D.T V) ∧
      UniqueMax D.M (K ⊔ F12.Wi 1 D.T V))
    (hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥) :
    barSub ⊥ V c.elemAbelian L ≠ ⊥ ∧ barSub ⊥ V c.elemAbelian K ≠ ⊥ :=
  c.barSub_ne_bot (c.v0_eq_bot h182 h1669 hg) h127 hU hW1

theorem fixV_eq_bot_gen (c : A5Pair18 D V₀ V L K)
    (h182 : R18_2At D V₀ V 5 L c.data.hyp)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hg : Gap_18_4_Delta D V₀ V L c.data) (h61 : UC6.R6_1 D)
    (hU : UniqueMax D.M (L ⊔ F12.Wi 1 D.T V))
    (hW1 : ⁅E3.wClos V 1 D.T, V⁆ = ⊥)
    (hnum : ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M) :
    fixV (barSub ⊥ V c.elemAbelian (L ⊔ K)) = ⊥ :=
  c.fixV_eq_bot (c.v0_eq_bot h182 h1669 hg) h61 hU hW1 hnum




end A5Pair18

theorem bParam_map_congr {V W : Type*} [CommGroup V] [CommGroup W] [Finite V] [Finite W]
    (e : V ≃* W) (X Y : Subgroup (MulAut V)) :
    bParam (X.map (MulAut.congr e).toMonoidHom) (Y.map (MulAut.congr e).toMonoidHom) =
      bParam X Y := by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hsurj : Function.Surjective (MulAut.congr e).toMonoidHom := (MulAut.congr e).surjective
  have key : ∀ k : ℕ, 0 < k →
      (bParam (X.map (MulAut.congr e).toMonoidHom) (Y.map (MulAut.congr e).toMonoidHom) < k ↔
        bParam X Y < k) := by
    intro k hk
    rw [bParam_lt_iff hk, bParam_lt_iff hk]
    constructor
    · intro h A hA
      have h2 := h (A.map (MulAut.congr e).toMonoidHom)
        ((aSet_map_congr_equiv_iff e k Y A).2 hA)
      rw [← Subgroup.map_commutator] at h2
      exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h2
    · intro h A hA
      set A₀ : Subgroup (MulAut V) := A.comap (MulAut.congr e).toMonoidHom with hA₀
      have hA₀map : A₀.map (MulAut.congr e).toMonoidHom = A :=
        Subgroup.map_comap_eq_self_of_surjective hsurj A
      have hA₀mem : A₀ ∈ E3.aSet k Y := by
        refine (aSet_map_congr_equiv_iff e k Y A₀).1 ?_
        rwa [hA₀map]
      have h2 := h A₀ hA₀mem
      rw [← hA₀map, ← Subgroup.map_commutator, h2, Subgroup.map_bot]
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < bParam (X.map (MulAut.congr e).toMonoidHom)
        (Y.map (MulAut.congr e).toMonoidHom) := lt_of_le_of_lt (Nat.zero_le _) hlt
    exact absurd ((key _ hpos).2 hlt) (lt_irrefl _)
  · by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < bParam X Y := lt_of_le_of_lt (Nat.zero_le _) hlt
    exact absurd ((key _ hpos).1 hlt) (lt_irrefl _)

theorem bParam_map_conj {W : Type*} [CommGroup W] [Finite W] (a : MulAut W)
    (X Y : Subgroup (MulAut W)) :
    bParam (X.map (MulAut.conj a).toMonoidHom) (Y.map (MulAut.conj a).toMonoidHom) =
      bParam X Y := by
  have h : MulAut.conj a = MulAut.congr a := by
    ext f x
    simp [MulAut.conj_apply, MulAut.congr_apply]
  rw [h]
  exact bParam_map_congr a X Y

namespace A5Pair18

theorem bBar_conjSubgroup (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥) {x : G} (hx : x ∈ D.M) :
    bBar (conjSubgroup L x) D.M ⊥ V c.elemAbelian = bBar L D.M ⊥ V c.elemAbelian := by
  subst hV₀
  have hX : ∀ Y : Subgroup G, bBar Y D.M ⊥ V c.elemAbelian =
      bParam (autI c.elemAbelian Y) (autI c.elemAbelian D.M) := by
    intro Y
    have hbar : bBar Y D.M ⊥ V c.elemAbelian =
        bParam (barSub ⊥ V c.elemAbelian Y) (barSub ⊥ V c.elemAbelian D.M) := rfl
    rw [hbar, TwelveTwentyThree.barSub_bot_eq_map_autI V c.elemAbelian Y,
      TwelveTwentyThree.barSub_bot_eq_map_autI V c.elemAbelian D.M]
    exact bParam_map_congr (TwelveShort.mkTilEquiv V c.elemAbelian) _ _
  have hpF := c.data.hyp.hyp125.pairFacts
  have hgM : x⁻¹ ∈ D.M := D.M.inv_mem hx
  have hgN : x⁻¹ ∈ normalizer (V : Set G) := hpF.le_normalizer hgM
  have hK : conjSubgroup L x = cjSub x⁻¹ L := rfl
  have hMM : cjSub x⁻¹ D.M = D.M := by
    ext m
    rw [cjSub, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx) hk) (by simpa using hx)
    · intro hm
      refine ⟨x * m * x⁻¹, D.M.mul_mem (D.M.mul_mem hx hm) (D.M.inv_mem hx), ?_⟩
      show (MulAut.conj x⁻¹) (x * m * x⁻¹) = m
      rw [MulAut.conj_apply]
      group
  have hmapL : (autI c.elemAbelian L).map
        (MulAut.conj (convI c.elemAbelian ⟨x⁻¹, hgN⟩)).toMonoidHom =
      autI c.elemAbelian (conjSubgroup L x) := by
    rw [hK]
    exact autI_cjSub (hV := c.elemAbelian) hgN L
  have hmapM : (autI c.elemAbelian D.M).map
        (MulAut.conj (convI c.elemAbelian ⟨x⁻¹, hgN⟩)).toMonoidHom =
      autI c.elemAbelian D.M := by
    rw [autI_cjSub (hV := c.elemAbelian) hgN D.M, hMM]
  rw [hX, hX]
  calc bParam (autI c.elemAbelian (conjSubgroup L x)) (autI c.elemAbelian D.M)
      = bParam ((autI c.elemAbelian L).map
          (MulAut.conj (convI c.elemAbelian ⟨x⁻¹, hgN⟩)).toMonoidHom)
          ((autI c.elemAbelian D.M).map
            (MulAut.conj (convI c.elemAbelian ⟨x⁻¹, hgN⟩)).toMonoidHom) := by
        rw [hmapL, hmapM]
    _ = bParam (autI c.elemAbelian L) (autI c.elemAbelian D.M) :=
        bParam_map_conj (convI c.elemAbelian ⟨x⁻¹, hgN⟩) _ _

theorem bParam_eq_two_of_swap (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥)
    (hbL : bBar L D.M ⊥ V c.elemAbelian ≤ 2) (hbK : bBar K D.M ⊥ V c.elemAbelian ≤ 2)
    (hamax : aBar D.M ⊥ V c.elemAbelian =
      max (bBar L D.M ⊥ V c.elemAbelian) (bBar K D.M ⊥ V c.elemAbelian))
    (ha : aBar D.M ⊥ V c.elemAbelian = 2)
    (hsw : ∃ x ∈ D.M, K = conjSubgroup L x) :
    bBar L D.M ⊥ V c.elemAbelian = 2 ∧ bBar K D.M ⊥ V c.elemAbelian = 2 := by
  obtain ⟨x, hx, rfl⟩ := hsw
  have heq : bBar (conjSubgroup L x) D.M ⊥ V c.elemAbelian =
      bBar L D.M ⊥ V c.elemAbelian := c.bBar_conjSubgroup hV₀ hx
  have hm : max (bBar L D.M ⊥ V c.elemAbelian) (bBar (conjSubgroup L x) D.M ⊥ V c.elemAbelian)
      = 2 := by
    rw [← hamax]
    exact ha
  rw [heq, max_self] at hm
  exact ⟨hm, heq.trans hm⟩

end A5Pair18


@[expose] def CaseOne18 (D : Data G) (V L K : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  (∃ x ∈ Mbar D.M ⊥ V hV, barSub ⊥ V hV K =
      (barSub ⊥ V hV L).map (MulAut.conj x).toMonoidHom) ∧
    commSub (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (barSub ⊥ V hV L))
      (barSub ⊥ V hV K) = ⊥

@[expose] def CaseTwo18 (D : Data G) (V L K : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  (∃ x ∈ Mbar D.M ⊥ V hV, barSub ⊥ V hV K =
      (barSub ⊥ V hV L).map (MulAut.conj x).toMonoidHom) ∧
    IsOmegaPlus ↥(barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) 4 2 ∧
      SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2)
        (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) ⊤ ⊥ 2

@[expose] def CaseThree18 (D : Data G) (V L K : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  IsOmegaPlus ↥(barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) 4 2 ∧
    NatOmegaPlus (barSub ⊥ V hV L ⊔ barSub ⊥ V hV K) ⊤ ⊥ 4 2

structure A5Config18 (D : Data G) (V₀ V L K : Subgroup G) : Prop where
  pair : A5Pair18 D V₀ V L K
  v0 : V₀ = ⊥
  numerics : mBar D.M ⊥ V (pair.elemAbelian) = 4 ∧ aBar D.M ⊥ V (pair.elemAbelian) = 2 ∧ D.k = 2 ∧
    ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M
  normalizerW : normalizer (F12.Wi 1 D.T V : Set G) ≤ D.M
  uniqueMaxW : UniqueMax D.M (D.M ⊓ normalizer (F12.Wi 1 D.T V : Set G))
  uniqueMaxL : UniqueMax D.M (L ⊔ F12.Wi 1 D.T V)
  uniqueMaxK : UniqueMax D.M (K ⊔ F12.Wi 1 D.T V)
  barSubL : barSub ⊥ V pair.elemAbelian L ≠ ⊥
  barSubK : barSub ⊥ V pair.elemAbelian K ≠ ⊥
  fixV : fixV (barSub ⊥ V pair.elemAbelian (L ⊔ K)) = ⊥

namespace A5Config18

abbrev elemAbelian (c : A5Config18 D V₀ V L K) : IsElemAbelian 2 V := c.pair.elemAbelian

theorem barSub_not_normal_of_swap (c : A5Config18 D V₀ V L K)
    (hne : barSub ⊥ V c.elemAbelian L ≠ barSub ⊥ V c.elemAbelian K)
    (hsw : ∃ x ∈ D.M, K = conjSubgroup L x) :
    ¬ ((barSub ⊥ V c.elemAbelian L).subgroupOf (Mbar D.M ⊥ V c.elemAbelian)).Normal := by
  intro hLn'
  obtain ⟨x, hxM, hK⟩ := hsw
  apply hne
  have hp := c.pair.data.hyp.hyp125
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hp.pairFacts.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLS : L ≤ stabTil (⊥ : Subgroup G) V := c.pair.mem_calC_L.1.le.trans hMS
  have hxS : x⁻¹ ∈ stabTil (⊥ : Subgroup G) V := hMS (D.M.inv_mem hxM)
  have hbar := TwelveTwentyThree.barSub_map_conj (V₀ := ⊥) c.elemAbelian hLS hxS
  have hy : actTil ⊥ V c.elemAbelian ⟨x⁻¹, hxS⟩ ∈ Mbar D.M ⊥ V c.elemAbelian :=
    actTil_mem_barSub ⊥ V c.elemAbelian (D.M.inv_mem hxM) hxS
  have hnorm : Mbar D.M ⊥ V c.elemAbelian ≤
      normalizer ((barSub ⊥ V c.elemAbelian L : Subgroup _) : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (barSub_mono ⊥ V c.elemAbelian c.pair.mem_calC_L.1.le)).1 hLn'
  have heq := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hnorm hy)
  exact ((show barSub ⊥ V c.elemAbelian (L.map (MulAut.conj x⁻¹).toMonoidHom) =
      barSub ⊥ V c.elemAbelian L by rw [hbar]; exact heq).symm).trans
    (congrArg (barSub ⊥ V c.elemAbelian) hK.symm)

theorem fixV_of_normal (c : A5Config18 D V₀ V L K)
    (hne : barSub ⊥ V c.elemAbelian L ≠ barSub ⊥ V c.elemAbelian K) :
    ((barSub ⊥ V c.elemAbelian L).subgroupOf (Mbar D.M ⊥ V c.elemAbelian)).Normal →
      ((barSub ⊥ V c.elemAbelian K).subgroupOf (Mbar D.M ⊥ V c.elemAbelian)).Normal →
      CFSG.Quasithin.fixV (barSub ⊥ V c.elemAbelian L) = ⊥ ∧
        CFSG.Quasithin.fixV (barSub ⊥ V c.elemAbelian K) = ⊥ := by
  intro hLn' _
  rcases c.pair.dichotomy with ⟨-, hsw⟩ | ⟨-, hLn, hKn⟩
  · exact absurd hLn' (c.barSub_not_normal_of_swap hne hsw)
  · exact ⟨c.pair.fixV_barSub_eq_bot_of_normal c.v0 c.pair.mem_calC_L.1.le hLn c.uniqueMaxL
        c.numerics.2.2.2,
      c.pair.fixV_barSub_eq_bot_of_normal c.v0 c.pair.mem_calC.1.le hKn c.uniqueMaxK
        c.numerics.2.2.2⟩

theorem trichotomy (c : A5Config18 D V₀ V L K) (hW : W4Thm14_4)
    (hKG : IsKGroup ↥(Mbar D.M ⊥ V c.elemAbelian))
    (hO2 : O2Trivial (Mbar D.M ⊥ V c.elemAbelian))
    (hBasic : IsBasicModule (Mbar D.M ⊥ V c.elemAbelian))
    (hcompL : IsComponentOf (barSub ⊥ V c.elemAbelian L) (Mbar D.M ⊥ V c.elemAbelian))
    (hcompK : IsComponentOf (barSub ⊥ V c.elemAbelian K) (Mbar D.M ⊥ V c.elemAbelian))
    (hLalt : IsAlt ↥(barSub ⊥ V c.elemAbelian L) 5) (hKalt : IsAlt ↥(barSub ⊥ V c.elemAbelian K) 5)
    (hne : barSub ⊥ V c.elemAbelian L ≠ barSub ⊥ V c.elemAbelian K)
    (hXnorm : ((barSub ⊥ V c.elemAbelian L ⊔ barSub ⊥ V c.elemAbelian K).subgroupOf
      (Mbar D.M ⊥ V c.elemAbelian)).Normal)
    (hbL : bParam (barSub ⊥ V c.elemAbelian L) (Mbar D.M ⊥ V c.elemAbelian) = 2)
    (hbK : bParam (barSub ⊥ V c.elemAbelian K) (Mbar D.M ⊥ V c.elemAbelian) = 2)
    (hfix12 : ((barSub ⊥ V c.elemAbelian L).subgroupOf (Mbar D.M ⊥ V c.elemAbelian)).Normal →
      ((barSub ⊥ V c.elemAbelian K).subgroupOf (Mbar D.M ⊥ V c.elemAbelian)).Normal →
      CFSG.Quasithin.fixV (barSub ⊥ V c.elemAbelian L) = ⊥ ∧
        CFSG.Quasithin.fixV (barSub ⊥ V c.elemAbelian K) = ⊥) :
    CaseOne18 D V L K c.elemAbelian ∨ CaseTwo18 D V L K c.elemAbelian ∨
      CaseThree18 D V L K c.elemAbelian := by
  have hLstab : L ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil (c.pair.mem_calC_L.1.le.trans c.pair.data.hyp.hyp125.pairFacts.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil (c.pair.mem_calC.1.le.trans c.pair.data.hyp.hyp125.pairFacts.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hbsup : barSub ⊥ V c.elemAbelian (L ⊔ K) =
      barSub ⊥ V c.elemAbelian L ⊔ barSub ⊥ V c.elemAbelian K := by
    rw [barSub, barSub, barSub, Subgroup.subgroupOf_sup hLstab hKstab, Subgroup.map_sup]
  have hfix : CFSG.Quasithin.fixV (barSub ⊥ V c.elemAbelian L ⊔
      barSub ⊥ V c.elemAbelian K) = ⊥ := by
    rw [← hbsup]
    exact A5Config18.fixV c
  exact hW (Vtil ⊥ V c.elemAbelian) (s15_Infra_vtil_sq_eq_one ⊥ V c.elemAbelian)
    (Mbar D.M ⊥ V c.elemAbelian) (barSub ⊥ V c.elemAbelian L)
    (barSub ⊥ V c.elemAbelian K) (barSub ⊥ V c.elemAbelian L ⊔ barSub ⊥ V c.elemAbelian K)
    hKG hO2 hBasic hcompL hcompK hLalt hKalt
    (barSub_mono ⊥ V c.elemAbelian c.pair.mem_calC_L.1.le)
    (barSub_mono ⊥ V c.elemAbelian c.pair.mem_calC.1.le) hne rfl hXnorm hbL hbK hfix
    (by rw [show E3.mParam (Mbar D.M ⊥ V c.elemAbelian) = mBar D.M ⊥ V c.elemAbelian from rfl,
      c.numerics.1])
    hfix12

end A5Config18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
