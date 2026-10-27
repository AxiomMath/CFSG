module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSixtyOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tb
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s1715six_false_of_central (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hk2 : D.k = 2) (hm4 : mBar D.M ⊥ V h.isElemAbelian = 4)
    {H₁ H₂ : Subgroup G} (hT₁ : D.T ≤ H₁) (hT₂ : D.T ≤ H₂)
    (hF₁ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁)
    (hF₂ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂)
    (hO₁ : ∀ g : G, g ∉ D.M → ¬ twoResidual H₁ ≤ conjSubgroup D.M g)
    (hO₂ : ∀ g : G, g ∉ D.M → ¬ twoResidual H₂ ≤ conjSubgroup D.M g)
    (hU : UniqueMax D.M (H₁ ⊔ H₂ ⊔ D.T))
    {t : G} (htV : t ∈ V) (ht1 : t ≠ 1) (htT : ∀ k ∈ D.T, k * t = t * k)
    (hCt : centralizer ((zpowers t : Subgroup G) : Set G) ≤ D.M) : False := by
  classical
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D h.inCalV
  have htTmem : t ∈ D.T := hVT htV
  have ht_cClos : ∀ n : ℕ, t ∈ E3.cClos V n D.T := by
    intro n
    refine ⟨htTmem, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun x hx => htT x (E3.wClos_le n D.T hx)
  have hC_cClos : ∀ n : ℕ, centralizer (E3.cClos V n D.T : Set G) ≤ D.M := by
    intro n
    exact (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.2 (Subgroup.zpowers_le.2 (ht_cClos n)))).trans hCt
  have hm2 : MBarGT D.M ⊥ V 2 := (h.mBarGT_iff_lt_mBar 2).2 (by omega)
  have hm3 : MBarGT D.M ⊥ V 3 := (h.mBarGT_iff_lt_mBar 3).2 (by omega)
  have hN0 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    ((twelve_ten_two D hx h61 h126 h111 h rfl (i := 0) (by simpa [hk2] using hm2))
      ).resolve_right fun hc => hc (by simpa [hk2] using hC_cClos 2)
  have hN1 : ¬ normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M :=
    ((twelve_ten_two D hx h61 h126 h111 h rfl (i := 1) (by simpa [hk2] using hm3))
      ).resolve_right fun hc => hc (by simpa [hk2] using hC_cClos 3)
  have hVW0 : V ≤ E3.wClos V 0 D.T := by
    refine E3.le_wClos ?_
    refine ⟨hVT, 1, ?_, ?_⟩
    · rw [conjSubgroup_one]
    · rw [conjSubgroup_one]
      exact E3.mQuot_self V
  have hW0ne : E3.wClos V 0 D.T ≠ ⊥ := fun hbot =>
    h.inCalV.1 (le_bot_iff.1 (hVW0.trans (le_of_eq hbot)))
  have hW0p : IsPGroup 2 (E3.wClos V 0 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  have hrk : 3 ≤ rk ↥V := by
    have hcard := Hyp125.eight_le_card_of_bot h
    have hpow : Nat.card ↥V = 2 ^ rk ↥V :=
      card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
    rw [hpow] at hcard
    have h8 : 2 ^ 3 ≤ 2 ^ rk ↥V := by simpa using hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h8
  have hW01 : E3.wClos V 0 D.T ≤ E3.wClos V 1 D.T :=
    wClos_le_wClos_of_le hV (by norm_num) (by omega) D.T
  have hVW1 : V ≤ E3.wClos V 1 D.T := hVW0.trans hW01
  have hxh : ¬ H₁ ≤ normalizer (E3.wClos V 0 D.T : Set G) ∨
      ¬ H₂ ≤ normalizer (E3.wClos V 0 D.T : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : H₁ ⊔ H₂ ⊔ D.T ≤ normalizer (E3.wClos V 0 D.T : Set G) := by
      refine sup_le (sup_le hcon.1 hcon.2) ?_
      exact (Subgroup.le_normalizer).trans
        (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) D.T)
    exact hN0 (uc22p22p_le_of_uniqueMax hU ⟨_, hW0ne, hW0p, rfl⟩ hle)
  have key : ∀ H : Subgroup G, D.T ≤ H → CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H →
      (∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g) →
      ¬ H ≤ normalizer (E3.wClos V 0 D.T : Set G) →
      normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M := by
    intro H hTH hFH hOH hHN
    intro g hgN
    by_contra hgM
    have h01 : 0 + 1 < E3.sParam hV := by
      have h1 := s16c167_one_lt_sParam D hx h61 h (by omega)
      simpa using h1
    have hcomm : ⁅E3.cClos V 1 D.T, twoResidual H⁆ = ⊥ :=
      (uc22p22tb_dich hV (TwelveShort.isSylowIn_of_le D hTH) (i := 0) (j := 1) hFH h01
        ).resolve_left hHN
    have hcomm' : ⁅twoResidual H, E3.cClos V 1 D.T⁆ = ⊥ := by
      rwa [Subgroup.commutator_comm]
    have hleCent : twoResidual H ≤
        Subgroup.centralizer (E3.cClos V 1 D.T : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm'
    have htZ : t ∈ centerOf (E3.wClos V 1 D.T) :=
      ⟨hVW1 htV, Subgroup.mem_centralizer_iff.2 fun x hx =>
        htT x (E3.wClos_le 1 D.T hx)⟩
    have hgtZ : g * t * g⁻¹ ∈ centerOf (E3.wClos V 1 D.T) :=
      (Subgroup.mem_normalizer_iff.1
        ((E3.normalizer_le_normalizer_centerOf _) hgN) t).1 htZ
    have hgtC : g * t * g⁻¹ ∈ E3.cClos V 1 D.T :=
      CFSG.LocalAnalysis.WeakClosure81.centerOf_wClos_le_cClos_self 1 D.T hgtZ
    have hxC : ∀ x ∈ twoResidual H, g⁻¹ * x * g ∈ D.M := by
      intro x hx
      have hxc : (g * t * g⁻¹) * x = x * (g * t * g⁻¹) :=
        Subgroup.mem_centralizer_iff.1 (hleCent hx) (g * t * g⁻¹) hgtC
      have hconj : g⁻¹ * x * g * t = t * (g⁻¹ * x * g) := by
        calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxc]
          _ = t * (g⁻¹ * x * g) := by group
      have hmem : g⁻¹ * x * g ∈
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
        rw [CFSG.Walter.centralizer_zpowers_eq']
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hconj
      exact hCt hmem
    have hgM' : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
    exact hOH g⁻¹ hgM' fun x hx => mem_conjSubgroup_iff.2 (by simpa using hxC x hx)
  rcases hxh with h1 | h2
  · exact hN1 (key H₁ hT₁ hF₁ hO₁ h1)
  · exact hN1 (key H₂ hT₂ hF₂ hO₂ h2)

theorem s1715six_exists_central (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {H : Subgroup G} (hHM : H ≤ D.M) (hTH : D.T ≤ normalizer (H : Set G))
    (hfix : fixV (barSub ⊥ V h.isElemAbelian H) ≠ ⊥) :
    ∃ t : G, t ∈ V ∧ t ≠ 1 ∧ (∀ k ∈ D.T, k * t = t * k) ∧
      H ≤ centralizer ((zpowers t : Subgroup G) : Set G) := by
  classical
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hMV : D.M ≤ normalizer (V : Set G) := h.inCalV.2.2.1
  have hMstab : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hfix
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV w
  have hx1 : x.val ≠ 1 := by
    intro hx
    apply hw1
    apply Subtype.ext
    show mkTil ⊥ V hV x = 1
    rw [mkTil, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_modNull, hx]
    exact Subgroup.one_mem _
  have hcx : ∀ g ∈ H, g * x.val = x.val * g := by
    intro g hg
    have hgs : g ∈ stabTil ⊥ V := hMstab (hHM hg)
    have h1 := (mem_fixV.1 hw) _ (actTil_mem_barSub ⊥ V hV hg hgs)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot] at h1
    calc g * x.val = g * x.val * g⁻¹ * (x.val)⁻¹ * x.val * g := by group
      _ = x.val * g := by rw [h1, one_mul]
  set Y : Subgroup G := V ⊓ centralizer (H : Set G) with hYdef
  have hYT : Y ≤ D.T := inf_le_left.trans (uc22p22p_le_T_of_inCalV D h.inCalV)
  have hTY : D.T ≤ normalizer (Y : Set G) :=
    A1a.le_normalizer_inf (D.sylowM.le.trans hMV) (A1a.le_normalizer_centralizer hTH)
  have hYn : (Y.subgroupOf D.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYT).2 hTY
  have hxY : x.val ∈ Y := ⟨x.val_mem, Subgroup.mem_centralizer_iff.2 hcx⟩
  have hYne : Y.subgroupOf D.T ≠ ⊥ := by
    intro h0
    apply hx1
    have : (⟨x.val, hYT hxY⟩ : ↥D.T) ∈ Y.subgroupOf D.T := hxY
    rw [h0, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hYne)
  have htY : (t : G) ∈ Y := ht.1
  have htc : ∀ k ∈ D.T, k * (t : G) = (t : G) * k := fun k hk =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 ht.2 ⟨k, hk⟩)
  have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext (Subtype.ext h))
  exact ⟨(t : G), htY.1, ht1', htc,
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 htY.2)⟩

theorem s1715six_fixV_eq_bot (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) {V L : Subgroup G} (h : Hyp125 D ⊥ V)
    (hL : L ∈ calC D.M) (hUL : UniqueMax D.M L) (hk2 : D.k = 2)
    (hm4 : mBar D.M ⊥ V h.isElemAbelian = 4)
    {H₁ H₂ : Subgroup G} (hT₁ : D.T ≤ H₁) (hT₂ : D.T ≤ H₂)
    (hF₁ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁)
    (hF₂ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂)
    (hO₁ : ∀ g : G, g ∉ D.M → ¬ twoResidual H₁ ≤ conjSubgroup D.M g)
    (hO₂ : ∀ g : G, g ∉ D.M → ¬ twoResidual H₂ ≤ conjSubgroup D.M g)
    (hU : UniqueMax D.M (H₁ ⊔ H₂ ⊔ D.T)) :
    fixV (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ := by
  classical
  by_contra hfix
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hHM : UC22.conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hL.1.le
  have hTH : D.T ≤ normalizer (UC22.conjClosure D.M L : Set G) :=
    D.sylowM.le.trans (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  obtain ⟨t, htV, ht1, htT, hHc⟩ := s1715six_exists_central D h hHM hTH hfix
  have hLc : L ≤ centralizer ((zpowers t : Subgroup G) : Set G) :=
    (TwelveTwentyThree.le_conjClosure D.M L).trans hHc
  have hTc : D.T ≤ centralizer ((zpowers t : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 htT))
  have hU' : UniqueMax D.M (L ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D le_sup_left (sup_le hL.1.le D.sylowM.le) hUL
  have hNt : normalizer ((zpowers t : Subgroup G) : Set G) ≤ D.M :=
    uc22p22p_le_of_uniqueMax hU' ⟨_, Subgroup.zpowers_ne_bot.2 ht1,
      (uc22p22e_isPGroup_of_elem hV).to_le (Subgroup.zpowers_le.2 htV), rfl⟩
      ((sup_le hLc hTc).trans (Subgroup.centralizer_le_normalizer _))
  have hCt : centralizer ((zpowers t : Subgroup G) : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer _).trans hNt
  exact s1715six_false_of_central D hx h61 h126 h111 h hk2 hm4 hT₁ hT₂ hF₁ hF₂ hO₁ hO₂ hU
    htV ht1 htT hCt

theorem s1715six_inf_centralizer_eq_bot (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) {V L : Subgroup G} (h : Hyp125 D ⊥ V)
    (hL : L ∈ calC D.M) (hUL : UniqueMax D.M L) (hk2 : D.k = 2)
    (hm4 : mBar D.M ⊥ V h.isElemAbelian = 4)
    {H₁ H₂ : Subgroup G} (hT₁ : D.T ≤ H₁) (hT₂ : D.T ≤ H₂)
    (hF₁ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁)
    (hF₂ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂)
    (hO₁ : ∀ g : G, g ∉ D.M → ¬ twoResidual H₁ ≤ conjSubgroup D.M g)
    (hO₂ : ∀ g : G, g ∉ D.M → ¬ twoResidual H₂ ≤ conjSubgroup D.M g)
    (hU : UniqueMax D.M (H₁ ⊔ H₂ ⊔ D.T)) :
    V ⊓ centralizer ((UC22.conjClosure D.M L : Subgroup G) : Set G) = ⊥ := by
  classical
  have hfix := s1715six_fixV_eq_bot D hx h61 h126 h111 h hL hUL hk2 hm4
    hT₁ hT₂ hF₁ hF₂ hO₁ hO₂ hU
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  have hvV : v ∈ V := hv.1
  have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
      fixV (barSub ⊥ V hV (UC22.conjClosure D.M L)) := by
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ V hV (UC22.conjClosure D.M L) φ).1 hφ
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    have hcomm : (g : G) * v = v * (g : G) :=
      Subgroup.mem_centralizer_iff.1 hv.2 (g : G) hg
    calc (g : G) * v * (g : G)⁻¹ * v⁻¹ = v * (g : G) * (g : G)⁻¹ * v⁻¹ := by
          rw [hcomm]
      _ = 1 := by group
  rw [hfix] at hmem
  have h1 : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩) = 1 := Subgroup.mem_bot.1 hmem
  rw [mkTil, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_modNull,
    Subgroup.mem_bot] at h1
  exact hv1 h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
