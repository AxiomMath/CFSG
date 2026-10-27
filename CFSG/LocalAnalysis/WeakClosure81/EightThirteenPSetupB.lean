module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSetupA
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBarDown
public import CFSG.LocalAnalysis.WeakClosure81.EightEleven
public import CFSG.LocalAnalysis.WeakClosure81.EightTenAS
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCfg
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelve
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

@[expose] def Data810 (V H T L₀ : Subgroup G) : Prop :=
  IsComponentModN (kerMV V H) H L₀ ∧
    HasQuotShape L₀ (kerMV V H : Set G) (fun X _ => IsSimpleGroup X) ∧ L₀ ⊔ T = H ∧
    (HasQuotShape L₀ (kerMV V H : Set G) (fun X _ => IsL2 X 2) ∨
      HasQuotShape L₀ (kerMV V H : Set G) (fun X _ => IsU3 X 2) ∨
      ((HasQuotShape L₀ (kerMV V H : Set G) (fun X _ => IsL3 X 2) ∨
          HasQuotShape L₀ (kerMV V H : Set G) (fun X _ => IsSp4 X 2)) ∧
        ∃ t ∈ T ⊓ normalizer (L₀ : Set G), ActsOnDynkinMod (kerMV V H) L₀ t))

section BarSetupB

variable {H : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}

private theorem wc813psb_barSub_mono {A B : Subgroup G} (hAB : A ≤ B) :
    barSub H φ A ≤ barSub H φ B := by
  change (A.subgroupOf H).map φ ≤ (B.subgroupOf H).map φ
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hAB)

private theorem wc813psb_barPre_top : barPre H φ (⊤ : Subgroup Q) = H := by
  ext g
  rw [mem_barPre]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

private theorem wc813psb_barSub_top {C : Subgroup G} (hφ : IsBarMap H C φ) :
    barSub H φ H = ⊤ := by
  change (H.subgroupOf H).map φ = ⊤
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective φ hφ.surjective

end BarSetupB

private theorem wc813psb_exists_isE_not_le_of_inFSqAS {V H T M₀ : Subgroup G} {i j : ℕ}
    (hV : IsElemAbelian 2 V) (hT : IsSylowIn 2 T H) (hF : InFSqAS j H) (hTM : T ≤ M₀)
    (hHM : ¬ H ≤ M₀) (hA : ∃ A ∈ E3.gammaSet V i T, ¬ A ≤ pCoreOf 2 H) :
    ∃ A ∈ E3.gammaSet V i T, ∃ K : Subgroup G, E1.IsE j H T A K ∧ ¬ K ≤ M₀ := by
  obtain ⟨A₀, ⟨hA₀T, hA₀g⟩, hA₀O⟩ := hA
  obtain ⟨A, hAΩ, hAT, K, hK, hKM⟩ := exists_isE_not_le_of_inFSqAS hT hF hTM hHM
    (E3.isInvColl_gammaSet hV i H) ⟨A₀, ⟨hA₀T.trans hT.le, hA₀g⟩, hA₀O⟩
  exact ⟨A, ⟨hAT, hAΩ.2⟩, K, hK, hKM⟩

theorem Pre813.not_inFSqAS_one {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A) :
    ¬ InFSqAS 1 H := by
  intro hF
  have hV7 : Hyp7 V := h.minCex.hyp.hyp7
  have hH0 : IsCalH0 V H := h.calH0
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.minCex.hyp.calH h.minCex.hyp.sylow
  have hTM : T ≤ normalizer (V : Set G) := h.minCex.hyp.sylow.le.trans inf_le_right
  obtain ⟨A₀, hA₀, hA₀O, -⟩ := h.minCex.hyp.exists_gammaSet_not_le_normalizer
  obtain ⟨A', hA', K', hK', hK'M⟩ :=
    wc813psb_exists_isE_not_le_of_inFSqAS (M₀ := normalizer (V : Set G)) hV7.1 hTH hF hTM
      h.minCex.hyp.notLe ⟨A₀, hA₀, hA₀O⟩
  have hle := rk_le_add_of_isE_not_le_normalizer hV7 hH0 h.minCex.hyp.sylow hA' hK' hK'M
  have h3 : rk ↥V = 3 := h.concl812.1
  have hi : i = 1 := h.concl812.2.1
  omega

theorem Pre813.exists_data810 (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A) :
    OInf H = kerMV V H ∧ ∃ L₀ : Subgroup G, Data810 V H T L₀ := by
  have hker : OInf H = kerMV V H := by
    by_cases h1 : Concl881 V H
    · have h2 : ¬ Concl882 V H := fun h2 => h.minCex.fail ⟨h1, h2⟩
      obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := h.minCex.hyps_5_11 h2
      obtain ⟨-, hcase⟩ := h5_11 G H T hK hT hTlt hno hne hp
      rcases hcase with h11 | ⟨h22, L, hL, hLT, hshape⟩
      · exact absurd h11 h.not_inFSqAS_one
      · exact oInf_eq_kerMV hT (MinCex88.calNIn_eq_AS h5_11 h5_13 h.minCex) ⟨L, hL, hLT⟩
    · obtain ⟨hK, hT, hTlt, h3, hno, hne⟩ := h.minCex.hyps_5_13 h1
      obtain ⟨-, hcase⟩ := h5_13 G H T hK hT hTlt h3 hno hne
      rcases hcase with h11 | ⟨n, hn, hshape⟩
      · exact absurd h11 h.not_inFSqAS_one
      · exact absurd hshape (h.minCex.not_fStar_shape_AS h5_11 h5_13 h1 n hn)
  refine ⟨hker, ?_⟩
  rcases MinCex88.eight_ten_AS h5_11 h5_13 h.minCex with
    h1 | ⟨hpp, h2, L, hL, hLsimple, hLT, hshape⟩
  · exact absurd h1 h.not_inFSqAS_one
  · exact ⟨L, hL, hLsimple, hLT, hshape⟩

theorem maxT_bar (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A : Subgroup G} {i : ℕ}
    (h : Pre813 V H T i A) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    calNIn (⊤ : Subgroup Q) (barSub H φ T) =
      {barSub H φ (H ⊓ normalizer (V : Set G))} := by
  have hCB : cGrp H T ≤ H ⊓ normalizer (V : Set G) :=
    (cGrp_le_kerMV h5_11 h5_13 h).trans
      (le_inf (kerMV_le_self V H) (kerMV_le_normalizer V H))
  have hCH : cGrp H T ≤ H := hCB.trans inf_le_left
  have hTH : T ≤ H := h.minCex.hyp.sylow.le.trans inf_le_left
  have hBmem : H ⊓ normalizer (V : Set G) ∈ calNIn H T := by
    rw [MinCex88.calNIn_eq_AS h5_11 h5_13 h.minCex]
    exact Set.mem_singleton _
  refine Set.Subset.antisymm ?_ ?_
  · intro Xb hXb
    rw [Set.mem_singleton_iff]
    obtain ⟨hTXb, hXblt, hXbmax⟩ := hXb
    have hCX : cGrp H T ≤ barPre H φ Xb := le_barPre hCH hφ Xb
    have hXH : barPre H φ Xb ≤ H := barPre_le H φ Xb
    have hTX : T ≤ barPre H φ Xb := fun t ht =>
      mem_barPre.mpr ⟨hTH ht, hTXb (mem_barSub.mpr ⟨⟨t, hTH ht⟩, ht, rfl⟩)⟩
    have hXlt : barPre H φ Xb < H := by
      refine lt_of_le_of_ne hXH ?_
      intro heq
      have htop : Xb = ⊤ := by
        rw [← barSub_barPre hφ Xb, heq, wc813psb_barSub_top hφ]
      exact hXblt.ne htop
    have hXmax : ∀ Y : Subgroup G, barPre H φ Xb < Y → Y ≤ H → Y = H := by
      intro Y hXY hYH
      have hCY : cGrp H T ≤ Y := hCX.trans hXY.le
      have hbarlt : Xb < barSub H φ Y := by
        refine lt_of_le_of_ne ?_ ?_
        · rw [← barSub_barPre hφ Xb]
          exact wc813psb_barSub_mono hXY.le
        · intro heq
          have : barPre H φ Xb = Y := by
            rw [heq, barPre_barSub hφ hCY hYH]
          exact hXY.ne this
      have hbar : barSub H φ Y = ⊤ := hXbmax (barSub H φ Y) hbarlt le_top
      rw [← barPre_barSub hφ hCY hYH, hbar, wc813psb_barPre_top]
    have hXmem : barPre H φ Xb ∈ calNIn H T := ⟨hTX, hXlt, hXmax⟩
    rw [MinCex88.calNIn_eq_AS h5_11 h5_13 h.minCex, Set.mem_singleton_iff] at hXmem
    rw [← barSub_barPre hφ Xb, hXmem]
  · intro Xb hXb
    rw [Set.mem_singleton_iff] at hXb
    subst hXb
    refine ⟨wc813psb_barSub_mono hBmem.1, ?_, ?_⟩
    · refine lt_of_le_of_ne le_top ?_
      intro heq
      have hpre := congrArg (barPre H φ) heq
      rw [barPre_barSub hφ hCB inf_le_left, wc813psb_barPre_top] at hpre
      exact hBmem.2.1.ne hpre
    · intro Yb hlt _
      have hYb : barSub H φ (barPre H φ Yb) = Yb := barSub_barPre hφ Yb
      have hCY : cGrp H T ≤ barPre H φ Yb := le_barPre hCH hφ Yb
      have hCYH : barPre H φ Yb ≤ H := barPre_le H φ Yb
      have hle : H ⊓ normalizer (V : Set G) ≤ barPre H φ Yb := by
        intro x hx
        have hxH : x ∈ H := (inf_le_left : H ⊓ normalizer (V : Set G) ≤ H) hx
        exact mem_barPre.mpr ⟨hxH, hlt.le (mem_barSub.mpr ⟨⟨x, hxH⟩, hx, rfl⟩)⟩
      have hne : H ⊓ normalizer (V : Set G) ≠ barPre H φ Yb := by
        intro heq
        have : barSub H φ (H ⊓ normalizer (V : Set G)) = Yb := by rw [← hYb, heq]
        exact hlt.ne this
      have hYH : barPre H φ Yb = H :=
        hBmem.2.2 (barPre H φ Yb) (lt_of_le_of_ne hle hne) hCYH
      rw [← hYb, hYH, wc813psb_barSub_top hφ]

theorem isSylowIn_barSub_T {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A)
    {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H (cGrp H T) φ) :
    IsSylowIn 2 (barSub H φ T) (⊤ : Subgroup Q) := by
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.minCex.hyp.calH h.minCex.hyp.sylow
  have hTsyl : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
    have := (E1.isSylowIn_subgroupOf_iff (H := H) hTH.le le_rfl).mpr hTH
    rwa [Subgroup.subgroupOf_self] at this
  have hmap : IsSylowIn 2 ((T.subgroupOf H).map φ) ⊤ :=
    E1.isSylowIn_two_map_top hφ.surjective hTsyl
  simpa [barSub] using hmap

theorem barSub_A_basic {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A)
    {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H (cGrp H T) φ) :
    barSub H φ A ≤ barSub H φ T ∧ IsElemAbelian 2 (barSub H φ A) ∧
      Nat.card (barSub H φ A) = 4 := by
  obtain ⟨hAT, g, hAg, -⟩ := h.mem
  have hTH : T ≤ H := h.minCex.hyp.sylow.le.trans inf_le_left
  have hAH : A ≤ H := hAT.trans hTH
  have hAab : IsElemAbelian 2 A :=
    (isElemAbelian_conjSubgroup' h.minCex.hyp.hyp7.1 g).mono hAg
  have hCH : cGrp H T ≤ H := inf_le_left
  have hfaith := (eight_thirteen_faithful h.minCex.hyp.hyp7 h.calH0 h.minCex.hyp.sylow
    h.mem h.notLe).1
  have hAC : A ⊓ cGrp H T = ⊥ := by
    rw [cGrp, ← inf_assoc, inf_eq_left.mpr hAH]
    exact hfaith
  have hrel : (cGrp H T).relIndex A = Nat.card A := by
    rw [← Subgroup.inf_relIndex_right (cGrp H T) A, inf_comm, hAC,
      Subgroup.relIndex_bot_left]
  have hcardA : Nat.card A = 4 := by
    rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Open.IsElemAbelian.isPGroup hAab), h.concl812.2.2.1]
    norm_num
  refine ⟨wc813psb_barSub_mono hAT, isElemAbelian_barSub hAab φ, ?_⟩
  rw [card_barSub_eq_relIndex_of_isBarMap hAH hCH hφ, hrel, hcardA]

theorem kerMV_bar (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A : Subgroup G} {i : ℕ}
    (h : Pre813 V H T i A) (hK : OInf H = kerMV V H) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    (barSub H φ (kerMV V H)).Normal ∧ IsSolvable (barSub H φ (kerMV V H)) ∧
      barSub H φ (kerMV V H) ≤ barSub H φ (H ⊓ normalizer (V : Set G)) := by
  have hKH : kerMV V H ≤ H := kerMV_le_self V H
  have hnorm : ((kerMV V H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_kerMV (V := V) (H := H) hg hx
    · intro hx
      have h' := conj_mem_kerMV (V := V) (H := H) (H.inv_mem hg) hx
      have he : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
      rwa [he] at h'
  have hnormal : (barSub H φ (kerMV V H)).Normal := by
    have h' := hnorm.map φ hφ.surjective
    simpa [barSub] using h'
  have hsol : IsSolvable (barSub H φ (kerMV V H)) := by
    haveI : Group.IsSolvable (CFSG.solvableRadical ↥H) :=
      CFSG.Timmesfeld.Bridge.isSolvable_solvableRadical'
    let f : ↥(CFSG.solvableRadical ↥H) →* ↥(barSub H φ (kerMV V H)) :=
      (φ.comp (Subgroup.subtype (CFSG.solvableRadical ↥H))).codRestrict _
        (fun x => by
          have hxmem : H.subtype x.1 ∈ OInf H := Subgroup.mem_map_of_mem H.subtype x.2
          have hxker : (x.1 : G) ∈ kerMV V H := by
            rw [← hK]
            exact hxmem
          exact mem_barSub.mpr ⟨x.1, hxker, rfl⟩)
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨k, hkker, hkφ⟩ := mem_barSub.mp y.2
      have hkO : (k : G) ∈ OInf H := by rw [hK]; exact hkker
      obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.mp hkO
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      show φ s = (y : Q)
      rw [show s = k from Subtype.ext hsk, hkφ]
    exact Group.isSolvable_of_surjective (f := f) hfsurj
  refine ⟨hnormal, hsol, ?_⟩
  exact wc813psb_barSub_mono (le_inf (kerMV_le_self V H) (kerMV_le_normalizer V H))

theorem Pre813.cfg (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A : Subgroup G} {i : ℕ}
    (h : Pre813 V H T i A) (hK : OInf H = kerMV V H) {L₀ : Subgroup G}
    (hL₀ : Data810 V H T L₀) {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    Cfg813 (barSub H φ T) (barSub H φ A) (barSub H φ (H ⊓ normalizer (V : Set G)))
      (barSub H φ (kerMV V H)) (barSub H φ L₀) := by
  have hCN : cGrp H T ≤ kerMV V H := cGrp_le_kerMV h5_11 h5_13 h
  have hKL : kerMV V H ≤ L₀ := hL₀.1.2.1
  have hLH : L₀ ≤ H := hL₀.1.2.2.1
  have hTH : T ≤ H := h.minCex.hyp.sylow.le.trans inf_le_left
  refine
    { no_normal_two := no_normal_two_bar h hφ
      sylow := isSylowIn_barSub_T h hφ
      A_le := (barSub_A_basic h hφ).1
      A_elem := (barSub_A_basic h hφ).2.1
      A_card := (barSub_A_basic h hφ).2.2
      K1 := k1_bar h hφ
      TIS := tis_bar h5_11 h5_13 h hφ
      maxT := maxT_bar h5_11 h5_13 h hφ
      R_normal := (kerMV_bar h5_11 h5_13 h hK hφ).1
      R_solvable := (kerMV_bar h5_11 h5_13 h hK hφ).2.1
      R_le_B := (kerMV_bar h5_11 h5_13 h hK hφ).2.2
      L₀_comp := isComponentModN_barSub hφ hCN hL₀.1
      L₀_simple := hasQuotShape_barSub hφ hCN hKL hLH hL₀.2.1
      L₀_sup := ?_
      L₀_shape := ?_ }
  · rw [← barSub_sup hLH hTH φ, hL₀.2.2.1, wc813psb_barSub_top hφ]
  · rcases hL₀.2.2.2 with hL2 | hU3 | ⟨hSh, t, ht, hact⟩
    · exact Or.inl (Or.inl (hasQuotShape_barSub hφ hCN hKL hLH hL2))
    · exact Or.inl (Or.inr (hasQuotShape_barSub hφ hCN hKL hLH hU3))
    · have htH : t ∈ H := hTH (Subgroup.mem_inf.mp ht).1
      have hactbar := actsOnDynkinMod_barSub hφ htH hCN hLH hact
      refine Or.inr ⟨?_, ?_⟩
      · rcases hSh with hL3 | hSp4
        · exact Or.inl (hasQuotShape_barSub hφ hCN hKL hLH hL3)
        · exact Or.inr (hasQuotShape_barSub hφ hCN hKL hLH hSp4)
      · exact ⟨φ ⟨t, htH⟩,
          Subgroup.mem_inf.mpr
            ⟨mem_barSub.mpr ⟨⟨t, htH⟩, (Subgroup.mem_inf.mp ht).1, rfl⟩, hactbar.1⟩,
          hactbar⟩

end CFSG.LocalAnalysis.WeakClosure81

end
