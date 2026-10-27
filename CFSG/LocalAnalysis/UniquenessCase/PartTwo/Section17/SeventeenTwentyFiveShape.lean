module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerShape
public import CFSG.CGT.PushingUpLit.BHS7.SevenFourteenTransport
public import CFSG.GroupTheory.PowMemSupOfPGroup
public import CFSG.GroupTheory.CenterSubgroupOf
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def gap17_25_action {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L) :
    ↥(L ⊔ D.T) →* ↥(barSub V₀ V h.isElemAbelian (L ⊔ D.T)) :=
  let hstab : L ⊔ D.T ≤ stabTil V₀ V :=
    (sup_le c.mem_calC.1.le D.sylowM.le).trans
      (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  ((actTil V₀ V h.isElemAbelian).comp (Subgroup.inclusion hstab)).codRestrict
    (barSub V₀ V h.isElemAbelian (L ⊔ D.T))
    (fun x => actTil_mem_barSub V₀ V h.isElemAbelian x.2 (hstab x.2))

theorem gap17_25_action_ker_isPGroup {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L)
    (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G))
    (hsimple : IsSimpleGroup (Bar2 L))
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    IsPGroup 2 (gap17_25_action h c).ker := by
  classical
  set H : Subgroup G := L ⊔ D.T with hHdef
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hHleM : H ≤ D.M := sup_le c.mem_calC.1.le D.sylowM.le
  have hHstab : H ≤ stabTil V₀ V := hHleM.trans
    (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  let gH : ↥H →* ↥(barSub V₀ V h.isElemAbelian H) := gap17_25_action h c
  let Lsub : Subgroup ↥H := L.subgroupOf H
  let N : Subgroup ↥H := (pCoreOf 2 L).subgroupOf H
  have hNp : IsPGroup 2 N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)).symm
  have hNker : N ≤ gH.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hnP : (n : G) ∈ pCoreOf 2 L := Subgroup.mem_subgroupOf.mp hn
    have hmem : actTil V₀ V h.isElemAbelian ⟨(n : G), hHstab n.2⟩ ∈
        barSub V₀ V h.isElemAbelian (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V h.isElemAbelian hnP (hHstab n.2)
    rw [TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h.isElemAbelian c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)] at hmem
    show actTil V₀ V h.isElemAbelian ⟨(n : G), hHstab n.2⟩ = 1
    simpa using hmem
  have hkerL : gH.ker ⊓ Lsub = N := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxker, hxL⟩ := Subgroup.mem_inf.mp hx
      rw [MonoidHom.mem_ker] at hxker
      have hact : actTil V₀ V h.isElemAbelian ⟨(x : G), hHstab x.2⟩ = 1 := by
        have hh := congrArg (fun z : ↥(barSub V₀ V h.isElemAbelian H) =>
          ((z : MulAut (Vtil V₀ V h.isElemAbelian)))) hxker
        exact hh
      exact Subgroup.mem_subgroupOf.mpr
        (mem_pCoreOf_of_actTil_eq_one h c.mem_calC.1 hsimple hL1
          (Subgroup.mem_subgroupOf.mp hxL) (hHstab x.2) hact)
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hNker hx, Subgroup.mem_subgroupOf.mpr
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) (Subgroup.mem_subgroupOf.mp hx))⟩
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  have hTnorm : D.T ≤ Subgroup.normalizer (L : Set G) := D.sylowM.le.trans hMnorm
  obtain ⟨k, hkL⟩ :=
    CFSG.GroupTheory.exists_pow_prime_pow_mem_of_mem_sup (p := 2)
      D.sylowM.isPGroup hTnorm (x := ((x : ↥H) : G)) x.1.2
  have hxpowL : ((x : ↥H) : G) ^ 2 ^ k ∈ L := hkL
  have hxpowH : ((x : ↥H) : G) ^ 2 ^ k ∈ H := hLH hxpowL
  let zH : ↥H := ⟨((x : ↥H) : G) ^ 2 ^ k, hxpowH⟩
  have hxpow : (x : ↥H) ^ 2 ^ k = zH := by
    apply Subtype.ext
    rfl
  have hzK : zH ∈ gH.ker := by
    rw [MonoidHom.mem_ker, ← hxpow, map_pow, MonoidHom.mem_ker.mp x.2, one_pow]
  have hzL : zH ∈ Lsub := Subgroup.mem_subgroupOf.mpr hxpowL
  have hzN : zH ∈ N := by
    rw [← hkerL]
    exact Subgroup.mem_inf.mpr ⟨hzK, hzL⟩
  obtain ⟨m, hm⟩ := (isPGroup_iff_pow_pow_eq_one.mp hNp) ⟨zH, hzN⟩
  have hzpowH : zH ^ 2 ^ m = 1 := by
    have h := congrArg (fun w : ↥N => (w : ↥H)) hm
    simpa using h
  have hzpowG : (((x : ↥H) : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
    have h := congrArg (fun w : ↥H => (w : G)) hzpowH
    simpa [zH] using h
  refine ⟨k + m, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (((x : ↥H) : G) ^ 2 ^ (k + m)) = 1
  rw [Nat.pow_add, pow_mul]
  exact hzpowG

theorem gap17_25_barSub_L_ne_bot {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V) :
    barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ := by
  have hnt : ¬ F08.Thin8 L := by
    intro ht
    have hm3 := (h20 L c).1
    have hm3' : Open.pRank 3 L = 2 := by
      rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
      exact hm3
    have h3 : Open.pRank 3 L ≤ 1 := ht 3 Nat.prime_three (by norm_num)
    rw [hm3'] at h3
    exact absurd h3 (by norm_num)
  exact barSub_ne_bot_of_not_thin c.hyp125 hC117 c.mem_calC hnt

theorem gap17_25_action_surjective {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) : Function.Surjective (gap17_25_action c.hyp125 c) := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hpair := c.hyp125.pairFacts
  have hHstab : L ⊔ D.T ≤ stabTil V₀ V :=
    (sup_le c.mem_calC.1.le D.sylowM.le).trans
      (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  intro y
  obtain ⟨g, hgH, hgy⟩ :=
    (mem_barSub V₀ V hV (L ⊔ D.T) (y : MulAut (Vtil V₀ V hV))).1 y.2
  refine ⟨⟨(g : G), hgH⟩, ?_⟩
  apply Subtype.ext
  change actTil V₀ V hV ⟨(g : G), hHstab hgH⟩ = (y : MulAut (Vtil V₀ V hV))
  have hval : (⟨(g : G), hHstab hgH⟩ : stabTil V₀ V) = g := rfl
  rw [hval]
  exact hgy

theorem gap17_25_barSub_normal {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (hMnorm : D.M ≤ normalizer (L : Set G)) :
    ((barSub V₀ V c.hyp125.isElemAbelian L).subgroupOf
      (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))).Normal := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hpair := c.hyp125.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  have hTstab : D.T ≤ stabTil V₀ V :=
    hTM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  set K : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  set S : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (L ⊔ D.T)
  have hYsup : Y = K ⊔ S := s16c7_barSub_sup V₀ V hV hLstab hTstab
  have hKH : K ≤ Y := by
    rw [hYsup]
    exact le_sup_left
  have hSM : S ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hTM
  have hMbarN : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V hV))) :=
    mbar_le_normalizer_barSub c.hyp125 hLM hMnorm
  change (K.subgroupOf Y).Normal
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH, hYsup]
  exact sup_le Subgroup.le_normalizer (hSM.trans hMbarN)

theorem gap17_25_barSub_isSpor {D : Data G}
    {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2)
    (hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥) :
    IsSpor ↥((barSub V₀ V c.hyp125.isElemAbelian L).subgroupOf
      (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))) .J2 := by
  have hbar : IsSpor ↥(barSub V₀ V c.hyp125.isElemAbelian L) .J2 :=
    isSpor_barSub_of_J2 c.hyp125 c hJ2 hL1
  have hle : barSub V₀ V c.hyp125.isElemAbelian L ≤
      barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T) :=
    barSub_mono V₀ V c.hyp125.isElemAbelian le_sup_left
  obtain ⟨e⟩ := hbar
  exact ⟨(Subgroup.subgroupOfEquivOfLe hle).trans e⟩

theorem gap17_25_barSub_T_sylow {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) :
    IsSylowIn 2 ((barSub V₀ V c.hyp125.isElemAbelian D.T).subgroupOf
      (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))) ⊤ := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hLM : L ≤ D.M := c.mem_calC.1.le
  set S : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (L ⊔ D.T)
  have hSY : S ≤ Y := barSub_mono V₀ V hV le_sup_right
  have hTsyl : IsSylowIn 2 S Y := isSylowIn_barSub_T_sup c.hyp125 hLM
  change IsSylowIn 2 (S.subgroupOf Y) ⊤
  refine ⟨le_top, ?_, ?_⟩
  · exact hTsyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSY).symm
  · have hindexS : (S.subgroupOf Y).index = S.relIndex Y := by
      rw [← Subgroup.relIndex_top_right (S.subgroupOf Y), ← Subgroup.subgroupOf_self Y]
      exact Subgroup.relIndex_subgroupOf (H := S) (K := Y) (L := Y) le_rfl
    rw [Subgroup.relIndex_top_right, hindexS]
    exact hTsyl.not_dvd_relIndex

theorem gap17_25_H1_eq_comap {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) :
    (H17_25_one D V₀ V L c.hyp125.isElemAbelian).subgroupOf (L ⊔ D.T) =
      (Subgroup.centralizer (((Subgroup.center
          ((barSub V₀ V c.hyp125.isElemAbelian D.T).subgroupOf
            (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T)))).map
          ((barSub V₀ V c.hyp125.isElemAbelian D.T).subgroupOf
            (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))).subtype) :
          Set ↥(barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T)))).comap
        (gap17_25_action c.hyp125 c) := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hpair := c.hyp125.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hHstab : L ⊔ D.T ≤ stabTil V₀ V :=
    (sup_le hLM hTM).trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  set H : Subgroup G := L ⊔ D.T
  set S : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV H with hYdef
  have hSY : S ≤ Y := by
    rw [hYdef]
    exact barSub_mono V₀ V hV le_sup_right
  have hWY : (Subgroup.center S).map S.subtype ≤ Y :=
    (Subgroup.map_subtype_le (H := S) (K := Subgroup.center S)).trans hSY
  let Xbar : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set _)
  let HbY : Subgroup ↥Y := Xbar.subgroupOf Y
  let f : ↥H →* ↥Y := gap17_25_action c.hyp125 c
  have hcent : HbY = Subgroup.centralizer (((Subgroup.center (S.subgroupOf Y)).map
      (S.subgroupOf Y).subtype) : Set ↥Y) := by
    rw [CFSG.GroupTheory.map_center_subgroupOf_eq_subgroupOf_map_center Y S hSY]
    exact CFSG.CGT.PushingUpLit.BHS7.subgroupOf_centralizer Y
      ((Subgroup.center S).map S.subtype) hWY
  have hH1eq : (H17_25_one D V₀ V L hV).subgroupOf H = HbY.comap f := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    change (x : G) ∈ preBarSub H V₀ V hV Xbar ↔ x ∈ HbY.comap f
    rw [mem_preBarSub, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨-, hxstab, hxbar⟩
      have hval : (⟨(x : G), hxstab⟩ : stabTil V₀ V) = ⟨(x : G), hHstab x.2⟩ := rfl
      rw [hval] at hxbar
      exact hxbar
    · intro hx
      exact ⟨x.2, hHstab x.2, hx⟩
  change (H17_25_one D V₀ V L hV).subgroupOf H =
    (Subgroup.centralizer (((Subgroup.center (S.subgroupOf Y)).map
      (S.subgroupOf Y).subtype) : Set ↥Y)).comap f
  rw [hH1eq, hcent]

theorem gap17_25_H1_shape_core
    (D : Data G) (V₀ V : Subgroup G)
    (hK2 : K_J2_centralizer_shape)
    (L : Subgroup G) (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2)
    (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G))
    (hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥) :
    Nonempty (Bar2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Bar2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≃* Equiv.Perm (Fin 5)) := by
  classical
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hH1le : H17_25_one D V₀ V L c.hyp125.isElemAbelian ≤ L ⊔ D.T := inf_le_left
  set Y := barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T)
  set S : Subgroup ↥Y := (barSub V₀ V c.hyp125.isElemAbelian D.T).subgroupOf Y
  obtain ⟨n, hn⟩ := exists_index_barSub_pow_two c.hyp125 c hMnorm
  obtain ⟨e2⟩ := bar2_comap_mulEquiv (gap17_25_action c.hyp125 c)
    (gap17_25_action_surjective c) (gap17_25_action_ker_isPGroup c.hyp125 c hMnorm hsimple hL1)
    (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set ↥Y))
  have e : Bar2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≃*
      Bar2 (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set ↥Y)) :=
    (bar2Equiv (Subgroup.subgroupOfEquivOfLe hH1le).symm).trans
      ((bar2Equiv (MulEquiv.subgroupCongr (gap17_25_H1_eq_comap c))).trans e2)
  exact (hK2 ↥Y _ (gap17_25_barSub_normal c hMnorm) (gap17_25_barSub_isSpor c hJ2 hL1)
    ⟨n, hn⟩ S (gap17_25_barSub_T_sylow c)).imp (Nonempty.map e.trans) (Nonempty.map e.trans)

theorem gap17_25_H1_shape_of
    (D : Data G) (V₀ V : Subgroup G)
    (h17_20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V)
    (hK2 : K_J2_centralizer_shape)
    (L : Subgroup G) (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2) :
    Nonempty (Bar2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Bar2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≃* Equiv.Perm (Fin 5)) :=
  gap17_25_H1_shape_core D V₀ V hK2 L c hJ2
    ((Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h17_20 L c).2.1)
    (gap17_25_barSub_L_ne_bot c h17_20 hC117)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
