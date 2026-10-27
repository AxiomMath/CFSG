module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec42Cond
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralQuot
import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open RootHyp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem xOf_le_normalizer_Pc (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) :
    Tim79a.xOf V H ≤ Subgroup.normalizer (Pc M V : Set G) := by
  have hW_M : Tim79a.xOf V H ≤ M := xOf_le_M h hPH hVH
  have hW_CV : Tim79a.xOf V H ≤ Subgroup.centralizer (V : Set G) := by
    have hEab := isElemAbelian_xOf h hPH hVH
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hEab.1 hw) v
        (le_xOf_self V H hv))
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  refine le_inf ?_ ?_
  · have hQnorm : Tim79a.xOf V H ≤ Subgroup.normalizer
        (inSubgroup (pCore 2) M : Set G) :=
      hW_M.trans (inSubgroup_pCore_two M).2.2
    exact (Subgroup.commutator_mono le_rfl inf_le_left).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hQnorm)
  · rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le (K := Subgroup.centralizer (V : Set G))).mpr ?_
    rintro x ⟨w, hw, p, hp, rfl⟩
    have hwC : w ∈ Subgroup.centralizer (V : Set G) := hW_CV hw
    have hpC : p ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp hp).2
    exact (Subgroup.centralizer (V : Set G)).mul_mem
      ((Subgroup.centralizer (V : Set G)).mul_mem
        ((Subgroup.centralizer (V : Set G)).mul_mem hwC hpC)
        ((Subgroup.centralizer (V : Set G)).inv_mem hwC))
      ((Subgroup.centralizer (V : Set G)).inv_mem hpC)


private theorem pCore_HBar_le_normalizer_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :
    CFSG.pCore 2 (HBar V H) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
  classical
  obtain ⟨y, hyH, -, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  let T : Subgroup (HBar V H) := imgK V H (Pc M V)
  have hT : IsPGroup 2 T := (isElemAbelian_imgK h hPH hVH).isPGroup
  have hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set (HBar V H))) := by
    refine ⟨Subgroup.le_normalizer, ?_⟩
    intro g hg
    obtain ⟨x, rfl⟩ := piK_surjective V H g
    have hconj : conjSubgroup (piK V H x) T =
        imgK V H (conjSubgroup (x : G) (Pc M V)) :=
      (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) x.2 hPH).symm
    rw [hconj] at hg ⊢
    exact weaklyClosed_imgK h hPH x.2 hg
  obtain ⟨S, hSN, hTS⟩ :=
    CFSG.RankThree.GF2n.Tim81.CentralTI.exists_sylow_le_normalizer hT hwc
  have hOS : CFSG.pCore 2 (HBar V H) ≤ S :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := HBar V H)) S
  exact hOS.trans hSN

private theorem mem_normalizer_conj_V_of_mem_pCore (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ g : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hg : g ∈ H) {o : G} (hoH : o ∈ H)
    (hoO : piK V H ⟨o, hoH⟩ ∈ CFSG.pCore 2 (HBar V H)) :
    o ∈ Subgroup.normalizer (conjSubgroup g V : Set G) := by
  classical
  let T : Subgroup (HBar V H) := imgK V H (Pc M V)
  have hO_le_NT := pCore_HBar_le_normalizer_imgK h hPH hVH hH
  have hPgH : conjSubgroup g (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg
  have hO_norm : CFSG.pCore 2 (HBar V H) ≤
      Subgroup.normalizer (imgK V H (conjSubgroup g (Pc M V)) : Set (HBar V H)) := by
    have hOconj : conjSubgroup (piK V H ⟨g, hg⟩) (CFSG.pCore 2 (HBar V H)) =
        CFSG.pCore 2 (HBar V H) := by
      rw [conjSubgroup_eq_self_iff, Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have hSconj : conjSubgroup (piK V H ⟨g, hg⟩) (T : Subgroup (HBar V H)) =
        imgK V H (conjSubgroup g (Pc M V)) :=
      (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) hg hPH).symm
    calc CFSG.pCore 2 (HBar V H) =
          conjSubgroup (piK V H ⟨g, hg⟩) (CFSG.pCore 2 (HBar V H)) := hOconj.symm
      _ ≤ conjSubgroup (piK V H ⟨g, hg⟩)
            (Subgroup.normalizer (T : Set (HBar V H))) := Subgroup.map_mono hO_le_NT
      _ = Subgroup.normalizer (conjSubgroup (piK V H ⟨g, hg⟩) T : Set (HBar V H)) :=
          (normalizer_conjSubgroup _ _).symm
      _ = Subgroup.normalizer (imgK V H (conjSubgroup g (Pc M V)) : Set (HBar V H)) := by
          rw [hSconj]
  have hpiO : piK V H ⟨o, hoH⟩ ∈
      Subgroup.normalizer (imgK V H (conjSubgroup g (Pc M V)) : Set (HBar V H)) :=
    hO_norm hoO
  have hconjImg : imgK V H (conjSubgroup o (conjSubgroup g (Pc M V))) =
      imgK V H (conjSubgroup g (Pc M V)) := by
    rw [imgK_conjSubgroup (V := V) (H := H) (S := conjSubgroup g (Pc M V)) hoH hPgH]
    exact conjSubgroup_eq_self_iff.mpr hpiO
  have hsup : conjSubgroup o (conjSubgroup g (Pc M V)) ⊔ kOf V H =
      conjSubgroup g (Pc M V) ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq (V := V) (H := H)
      (conjSubgroup_le_of_le_of_mem hPgH hoH) hPgH).mp hconjImg
  have hPK : o ∈ Subgroup.normalizer
      ((conjSubgroup g (Pc M V) ⊔ kOf V H : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    rw [show conjSubgroup o (conjSubgroup g (Pc M V) ⊔ kOf V H) =
      conjSubgroup o (conjSubgroup g (Pc M V)) ⊔ conjSubgroup o (kOf V H)
      from Subgroup.map_sup _ _ _,
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hoH), hsup]
  have hW : o ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H hoH
  have hC : o ∈ Subgroup.normalizer
      (Subgroup.centralizer ((conjSubgroup g (Pc M V) ⊔ kOf V H : Subgroup G) : Set G)) :=
    mem_normalizer_centralizer hPK
  have hinf := mem_normalizer_inf hW hC
  rwa [RootHyp.xOf_inf_centralizer_sup_kOf_eq h hPH hg] at hinf


private theorem pCore_le_center_of_inf_imgK_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hD : imgK V H (Pc M V) ⊓ CFSG.pCore 2 (HBar V H) = ⊥) :
    CFSG.pCore 2 (HBar V H) ≤ Subgroup.center (HBar V H) := by
  classical
  obtain ⟨y, hyH, -, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  let T : Subgroup (HBar V H) := imgK V H (Pc M V)
  let O : Subgroup (HBar V H) := CFSG.pCore 2 (HBar V H)
  have hgen : Subgroup.normalClosure (T : Set (HBar V H)) = ⊤ := by
    simpa [T] using normalClosure_imgK_eq_top h hPH hyH hHy
  have hO_le_NT : O ≤ Subgroup.normalizer (T : Set (HBar V H)) := by
    simpa [O, T] using pCore_HBar_le_normalizer_imgK h hPH hVH hH
  have hTnormO : T ≤ Subgroup.normalizer (O : Set (HBar V H)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hD' : T ⊓ O = ⊥ := by simpa [T, O] using hD
  have hcommT : ⁅O, T⁆ ≤ T :=
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hO_le_NT)
  have hcommO : ⁅O, T⁆ ≤ O :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hTnormO)
  have hcomm_bot : ⁅O, T⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf hcommT hcommO).trans (le_of_eq hD')
  have hT_le_CO : T ≤ Subgroup.centralizer (O : Set (HBar V H)) := by
    rw [Subgroup.commutator_comm] at hcomm_bot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  have hY_le_CO : (⊤ : Subgroup (HBar V H)) ≤
      Subgroup.centralizer (O : Set (HBar V H)) := by
    rw [← hgen]
    exact Subgroup.normalClosure_le_normal hT_le_CO
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro z
  have hz : z ∈ Subgroup.centralizer (O : Set (HBar V H)) := hY_le_CO (Subgroup.mem_top z)
  exact (Subgroup.mem_centralizer_iff.mp hz o ho).symm

private theorem centralizes_conj_V_of_mem_pCore
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    {x : ↥H} (hxP : (x : G) ∈ Pc M V)
    (hxO : piK V H x ∈ CFSG.pCore 2 (HBar V H)) :
    ∀ g : G, g ∈ H → (x : G) ∈ Subgroup.centralizer (conjSubgroup g V : Set G) := by
  intro g hg
  let Vg : Subgroup G := conjSubgroup g V
  have hVgW : Vg ≤ Tim79a.xOf V H :=
    Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hg)
  have hVgM : Vg ≤ M := hVgW.trans (xOf_le_M h hPH hVH)
  have hVgNP : Vg ≤ Subgroup.normalizer (Pc M V : Set G) :=
    hVgW.trans (xOf_le_normalizer_Pc h hPH hVH)
  have hxN : (x : G) ∈ Subgroup.normalizer (Vg : Set G) :=
    mem_normalizer_conj_V_of_mem_pCore h hPH hVH hH hg x.2 hxO
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  by_contra hvcomm
  have hcomm1 : ⁅(x : G), v⁆ ≠ 1 := by
    intro h1
    apply hvcomm
    rw [commutatorElement_eq_one_iff_commute] at h1
    exact h1.eq.symm
  have hxd : (x : G) ∈ Pc M V := hxP
  have hcommVg : ⁅(x : G), v⁆ ∈ Vg := by
    rw [← commutatorElement_inv]
    exact Vg.inv_mem (CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hv hxN)
  have hcommP : ⁅(x : G), v⁆ ∈ Pc M V :=
    CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hxd (hVgNP hv)
  have hVgQ : Vg ⊓ inSubgroup (pCore 2) M ≠ ⊥ := by
    intro hbot
    have hmem : ⁅(x : G), v⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hcommVg, (Subgroup.mem_inf.mp hcommP).1⟩
    exact hcomm1 (Subgroup.mem_bot.mp hmem)
  have hVgP : Vg ≤ Pc M V := by
    rcases h.toHyp.conj_le_Pc_or_inf_eq_bot h.rootType hVgM with hle | hbot
    · exact hle
    · exact absurd hbot hVgQ
  have hvP : v ∈ Pc M V := hVgP hv
  have hcommPhi : ⁅(x : G), v⁆ ∈ inSubgroup frattini (Pc M V) := by
    have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
    have hmem := CFSG.SectionRank.Ccomm.commutator_mem_frattini
      (p := 2) hP2 ⟨(x : G), hxd⟩ ⟨v, hvP⟩
    change ⁅(x : G), v⁆ ∈ Subgroup.map (Pc M V).subtype
      (frattini ↥(Pc M V))
    exact Subgroup.mem_map_of_mem (Pc M V).subtype hmem
  have hcommV : ⁅(x : G), v⁆ ∈ V := h.toHyp.frattini_Pc_le hcommPhi
  have hVgNe : Vg ≠ V := by
    intro heq
    apply hvcomm
    have hxCV : (x : G) ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_inf.mp hxd).2
    rw [← heq] at hxCV
    exact (Subgroup.mem_centralizer_iff.mp hxCV v hv)
  have hVgBot : Vg ⊓ V = ⊥ := by
    rcases h.toHyp.ti g with hbot | heq
    · rwa [inf_comm] at hbot
    · have hVle : V ≤ Vg := heq ▸ inf_le_right
      exact absurd (conjSubgroup_eq_of_ge hVle) hVgNe
  have hmemBot : ⁅(x : G), v⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hVgBot]
    exact ⟨hcommVg, hcommV⟩
  exact hcomm1 (Subgroup.mem_bot.mp hmemBot)

theorem RootHyp.pCore_HBar_le_center (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :
    CFSG.pCore 2 (HBar V H) ≤ Subgroup.center (HBar V H) := by
  classical
  obtain ⟨y, hyH, -, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  let Y : Type := HBar V H
  let T : Subgroup Y := imgK V H (Pc M V)
  let O : Subgroup Y := CFSG.pCore 2 Y
  have hT_el : Assembly.IsElemAbelian 2 T := isElemAbelian_imgK h hPH hVH
  have hT_pg : IsPGroup 2 T := hT_el.isPGroup
  have hgen : Subgroup.normalClosure (T : Set Y) = ⊤ := by
    simpa [T, Y] using normalClosure_imgK_eq_top h hPH hyH hHy
  by_cases hD : T ⊓ O = ⊥
  · exact pCore_le_center_of_inf_imgK_eq_bot h hPH hVH hH (by simpa [T, O, Y] using hD)
  ·
    obtain ⟨dbar, hdbar_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    have hdbarT : (dbar : Y) ∈ T := (Subgroup.mem_inf.mp dbar.2).1
    have hdbarO : (dbar : Y) ∈ O := (Subgroup.mem_inf.mp dbar.2).2
    have hdbar1 : (dbar : Y) ≠ 1 := by
      intro h
      exact hdbar_ne (Subtype.ext h)
    obtain ⟨x, hxP, hxpi⟩ := mem_imgK_iff.mp hdbarT
    have hxH : (x : G) ∈ H := hPH hxP
    have hxO : piK V H ⟨(x : G), hxH⟩ ∈ O := by
      rwa [hxpi]
    have hdK : (x : G) ∈ kOf V H := by
      by_contra hxK
      have hxbar1 : piK V H ⟨(x : G), hxH⟩ ≠ 1 := by
        intro h
        exact hxK ((piK_eq_one_iff _).mp h)
      have hxcent : ∀ g : G, g ∈ H → (x : G) ∈
          Subgroup.centralizer (conjSubgroup g V : Set G) :=
        centralizes_conj_V_of_mem_pCore h hPH hVH hH hxP (by simpa [O] using hxO)
      apply hxK
      rw [mem_kOf_iff]
      refine ⟨hxH, ?_⟩
      have hW_le_Cx : Tim79a.xOf V H ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
        refine iSup₂_le fun U hU => ?_
        obtain ⟨g, hg, rfl⟩ := hU
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (Subgroup.mem_centralizer_iff.mp (hxcent g hg) w hw).symm
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp (hW_le_Cx hw) (x : G) (by simp)).symm
    have hxbar1' : piK V H ⟨(x : G), hxH⟩ = 1 := (piK_eq_one_iff _).mpr hdK
    exact absurd (hxpi.symm.trans hxbar1') hdbar1

theorem RootHyp.four_le_card_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    4 ≤ Nat.card (imgK V H (Pc M V)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := isElemAbelian_imgK h hPH hVH
  have hTp : IsPGroup 2 ↥(imgK V H (Pc M V)) := CFSG.Open.IsElemAbelian.isPGroup hT
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(imgK V H (Pc M V)))).mp hTp
  have hne := (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).1
  have hn0 : n ≠ 0 := by
    intro h0
    apply hne
    have hc : Nat.card (imgK V H (Pc M V)) = 1 := by rw [hn, h0, pow_zero]
    exact Subgroup.card_eq_one.mp hc
  have hn1 : n ≠ 1 := by
    intro h1
    apply false_of_card_imgK_eq_two h hPH hVH hH hnM
    rw [hn, h1]
    norm_num
  have hn2 : 2 ≤ n := by omega
  rw [hn]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

theorem RootHyp.not_normal_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    ¬ (imgK V H (Pc M V)).Normal := by
  classical
  intro hN
  haveI : (imgK V H (Pc M V)).Normal := hN
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hne := (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).2
  have hconj : conjSubgroup (piK V H ⟨y, hyH⟩) (imgK V H (Pc M V)) =
      imgK V H (Pc M V) := by
    rw [conjSubgroup_eq_self_iff, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hEq : imgK V H (conjSubgroup y (Pc M V)) = imgK V H (Pc M V) := by
    rw [imgK_conjSubgroup hyH hPH]
    exact hconj
  rw [← hPy] at hEq
  exact hne hEq.symm

theorem RootHyp.isWC_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) : IsWC (imgK V H (Pc M V)) := by
  refine CentralTI.isWC_of_isTI (isElemAbelian_imgK h hPH hVH) (isTI_imgK h hPH hVH) ?_
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro gbar hg
  obtain ⟨x, rfl⟩ := piK_surjective V H gbar
  have hconj : conjSubgroup (piK V H x) (imgK V H (Pc M V)) =
      imgK V H (conjSubgroup (x : G) (Pc M V)) :=
    (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) x.2 hPH).symm
  rw [hconj] at hg ⊢
  exact weaklyClosed_imgK h hPH x.2 hg

theorem RootHyp.le_center_of_odd_normal (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (O : Subgroup (HBar V H)) [O.Normal] (hO : Odd (Nat.card O)) :
    O ≤ Subgroup.center (HBar V H) := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  let Y := HBar V H
  let T : Subgroup Y := imgK V H (Pc M V)
  have hT := isElemAbelian_imgK h hPH hVH
  have hTI := isTI_imgK h hPH hVH
  have h4 := four_le_card_imgK h hPH hVH hH hnM
  have hgen : Subgroup.normalClosure (T : Set Y) = ⊤ := by
    simpa [T, Y] using normalClosure_imgK_eq_top h hPH hyH hHy
  have hTO : T ≤ Subgroup.normalizer (O : Set Y) :=
    Subgroup.le_normalizer_of_normal (H := O)
  have hOT : O ≤ Subgroup.centralizer (T : Set Y) :=
    CentralTI.le_centralizer_of_odd_card hT h4 hTI hTO hO
  have hT_le_CO : T ≤ Subgroup.centralizer (O : Set Y) :=
    Subgroup.le_centralizer_iff.mpr hOT
  have hle : Subgroup.normalClosure (T : Set Y) ≤ Subgroup.centralizer (O : Set Y) :=
    Subgroup.normalClosure_le_normal hT_le_CO
  have htop_le : (⊤ : Subgroup Y) ≤ Subgroup.centralizer (O : Set Y) := by
    rw [← hgen]
    exact hle
  have hO_le_center : O ≤ Subgroup.centralizer (⊤ : Subgroup Y) :=
    Subgroup.le_centralizer_iff.mp htop_le
  simpa [Y, Subgroup.centralizer_univ] using hO_le_center

theorem RootHyp.le_center_of_isNilpotent_normal (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (E : Subgroup (HBar V H)) [E.Normal] (hE : Group.IsNilpotent ↥E) :
    E ≤ Subgroup.center (HBar V H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := HBar V H
  have hEY : E ≤ Subgroup.center Y := by
    refine (normal_nilpotent_le_sup_pCore (G := Y) (N := E) ‹E.Normal› hE).trans ?_
    refine iSup_le fun p => ?_
    haveI : Fact (Nat.Prime p.1.1) := ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
    by_cases hp2 : p.1.1 = 2
    · rw [hp2]
      simpa [Y] using pCore_HBar_le_center h hPH hVH hH
    · have hpodd : Odd p.1.1 :=
        (Nat.prime_of_mem_primeFactors p.1.2).odd_of_ne_two hp2
      have hcard : Odd (Nat.card (CFSG.pCore p.1.1 Y)) := by
        obtain ⟨n, hn⟩ :=
          (IsPGroup.iff_card (p := p.1.1) (G := ↥(CFSG.pCore p.1.1 Y))).mp
            (CFSG.pCore_isPGroup (G := Y) (p := p.1.1))
        rw [hn]
        exact Odd.pow hpodd
      exact le_center_of_odd_normal h hPH hVH hH hnM (CFSG.pCore p.1.1 Y) hcard
  simpa [Y] using hEY

theorem RootHyp.le_center_of_isSolvable_normal (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (R : Subgroup (HBar V H)) [R.Normal] (hR : Group.IsSolvable ↥R) :
    R ≤ Subgroup.center (HBar V H) := by
  classical
  let Y := HBar V H
  let F : Subgroup Y := fittingSubgroupOf (G := Y) R
  have hF_normal : F.Normal := fittingSubgroupOf_normal R ‹R.Normal›
  have hF_nil : Group.IsNilpotent ↥F := fittingSubgroupOf_isNilpotent R
  haveI : F.Normal := hF_normal
  have hF_center : F ≤ Subgroup.center Y :=
    le_center_of_isNilpotent_normal h hPH hVH hH hnM F hF_nil
  have hR_le_C : R ≤ Subgroup.centralizer (F : Set Y) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (Subgroup.mem_center_iff.mp (hF_center hf) r).symm
  have hcent := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥R) hR
  have hR_le_F : R ≤ F := by
    intro r hr
    have hmem : (⟨r, hr⟩ : ↥R) ∈
        Subgroup.centralizer (fittingSubgroup ↥R : Set ↥R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyF : (y : Y) ∈ F := Subgroup.mem_map_of_mem R.subtype hy
      exact Subtype.ext (hR_le_C hr (y : Y) hyF)
    exact Subgroup.mem_map_of_mem R.subtype (hcent hmem)
  exact hR_le_F.trans hF_center

theorem RootHyp.not_isSolvable_HBar (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    ¬ Group.IsSolvable (HBar V H) := by
  classical
  intro hsolv
  have hsolv_top : Group.IsSolvable ↥(⊤ : Subgroup (HBar V H)) := inferInstance
  have htop_le : (⊤ : Subgroup (HBar V H)) ≤ Subgroup.center (HBar V H) :=
    le_center_of_isSolvable_normal h hPH hVH hH hnM ⊤ hsolv_top
  have hcenter : Subgroup.center (HBar V H) = ⊤ :=
    le_antisymm le_top htop_le
  haveI : IsMulCommutative (HBar V H) := Subgroup.center_eq_top_iff.mp hcenter
  exact not_normal_imgK h hPH hH hnM (Subgroup.normal_of_isMulCommutative _)

private theorem isSolvable_comap_mk {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    {Z₀ : Subgroup (G ⧸ N)} (hNcomm : IsMulCommutative ↥N)
    (hZ₀_center : Z₀ ≤ Subgroup.center (G ⧸ N)) :
    Group.IsSolvable ↥(Z₀.comap (QuotientGroup.mk' N)) := by
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Z₂ : Subgroup G := Z₀.comap π
  have hN_le_Z₂ : N ≤ Z₂ := by
    intro n hn
    exact Subgroup.mem_comap.mpr (by
      have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [h1]
      exact Z₀.one_mem)
  have hZ₀_comm : IsMulCommutative ↥Z₀ := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_center_iff.mp (hZ₀_center a.2) b).symm
  haveI : IsMulCommutative ↥Z₀ := hZ₀_comm

  haveI : IsMulCommutative ↥N := hNcomm
  haveI : (N.subgroupOf Z₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_Z₂).mpr
      (Subgroup.le_normalizer_of_normal (H := N))
  haveI : IsMulCommutative ↥(N.subgroupOf Z₂) := inferInstance
  have hψ_surj : Function.Surjective
      (MonoidHom.codRestrict (π.comp Z₂.subtype) Z₀ (fun x => x.2)) := by
    intro z
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (z : G ⧸ N)
    refine ⟨⟨y, ?_⟩, ?_⟩
    · exact Subgroup.mem_comap.mpr (by rw [hy]; exact z.2)
    · apply Subtype.ext
      exact hy
  have hψ_ker : MonoidHom.ker (MonoidHom.codRestrict (π.comp Z₂.subtype) Z₀
      (fun x => x.2)) = N.subgroupOf Z₂ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : G)).mp (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx
  have hquot_iso : (↥Z₂ ⧸ N.subgroupOf Z₂) ≃* ↥Z₀ :=
    (QuotientGroup.quotientMulEquivOfEq hψ_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hψ_surj)
  haveI : Group.IsSolvable ↥(N.subgroupOf Z₂) := inferInstance
  haveI : Group.IsSolvable (↥Z₂ ⧸ N.subgroupOf Z₂) :=
    Group.isSolvable_of_surjective (f := hquot_iso.symm.toMonoidHom)
      hquot_iso.symm.surjective
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf Z₂)

private theorem RootHyp.exists_listGroup_quot_of_covering (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {N : Subgroup (HBar V H)} [N.Normal] (hN : Assembly.IsElemAbelian 2 N)
    (hcov : IsCoveringOfList (HBar V H ⧸ N)) :
    ∃ Z : Subgroup (HBar V H), Z ≤ Subgroup.center (HBar V H) ∧
      ∃ _ : Z.Normal, ListGroup (HBar V H ⧸ Z) := by
  classical
  obtain ⟨-, Z₀, hZ₀_center, hZ₀_normal, hList⟩ := hcov
  haveI : Z₀.Normal := hZ₀_normal
  let π : HBar V H →* HBar V H ⧸ N := QuotientGroup.mk' N
  let Z₂ : Subgroup (HBar V H) := Z₀.comap π
  have hZ₂_normal : Z₂.Normal := by
    dsimp [Z₂]
    infer_instance
  haveI : Z₂.Normal := hZ₂_normal
  have hN_le_Z₂ : N ≤ Z₂ := by
    intro n hn
    exact Subgroup.mem_comap.mpr (by
      have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [h1]
      exact Z₀.one_mem)
  have hZ₀_comm : IsMulCommutative ↥Z₀ := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_center_iff.mp (hZ₀_center a.2) b).symm
  haveI : IsMulCommutative ↥Z₀ := hZ₀_comm
  have hZ₂_solv : Group.IsSolvable ↥(Z₀.comap (QuotientGroup.mk' N)) :=
    isSolvable_comap_mk hN.1 hZ₀_center
  have hZ₂_center : Z₂ ≤ Subgroup.center (HBar V H) :=
    le_center_of_isSolvable_normal h hPH hVH hH hnM Z₂ hZ₂_solv
  refine ⟨Z₂, hZ₂_center, hZ₂_normal, ?_⟩
  have hmap : Z₂.map π = Z₀ := by
    dsimp [Z₂, π]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Z₀
  have e : HBar V H ⧸ Z₂ ≃* (HBar V H ⧸ N) ⧸ Z₀ := by
    have h := (QuotientGroup.quotientQuotientEquivQuotient (G := HBar V H) (N := N)
      (M := Z₂) hN_le_Z₂).symm
    exact h.trans (QuotientGroup.quotientMulEquivOfEq hmap)
  exact ListGroup.of_mulEquiv e.symm hList

theorem RootHyp.exists_listGroup_quot (hA : TheoremAStmt) (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    ∃ Z : Subgroup (HBar V H), Z ≤ Subgroup.center (HBar V H) ∧
      ∃ _ : Z.Normal, ListGroup (HBar V H ⧸ Z) := by
  classical
  let Y := HBar V H
  let T : Subgroup Y := imgK V H (Pc M V)
  have hT := isElemAbelian_imgK h hPH hVH
  have hTI := isTI_imgK h hPH hVH
  have h4 := four_le_card_imgK h hPH hVH hH hnM
  have hnotNormal := not_normal_imgK h hPH hH hnM
  have hWC : IsWC T := isWC_imgK h hPH hVH
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hgen : Subgroup.normalClosure (T : Set Y) = ⊤ := by
    simpa [T, Y] using normalClosure_imgK_eq_top h hPH hyH hHy
  have hconcl : ConclusionFor Y := by
    have h1 : ThmAConclusion T := hA Y T hWC
    have h1' : ConclusionFor ↥(Subgroup.normalClosure (T : Set Y)) :=
      (thmAConclusion_iff T).mp h1
    have e : ↥(Subgroup.normalClosure (T : Set Y)) ≃* Y := by
      rw [hgen]
      exact Subgroup.topEquiv
    exact conclusionFor_of_mulEquiv e h1'
  obtain ⟨N, hN_normal, hN_elem, hcase⟩ := hconcl
  haveI : N.Normal := hN_normal
  have hNp : IsPGroup 2 ↥N := CFSG.Open.IsElemAbelian.isPGroup hN_elem
  have hN_le_pCore : N ≤ CFSG.pCore 2 Y := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup₂_of_le N hN_normal (le_iSup_of_le hNp le_rfl)
  have hN_le_center : N ≤ Subgroup.center Y :=
    hN_le_pCore.trans (pCore_HBar_le_center h hPH hVH hH)
  rcases hcase with hZ | hcov
  · exfalso
    exact hnotNormal (CentralTI.zstar_normal (T := T) (N := N) hT h4 hTI hgen
      hN_le_center hNp hZ)
  · simpa [Y] using exists_listGroup_quot_of_covering h hPH hVH hH hnM hN_elem hcov

end CFSG.RankThree.GF2n.Tim81
