module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

theorem conjSubgroup_map_hom {K : Type*} [Group K] (f : G →* K) (A : Subgroup G) (x : G) :
    conjSubgroup (f x) (A.map f) = (conjSubgroup x A).map f := by
  ext y
  rw [mem_conjSubgroup, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hay⟩
    refine ⟨x * a * x⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup, show x⁻¹ * (x * a * x⁻¹) * x = a by group]; exact ha
    · rw [map_mul, map_mul, map_inv, hay]; group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨x⁻¹ * a * x, mem_conjSubgroup.mp ha, ?_⟩
    rw [map_mul, map_mul, map_inv]

theorem subgroupOf_conjSubgroup (H A : Subgroup G) (x : ↥H) :
    (conjSubgroup (x : G) A).subgroupOf H = conjSubgroup x (A.subgroupOf H) := by
  ext y
  simp only [Subgroup.mem_subgroupOf, mem_conjSubgroup]
  rfl

theorem pCoreOf_top_subgroupOf (X : Subgroup G) :
    pCoreOf 2 (⊤ : Subgroup X) = (pCoreOf 2 X).subgroupOf X := by
  have h1 : pCoreOf 2 (⊤ : Subgroup X) = CFSG.pCore 2 ↥X := by
    rw [pCoreOf]
    change (CFSG.pCore 2 (⊤ : Subgroup X)).map
      (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom = CFSG.pCore 2 ↥X
    exact CFSG.pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
  rw [h1]
  exact (CFSG.openPCoreOf_subgroupOf 2 X).symm

variable [Finite G]


theorem tim79a_seven_three_four_ti_inH {V H E J : Subgroup G}
    (hV : Assembly.IsElemAbelian 2 V) (hTI : IsTI V) (hVH : V ≤ H)
    (hE : IsMulCommutative E) (hEH : E ≤ H) (hEn : (E.subgroupOf H).Normal)
    (hEV : ∀ g ∈ H, E ⊓ conjSubgroup g V ≠ ⊥)
    (hVO : ¬ V ≤ pCoreOf 2 H)
    (hJ : J ≤ pCoreOf 2 H) (hJn : (J.subgroupOf H).Normal)
    (hIJ : ∀ g ∈ H, conjSubgroup g V ⊓ pCoreOf 2 H ≤ J)
    {h : G} (hh : h ∈ H) {a a' : G} (ha : a ∈ V) (haJ : a ∉ J)
    (ha' : a' ∈ conjSubgroup h V) (haJ' : a⁻¹ * a' ∈ J) :
    ∃ x ∈ J, conjSubgroup h V = conjSubgroup x V := by
  have hqc : ∀ g : ↥H, CFSG.Quasithin.conjSubgroup (V.subgroupOf H) g =
      (conjSubgroup ((g : G)⁻¹) V).subgroupOf H := by
    intro g
    have e := LocalAnalysis.WeakClosure81.t75_conjSubgroup_eq (V.subgroupOf H) g⁻¹
    rw [inv_inv] at e
    rw [← e]
    have := subgroupOf_conjSubgroup H V g⁻¹
    rw [Subgroup.coe_inv] at this
    exact this.symm
  have hO : pCoreOf 2 (⊤ : Subgroup ↥H) = (pCoreOf 2 H).subgroupOf H := pCoreOf_top_subgroupOf H
  have hV' : IsElemAbelian 2 (V.subgroupOf H) :=
    CFSG.Open.IsElemAbelian.comap hV H.subtype_injective
  have hTI' : IsTI (V.subgroupOf H) := by
    intro g
    have e1 : conjSubgroup g (V.subgroupOf H) = (conjSubgroup (g : G) V).subgroupOf H :=
      (subgroupOf_conjSubgroup H V g).symm
    have e2 : V.subgroupOf H ⊓ (conjSubgroup (g : G) V).subgroupOf H =
        (V ⊓ conjSubgroup (g : G) V).subgroupOf H := by
      simp only [Subgroup.subgroupOf]
      rw [Subgroup.comap_inf]
    rw [e1, e2]
    rcases hTI (g : G) with h1 | h1
    · left; rw [h1]; simp
    · right; rw [h1]
  have hE' : IsMulCommutative (E.subgroupOf H) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (Subtype.val : ↥E → G)
      (hE.is_comm.comm ⟨(x.1 : G), x.2⟩ ⟨(y.1 : G), y.2⟩)
    exact h
  have hnormTop : ∀ {K : Subgroup G}, (K.subgroupOf H).Normal →
      ((K.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal := fun {K} hK =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2
      (Subgroup.normalizer_eq_top_iff.mpr hK).ge
  have hEV' : E.subgroupOf H ⊓ V.subgroupOf H ≠ ⊥ := by
    have := hEV 1 H.one_mem
    rw [conjSubgroup_one] at this
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp this
    intro hbot
    have hmem : (⟨x, hEH (Subgroup.mem_inf.mp hx).1⟩ : ↥H) ∈ E.subgroupOf H ⊓ V.subgroupOf H :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 (Subtype.ext (congrArg (Subtype.val : ↥H → G) hmem))
  have hVOm : V.subgroupOf H ∈ LocalAnalysis.WeakClosure81.omegaSet (V.subgroupOf H)
      (⊤ : Subgroup ↥H) (E.subgroupOf H) := by
    refine ⟨1, (CFSG.Quasithin.conjSubgroup_one _).symm, hEV', ?_⟩
    rw [hO]
    intro h'
    apply hVO
    intro v hv
    exact h' (show (⟨v, hVH hv⟩ : ↥H) ∈ V.subgroupOf H from hv)
  have hOmH : ∀ W ∈ LocalAnalysis.WeakClosure81.omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (E.subgroupOf H), W ≤ ⊤ := fun _ _ => le_top
  have hJ' : J.subgroupOf H ≤ pCoreOf 2 (⊤ : Subgroup ↥H) := by
    rw [hO]; exact fun x hx => hJ hx
  have hIJ' : LocalAnalysis.WeakClosure81.iSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (E.subgroupOf H) ≤ J.subgroupOf H := by
    unfold LocalAnalysis.WeakClosure81.iSub
    refine iSup₂_le fun U hU => ?_
    obtain ⟨g, rfl, -, -⟩ := LocalAnalysis.WeakClosure81.mem_omegaSet.mp hU
    rw [hqc g, hO]
    intro y hy
    exact hIJ _ (H.inv_mem g.2) ⟨(Subgroup.mem_inf.mp hy).1, (Subgroup.mem_inf.mp hy).2⟩
  have hUH : conjSubgroup h V ≤ H := conjSubgroup_le_of_le_of_mem hVH hh
  have key := LocalAnalysis.WeakClosure81.seven_three_four_ti (G := ↥H) (V := V.subgroupOf H)
    (H := ⊤) (E := E.subgroupOf H) (J := J.subgroupOf H) hV' hTI' hE' le_top (hnormTop hEn) hVOm
    hOmH hJ' (hnormTop hJn) hIJ' (h := (⟨h⁻¹, H.inv_mem hh⟩ : ↥H)) (Subgroup.mem_top _)
    (a := ⟨a, hVH ha⟩) (a' := ⟨a', hUH ha'⟩)
    (show (⟨a, hVH ha⟩ : ↥H) ∈ V.subgroupOf H from ha)
    (show (⟨a, hVH ha⟩ : ↥H) ∉ J.subgroupOf H from haJ)
    (by rw [hqc, Subgroup.mem_subgroupOf]; simpa using ha')
    (show ((⟨a, hVH ha⟩ : ↥H)⁻¹ * ⟨a', hUH ha'⟩) ∈ J.subgroupOf H from by
      rw [Subgroup.mem_subgroupOf]; simpa using haJ')
  obtain ⟨x, hxJ, hx⟩ := key
  rw [hqc, hqc] at hx
  have hxx : ((x : G))⁻¹ ∈ J := J.inv_mem hxJ
  refine ⟨(x : G)⁻¹, hxx, ?_⟩
  have hUH' : conjSubgroup ((x : G)⁻¹) V ≤ H := conjSubgroup_le_of_le_of_mem hVH (H.inv_mem x.2)
  have h2 := Subgroup.subgroupOf_inj.mp (by simpa using hx)
  rwa [inf_eq_left.mpr hUH, inf_eq_left.mpr hUH'] at h2

end CFSG.RankThree.GF2n.Tim79a
