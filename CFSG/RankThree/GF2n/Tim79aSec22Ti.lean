module

public import CFSG.RankThree.GF2n.Tim79aSec2O2
public import CFSG.RankThree.GF2n.Tim79aSec22Adapter

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

theorem conjSubgroup_piBar_barOf {V H : Subgroup G} (x : ↥H) (S : Subgroup G) :
    conjSubgroup (piBar V H x) (barOf V H S) = barOf V H (conjSubgroup (x : G) S) := by
  unfold barOf
  rw [conjSubgroup_map_hom, subgroupOf_conjSubgroup]

variable {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem inf_normalizer_conj_ne_bot {h : G} (hh : h ∈ H) :
    V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G) ≠ ⊥ := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.eOf_inf_V_ne_bot
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.eOf_inf_conj_ne_bot hh)
  obtain ⟨hxE, hxV⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyE, hyU⟩ := Subgroup.mem_inf.mp hy
  have hcomm : x * y = y * x :=
    congrArg Subtype.val ((isMulCommutative_eOf H).is_comm.comm ⟨x, hxE⟩ ⟨y, hyE⟩)
  have hxN : x ∈ Subgroup.normalizer (conjSubgroup h V : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti h) hyU
      (fun h' => hy1 (Subtype.ext h')) hcomm
  intro hbot
  have : x ∈ V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G) := ⟨hxV, hxN⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hx1 (Subtype.ext this)

theorem commute_of_isPGroup_sup_wOf {h : G} (hh : h ∈ H)
    (h2 : IsPGroup 2 ↥(V ⊔ conjSubgroup h V ⊔ wOf V H)) :
    ∀ u ∈ V, ∀ v ∈ conjSubgroup h V, u * v = v * u := by
  have hP : IsPGroup 2 ↥(V ⊔ conjSubgroup h V) := h2.to_le le_sup_left
  have hW' : conjSubgroup h V = CFSG.Quasithin.conjSubgroup V h⁻¹ :=
    LocalAnalysis.WeakClosure81.t75_conjSubgroup_eq V h
  exact LocalAnalysis.WeakClosure81.commute_of_isPGroup_sup (W := V) (W' := conjSubgroup h V)
    hc.elemAb hc.ti ⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩ ⟨h⁻¹, hW'⟩
    (hc.inf_normalizer_conj_ne_bot hh) hP

theorem isPGroup_barOf_sup_iff {h : G} (hh : h ∈ H) :
    IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V)) ↔
      IsPGroup 2 ↥(V ⊔ conjSubgroup h V ⊔ wOf V H) := by
  have hVH := hc.V_le_H
  have hUH : conjSubgroup h V ≤ H := conjSubgroup_le_of_le_of_mem hVH hh
  have hXH : V ⊔ conjSubgroup h V ⊔ wOf V H ≤ H := sup_le (sup_le hVH hUH) (wOf_le_H V H)
  have hbar : barOf V H V ⊔ barOf V H (conjSubgroup h V) =
      (((V ⊔ conjSubgroup h V ⊔ wOf V H).subgroupOf H).map (piBar V H)) := by
    unfold barOf
    rw [Subgroup.subgroupOf_sup (sup_le hVH hUH) (wOf_le_H V H),
      Subgroup.subgroupOf_sup hVH hUH, Subgroup.map_sup, Subgroup.map_sup]
    have hW : ((wOf V H).subgroupOf H).map (piBar V H) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (piBar_eq_one_iff x).2 hx
    rw [hW, sup_bot_eq]
  rw [hbar]
  constructor
  · intro hP
    exact LocalAnalysis.WeakClosure81.isPGroup_of_map_mk_isPGroup hXH (wOf_le_H V H)
      (wOf_normal V H) (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian)
      hP
  · intro hP
    have : IsPGroup 2 (((V ⊔ conjSubgroup h V ⊔ wOf V H).subgroupOf H)) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
    exact this.map (piBar V H)

theorem commute_of_isPGroup_barOf_sup {h : G} (hh : h ∈ H)
    (h2 : IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V))) :
    ∀ u ∈ V, ∀ v ∈ conjSubgroup h V, u * v = v * u :=
  hc.commute_of_isPGroup_sup_wOf hh ((hc.isPGroup_barOf_sup_iff hh).1 h2)

theorem mem_normalizer_of_inf_ne_bot {h : G} (hh : h ∈ H)
    (hne : barOf V H V ⊓ conjSubgroup (piBar V H ⟨h, hh⟩) (barOf V H V) ≠ ⊥) :
    h ∈ Subgroup.normalizer (V : Set G) := by
  rw [conjSubgroup_piBar_barOf] at hne
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨haV, haU⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨v, hvV, rfl⟩ := mem_barOf_iff.mp haV
  obtain ⟨u, huU, huv⟩ := mem_barOf_iff.mp haU
  have hvW : (v : G) ∉ wOf V H := fun h' => ha1 (Subtype.ext ((piBar_eq_one_iff v).2 h'))
  have hvuW : ((v : G))⁻¹ * (u : G) ∈ wOf V H := by
    have : piBar V H (v⁻¹ * u) = 1 := by rw [map_mul, map_inv, huv]; simp
    simpa using (piBar_eq_one_iff _).1 this
  have hEH : eOf H ≤ H := (eOf_le_pCore H).trans (inSubgroup_pCore_two H).2.1
  obtain ⟨x, hxW, hx⟩ := tim79a_seven_three_four_ti_inH hc.elemAb hc.ti hc.V_le_H
    (isMulCommutative_eOf H) hEH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hEH).2 (H_le_normalizer_eOf H))
    (fun g hg => hc.eOf_inf_conj_ne_bot hg) hc.notLe (wOf_le_pCore V H) inferInstance
    (fun g hg => inf_pCore_le_wOf (conjSubgroup_mem_omegaOf hg)) hh hvV hvW huU hvuW
  have hxM : x ∈ Subgroup.normalizer (V : Set G) :=
    hc.normalizer_eq ▸ hc.pCoreH_le_M (wOf_le_pCore V H hxW)
  exact mem_normalizer_iff_conjSubgroup_eq.mpr
    (hx.symm ▸ mem_normalizer_iff_conjSubgroup_eq.mp hxM)

theorem barOf_V_ne_bot : barOf V H V ≠ ⊥ := by
  intro hbot
  apply hc.not_V_le_wOf
  intro v hv
  have h1 : piBar V H ⟨v, hc.V_le_H hv⟩ ∈ barOf V H V :=
    mem_barOf_iff.mpr ⟨⟨v, hc.V_le_H hv⟩, hv, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (piBar_eq_one_iff _).1 h1

theorem isTI_barOf_V : IsTI (barOf V H V) := by
  intro y
  obtain ⟨x, rfl⟩ := piBar_surjective V H y
  by_cases hxN : (x : G) ∈ Subgroup.normalizer (V : Set G)
  · right
    rw [conjSubgroup_piBar_barOf, mem_normalizer_iff_conjSubgroup_eq.mp hxN, inf_idem]
  · left
    by_contra hne
    apply hxN
    refine hc.mem_normalizer_of_inf_ne_bot x.2 ?_
    simpa using hne

theorem normalizer_barOf_V :
    Subgroup.normalizer ((barOf V H V : Subgroup (Hbar V H)) : Set (Hbar V H)) =
      barOf V H (Subgroup.normalizer (V : Set G)) := by
  ext y
  obtain ⟨x, rfl⟩ := piBar_surjective V H y
  constructor
  · intro hy
    have hconj : conjSubgroup (piBar V H x) (barOf V H V) = barOf V H V :=
      mem_normalizer_iff_conjSubgroup_eq.mp hy
    have hne : barOf V H V ⊓ conjSubgroup (piBar V H ⟨x, x.2⟩) (barOf V H V) ≠ ⊥ := by
      have : piBar V H ⟨x, x.2⟩ = piBar V H x := rfl
      rw [this, hconj, inf_idem]
      exact hc.barOf_V_ne_bot
    exact mem_barOf_iff.mpr ⟨x, hc.mem_normalizer_of_inf_ne_bot x.2 hne, rfl⟩
  · intro hy
    obtain ⟨n, hnN, hnx⟩ := mem_barOf_iff.mp hy
    rw [← hnx, mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_piBar_barOf,
      mem_normalizer_iff_conjSubgroup_eq.mp hnN]

end MinCex

end CFSG.RankThree.GF2n.Tim79a
