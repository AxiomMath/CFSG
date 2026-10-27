module

public import CFSG.Monster.B.TwoA.Fischer.Slice
public import CFSG.Monster.B.TwoA.Unitary.CliquePlane

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix CFSG.Monster.B.TwoA.Unitary.Clique

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem act_inv_act (a : S) (v : V) : act a⁻¹ (act a v) = v := by
  rw [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

theorem act_act_inv (a : S) (v : V) : act a (act a⁻¹ v) = v := by
  rw [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem image_act_inv_image (a : S) (D : Set V) : act a⁻¹ '' (act a '' D) = D := by
  rw [map_inv, Equiv.Perm.inv_def, Equiv.symm_image_image]

theorem mem_image_act_iff (a : S) (D : Set V) (v : V) : v ∈ act a '' D ↔ act a⁻¹ v ∈ D := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [act_inv_act]
  · intro h
    exact ⟨_, h, act_act_inv a v⟩

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem act_mem_iff {a : S} (ha : a ∈ sliceGroup lab Y) (y : V) : act a y ∈ Y ↔ y ∈ Y := by
  refine ⟨fun h => ?_, hS.mapsTo a ha y⟩
  have h' := hS.mapsTo _ ((sliceGroup lab Y).inv_mem ha) _ h
  rwa [act_inv_act] at h'

theorem commute_act_iff (a : S) (y z : V) :
    Commute (lab (act a y)) (lab (act a z)) ↔ Commute (lab y) (lab z) := by
  rw [hS.lab_act, hS.lab_act]
  exact Commute.conj_iff a

theorem adj_act_iff {a : S} (ha : a ∈ sliceGroup lab Y) (y z : V) :
    (sliceGraph lab Y).Adj (act a y) (act a z) ↔ (sliceGraph lab Y).Adj y z := by
  rw [sliceGraph_adj, sliceGraph_adj, hS.act_mem_iff ha, hS.act_mem_iff ha,
    (act a).injective.ne_iff, hS.commute_act_iff]

theorem isClique_image {a : S} (ha : a ∈ sliceGroup lab Y) {D : Set V}
    (hD : D ⊆ Y ∧ (sliceGraph lab Y).IsClique D) :
    act a '' D ⊆ Y ∧ (sliceGraph lab Y).IsClique (act a '' D) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hS.mapsTo a ha y (hD.1 hy)
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hne
    exact (hS.adj_act_iff ha y z).2 (hD.2 hy hz fun h => hne (h ▸ rfl))

theorem isSliceMaxClique_image {a : S} (ha : a ∈ sliceGroup lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) : IsSliceMaxClique lab Y (act a '' C) := by
  refine ⟨hS.isClique_image ha hC.1, fun D hD hle => ?_⟩
  have h1 := hS.isClique_image ((sliceGroup lab Y).inv_mem ha) hD
  have h2 : C ⊆ act a⁻¹ '' D := by
    rw [← image_act_inv_image a C]
    exact Set.image_mono hle
  have h3 := hC.2 h1 h2
  intro v hv
  rw [mem_image_act_iff]
  exact h3 ⟨v, hv, rfl⟩

theorem finite_sliceGroup : Finite (sliceGroup lab Y) := by
  have : Finite Y := hS.finite.to_subtype
  refine Finite.of_injective (slicePerm act lab Y hS.mapsTo) ?_
  rw [injective_iff_map_eq_one]
  intro a ha
  refine Subtype.ext (hS.faithful a a.2 fun y hy => ?_)
  have := congrArg (fun σ : Equiv.Perm Y => ((σ ⟨y, hy⟩ : Y) : V)) ha
  exact this

theorem act_mem_neighborSet {u : V} {a : S} (ha : a ∈ sliceStab act lab Y u) {z : V}
    (hz : z ∈ (sliceGraph lab Y).neighborSet u) :
    act a z ∈ (sliceGraph lab Y).neighborSet u := by
  have h := (hS.adj_act_iff ha.1 u z).2 hz
  rwa [show act a u = u from ha.2] at h

theorem act_mem_neighborSet_iff {u : V} {a : S} (ha : a ∈ sliceStab act lab Y u) (z : V) :
    act a z ∈ (sliceGraph lab Y).neighborSet u ↔ z ∈ (sliceGraph lab Y).neighborSet u := by
  refine ⟨fun h => ?_, hS.act_mem_neighborSet ha⟩
  have h' := hS.act_mem_neighborSet ((sliceStab act lab Y u).inv_mem ha) h
  rwa [act_inv_act] at h'

theorem lab_mem_sliceStab_of_mem {u z : V} (hz : z ∈ (sliceGraph lab Y).neighborSet u) :
    lab z ∈ sliceStab act lab Y u :=
  hS.lab_mem_sliceStab hz.1 hz.2.1 hz.2.2.2.symm

end IsFischerSlice

theorem mem_neighborSet_of_mem_clique {C : Set V} (hC : (sliceGraph lab Y).IsClique C) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) (hne : v ≠ u) : v ∈ (sliceGraph lab Y).neighborSet u :=
  hC hu hv hne.symm

theorem eq_insert_of_isClique {C : Set V} (hC : (sliceGraph lab Y).IsClique C) {u : V}
    (hu : u ∈ C) : C = insert u (Subtype.val '' {z : (sliceGraph lab Y).neighborSet u |
      (z : V) ∈ C}) := by
  ext v
  constructor
  · intro hv
    by_cases hvu : v = u
    · rw [hvu]
      exact Set.mem_insert u _
    · exact Set.mem_insert_of_mem u
        ⟨⟨v, mem_neighborSet_of_mem_clique hC hu hv hvu⟩, hv, rfl⟩
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact hu
    · exact hz

theorem sq_eq_one_of_mem_zpowers {G : Type*} [Group G] {g x : G} (hg : g ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers g) : x ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u)

theorem φ_lab (hS : IsFischerSlice act lab Y) (z : (sliceGraph lab Y).neighborSet u) :
    L.φ ⟨lab z, hS.lab_mem_sliceStab_of_mem z.2⟩ = tPt (L.τ z) :=
  L.lab_eq z _ rfl

theorem tau_act (hS : IsFischerSlice act lab Y) (a : sliceStab act lab Y u)
    (z : (sliceGraph lab Y).neighborSet u) :
    L.τ ⟨act a z, hS.act_mem_neighborSet a.2 z.2⟩ = projAct (L.φ a) (L.τ z) :=
  L.equivariant a z _ rfl

theorem adj_iff (hS : IsFischerSlice act lab Y) (z z' : (sliceGraph lab Y).neighborSet u) :
    (sliceGraph lab Y).Adj z z' ↔ isoGraph.Adj (L.τ z) (L.τ z') := by
  rw [adj_iff_commute]
  set a : sliceStab act lab Y u := ⟨lab z, hS.lab_mem_sliceStab_of_mem z.2⟩ with ha
  set a' : sliceStab act lab Y u := ⟨lab z', hS.lab_mem_sliceStab_of_mem z'.2⟩ with ha'
  have hφ : L.φ a = tPt (L.τ z) := L.φ_lab hS z
  have hφ' : L.φ a' = tPt (L.τ z') := L.φ_lab hS z'
  constructor
  · intro h
    refine ⟨fun e => h.2.2.1 (congrArg Subtype.val (L.τ.injective e)), ?_⟩
    have hc : Commute a a' := Subtype.ext h.2.2.2.eq
    rw [← hφ, ← hφ']
    exact hc.map L.φ
  · rintro ⟨hne, hc⟩
    refine ⟨z.2.2.1, z'.2.2.1, fun e => hne (congrArg L.τ (Subtype.ext e)), ?_⟩
    by_contra hnc
    have h3 := hS.orderOf_mul z z.2.2.1 z' z'.2.2.1 hnc
    have h1 : L.φ ((a * a') ^ 2) = 1 := by
      rw [map_pow, map_mul, hφ, hφ', hc.mul_pow, tPt_sq, tPt_sq, one_mul]
    have h2 := (L.ker _).1 h1
    have hu2 : lab u ^ 2 = 1 := by
      rw [← hS.orderOf_lab u z.2.1]
      exact pow_orderOf_eq_one _
    have h4 : (lab z * lab z') ^ 4 = 1 := by
      have := sq_eq_one_of_mem_zpowers hu2 h2
      simp only [Subgroup.coe_pow, Subgroup.coe_mul] at this
      rw [← pow_mul] at this
      exact this
    have h5 : (lab z * lab z') ^ 3 = 1 := by
      rw [← h3]
      exact pow_orderOf_eq_one _
    have h6 : lab z * lab z' = 1 := by
      calc lab z * lab z' = (lab z * lab z') ^ 4 * ((lab z * lab z') ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, h5, inv_one, mul_one]
    rw [h6, orderOf_one] at h3
    exact absurd h3 (by decide)

@[expose] def img (D : Set V) : Set IsoPt := L.τ '' {z | (z : V) ∈ D}

theorem mem_img_iff (D : Set V) (z : (sliceGraph lab Y).neighborSet u) :
    L.τ z ∈ L.img D ↔ (z : V) ∈ D := by
  constructor
  · rintro ⟨w, hw, e⟩
    rwa [← L.τ.injective e]
  · intro h
    exact ⟨z, h, rfl⟩

theorem finite_neighborSet (L' : LocalChart act lab Y u) :
    Finite ((sliceGraph lab Y).neighborSet u) :=
  Finite.of_equiv _ L'.τ.symm

theorem maximal_img (hS : IsFischerSlice act lab Y) {C : Set V} (hC : IsSliceMaxClique lab Y C)
    (hu : u ∈ C) : Maximal isoGraph.IsClique (L.img C) := by
  refine ⟨?_, fun T hT hle => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ hne
    refine (L.adj_iff hS z z').1 (hC.1.2 hz hz' fun e => hne ?_)
    rw [Subtype.ext e]
  · have huY : u ∈ Y := hC.1.1 hu
    set D : Set V := insert u (Subtype.val '' (L.τ ⁻¹' T)) with hD
    have hDcl : D ⊆ Y ∧ (sliceGraph lab Y).IsClique D := by
      refine ⟨?_, ?_⟩
      · rintro v (rfl | ⟨z, -, rfl⟩)
        · exact huY
        · exact z.2.2.1
      · rintro v hv w hw hvw
        rcases hv with rfl | ⟨z, hz, rfl⟩ <;> rcases hw with rfl | ⟨z', hz', rfl⟩
        · exact absurd rfl hvw
        · exact z'.2
        · exact (sliceGraph lab Y).adj_symm z.2
        · refine (L.adj_iff hS z z').2 (hT hz hz' fun e => hvw ?_)
          rw [L.τ.injective e]
    have hCD : C ⊆ D := by
      intro v hv
      by_cases hvu : v = u
      · rw [hvu]
        exact Set.mem_insert u _
      · have hvn := mem_neighborSet_of_mem_clique hC.1.2 hu hv hvu
        refine Set.mem_insert_of_mem u ⟨⟨v, hvn⟩, hle ?_, rfl⟩
        exact (L.mem_img_iff C ⟨v, hvn⟩).2 hv
    have hDC := hC.2 hDcl hCD
    intro p hp
    have hz : ((L.τ.symm p : (sliceGraph lab Y).neighborSet u) : V) ∈ C :=
      hDC (Set.mem_insert_of_mem u ⟨_, by simpa using hp, rfl⟩)
    have := (L.mem_img_iff C _).2 hz
    rwa [Equiv.apply_symm_apply] at this

theorem exists_img_eq (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C) :
    ∃ W : Submodule CFSG.Fischer.F4 CFSG.Monster.B.Classical.UnitarySix.V,
      IsMaxIso W ∧ L.img C = planePts W :=
  (maximal_isClique_iff _).1 (L.maximal_img hS hC hu)

theorem ncard_img (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C) : (L.img C).ncard = 21 := by
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  rw [hWe, hW.ncard_planePts]

end LocalChart

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem nonempty_of_isSliceMaxClique {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    C.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hY : Y.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hS.ncard]; decide)
  obtain ⟨y, hy⟩ := hY
  have h1 : ({y} : Set V) ⊆ Y ∧ (sliceGraph lab Y).IsClique {y} :=
    ⟨Set.singleton_subset_iff.2 hy, Set.pairwise_singleton _ _⟩
  have h2 := hC.2 h1 (by rw [h]; exact Set.empty_subset _)
  rw [h] at h2
  exact h2 rfl

theorem ncard_eq_of_isSliceMaxClique {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    C.ncard = 22 := by
  obtain ⟨u, hu⟩ := hS.nonempty_of_isSliceMaxClique hC
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  have : Finite ((sliceGraph lab Y).neighborSet u) := L.finite_neighborSet
  rw [eq_insert_of_isClique hC.1.2 hu, Set.ncard_insert_of_notMem, Set.ncard_image_of_injective _
    Subtype.val_injective]
  · have h := L.ncard_img hS hC hu
    rw [LocalChart.img, Set.ncard_image_of_injective _ L.τ.injective] at h
    rw [h]
  · rintro ⟨z, -, hz⟩
    exact z.2.2.2.1 hz.symm

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
