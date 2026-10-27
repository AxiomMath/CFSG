module

public import CFSG.Monster.B.TwoA.Fischer.CliqueCode

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

variable (lab Y) in
@[expose] def hexadFiber (C B : Set V) : Set V :=
  {x | x ∈ Y ∧ x ∉ C ∧ C ∩ (sliceGraph lab Y).neighborSet x = B}

theorem mem_hexadFiber {C B : Set V} {x : V} :
    x ∈ hexadFiber lab Y C B ↔ x ∈ Y ∧ x ∉ C ∧ C ∩ (sliceGraph lab Y).neighborSet x = B :=
  Iff.rfl

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem act_mem_hexadFiber {C B : Set V} {r : S} (hr : r ∈ ptStab act lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C B) : act r x ∈ hexadFiber lab Y C B := by
  obtain ⟨hxY, hxC, hxB⟩ := hx
  refine ⟨hS.mapsTo r hr.1 x hxY, fun h => hxC (((ptStab_le_setStab C hr).2 x).1 h), ?_⟩
  rw [← hxB]
  ext z
  simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
  refine and_congr_right fun hzC => ?_
  have h := hS.adj_act_iff hr.1 x z
  rwa [hr.2 z hzC] at h

theorem inter_neighborSet_act {C : Set V} {a : S} (ha : a ∈ setStab act lab Y C) (x : V) :
    C ∩ (sliceGraph lab Y).neighborSet (act a x) =
      act a '' (C ∩ (sliceGraph lab Y).neighborSet x) := by
  ext z
  rw [mem_image_act_iff]
  simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
  have h1 : z ∈ C ↔ act a⁻¹ z ∈ C := (((setStab act lab Y C).inv_mem ha).2 z).symm
  have h2 : (sliceGraph lab Y).Adj (act a x) z ↔ (sliceGraph lab Y).Adj x (act a⁻¹ z) := by
    rw [← hS.adj_act_iff ha.1 x (act a⁻¹ z), act_act_inv]
  rw [h1, h2]

theorem image_hexadFiber {C : Set V} {a : S} (ha : a ∈ setStab act lab Y C) (B : Set V) :
    act a '' hexadFiber lab Y C B = hexadFiber lab Y C (act a '' B) := by
  ext y
  rw [mem_image_act_iff, mem_hexadFiber, mem_hexadFiber,
    hS.act_mem_iff ((sliceGroup lab Y).inv_mem ha.1), ((setStab act lab Y C).inv_mem ha).2 y]
  have hy := hS.inter_neighborSet_act ha (act a⁻¹ y)
  rw [act_act_inv] at hy
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [hy]
  exact (Set.image_injective.2 (act a).injective).eq_iff.symm

end IsFischerSlice

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u) {C : Set V}

theorem inter_neighborSet_eq (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C)
    (hu : u ∈ C) {W : Submodule F4 UnitarySix.V} (hWe : L.img C = planePts W)
    (x : (sliceGraph lab Y).neighborSet u) (hx : (x : V) ∉ C) :
    C ∩ (sliceGraph lab Y).neighborSet x =
      insert u (Subtype.val '' (L.τ ⁻¹' planePts (perpSub (L.τ x) ⊓ W))) := by
  have hxW : L.τ x ∉ planePts W := by
    rw [← hWe, L.mem_img_iff]
    exact hx
  have hfib : L.τ x ∈ fiberY W (perpSub (L.τ x) ⊓ W) := ⟨hxW, rfl⟩
  ext v
  by_cases hvu : v = u
  · subst hvu
    exact iff_of_true ⟨hu, (sliceGraph lab Y).adj_symm x.2⟩ (Set.mem_insert _ _)
  · rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
    constructor
    · rintro ⟨hvC, hxv⟩
      have hvn := mem_neighborSet_of_mem_clique hC.1.2 hu hvC hvu
      rw [L.mem_insert_iff_tau _ hvn]
      have hvW : L.τ ⟨v, hvn⟩ ∈ planePts W := by
        rw [← hWe]
        exact (L.mem_img_iff C _).2 hvC
      exact (adj_iff_of_mem_fiberY hfib hvW).1 ((L.adj_iff hS x ⟨v, hvn⟩).1 hxv)
    · rintro (h | ⟨w, hw, rfl⟩)
      · exact absurd h hvu
      · have hwW : L.τ w ∈ planePts W := planePts_mono inf_le_right hw
        refine ⟨(L.mem_img_iff C w).1 (by rw [hWe]; exact hwW), ?_⟩
        exact (L.adj_iff hS x w).2 ((adj_iff_of_mem_fiberY hfib hwW).2 hw)

theorem eq_of_insert_eq {W A A' : Submodule F4 UnitarySix.V} (hW : IsTotIso W) (hAW : A ≤ W)
    (hA'W : A' ≤ W)
    (h : insert u (Subtype.val '' (L.τ ⁻¹' planePts A)) =
      insert u (Subtype.val '' (L.τ ⁻¹' planePts A'))) : A = A' := by
  refine eq_of_planePts_eq (hW.mono hAW) (hW.mono hA'W) (Set.ext fun p => ?_)
  obtain ⟨w, rfl⟩ := L.τ.surjective p
  exact (L.mem_insert_iff_tau _ w.2).symm.trans (h ▸ L.mem_insert_iff_tau _ w.2)

theorem hexadFiber_eq (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C)
    (hu : u ∈ C) {W : Submodule F4 UnitarySix.V} (hW : IsMaxIso W) (hWe : L.img C = planePts W)
    {A : Submodule F4 UnitarySix.V} (hAW : A ≤ W) :
    hexadFiber lab Y C (insert u (Subtype.val '' (L.τ ⁻¹' planePts A))) =
      Subtype.val '' (L.τ ⁻¹' fiberY W A) := by
  ext x
  constructor
  · rintro ⟨-, hxC, hxB⟩
    have huB : u ∈ C ∩ (sliceGraph lab Y).neighborSet x := by
      rw [hxB]
      exact Set.mem_insert u _
    have hxn : x ∈ (sliceGraph lab Y).neighborSet u := (sliceGraph lab Y).adj_symm huB.2
    refine ⟨⟨x, hxn⟩, ⟨fun h => hxC ((L.mem_img_iff C ⟨x, hxn⟩).1 (by rw [hWe]; exact h)), ?_⟩,
      rfl⟩
    have e := L.inter_neighborSet_eq hS hC hu hWe ⟨x, hxn⟩ hxC
    rw [hxB] at e
    exact (L.eq_of_insert_eq hW.2 hAW inf_le_right e).symm
  · rintro ⟨z, hz, rfl⟩
    have hzC : (z : V) ∉ C := fun h => hz.1 (by rw [← hWe]; exact (L.mem_img_iff C z).2 h)
    refine ⟨z.2.2.1, hzC, ?_⟩
    rw [L.inter_neighborSet_eq hS hC hu hWe z hzC, hz.2]

theorem ncard_hexadFiber (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C)
    (hu : u ∈ C) {W : Submodule F4 UnitarySix.V} (hW : IsMaxIso W) (hWe : L.img C = planePts W)
    {A : Submodule F4 UnitarySix.V} (hAW : A ≤ W) (hA : Module.finrank F4 A = 2) :
    (hexadFiber lab Y C (insert u (Subtype.val '' (L.τ ⁻¹' planePts A)))).ncard = 32 := by
  rw [L.hexadFiber_eq hS hC hu hW hWe hAW, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_preimage_of_injective_subset_range L.τ.injective (by
      rw [Equiv.range_eq_univ]
      exact Set.subset_univ _), ncard_fiberY hW hAW hA]

theorem exists_ptStab_act_eq (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C)
    (hu : u ∈ C) {W : Submodule F4 UnitarySix.V} (hW : IsMaxIso W) (hWe : L.img C = planePts W)
    {A : Submodule F4 UnitarySix.V} (hAW : A ≤ W) (hA : Module.finrank F4 A = 2)
    {z z' : (sliceGraph lab Y).neighborSet u} (hz : L.τ z ∈ fiberY W A)
    (hz' : L.τ z' ∈ fiberY W A) : ∃ r ∈ ptStab act lab Y C, act r z = z' := by
  obtain ⟨k, hk, hkz⟩ := exists_kerL_of_mem_fiberY hW hAW hA hz hz'
  obtain ⟨b, rfl⟩ := L.surj k
  refine ⟨b, (L.mem_ptStab_iff hS hC hu hWe b).2 hk, ?_⟩
  rw [← L.tau_act hS b z] at hkz
  exact congrArg (fun w : (sliceGraph lab Y).neighborSet u => (w : V)) (L.τ.injective hkz)

theorem ptStab_inf_actStab (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C)
    (hu : u ∈ C) {W : Submodule F4 UnitarySix.V} (hW : IsMaxIso W) (hWe : L.img C = planePts W)
    {A : Submodule F4 UnitarySix.V} (hAW : A ≤ W) (hA : Module.finrank F4 A = 2)
    (z : (sliceGraph lab Y).neighborSet u) (hz : L.τ z ∈ fiberY W A) :
    ptStab act lab Y C ⊓ actStab act (z : V) =
        Subgroup.closure (lab '' insert u (Subtype.val '' (L.τ ⁻¹' planePts A))) ∧
      Nat.card ↥(ptStab act lab Y C ⊓ actStab act (z : V)) = 32 := by
  set B := insert u (Subtype.val '' (L.τ ⁻¹' planePts A)) with hBdef
  have hzC : (z : V) ∉ C := fun h => hz.1 (by rw [← hWe]; exact (L.mem_img_iff C z).2 h)
  have hzB : C ∩ (sliceGraph lab Y).neighborSet z = B := by
    rw [L.inter_neighborSet_eq hS hC hu hWe z hzC, hz.2]
  have hRu : ptStab act lab Y C ⊓ actStab act (z : V) ≤ sliceStab act lab Y u :=
    fun r hr => ⟨hr.1.1, hr.1.2 u hu⟩
  have e : (ptStab act lab Y C ⊓ actStab act (z : V)).subgroupOf (sliceStab act lab Y u) =
      (kerL W ⊓ fixL (L.τ z)).comap L.φ := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf,
      L.mem_ptStab_iff hS hC hu hWe b, mem_actStab, mem_fixL]
    refine and_congr_right fun _ => ?_
    rw [← L.tau_act hS b z]
    constructor
    · intro h
      exact congrArg L.τ (Subtype.ext h)
    · intro h
      exact congrArg (fun w : (sliceGraph lab Y).neighborSet u => (w : V)) (L.τ.injective h)
  refine ⟨le_antisymm (fun r hr => ?_) ?_, ?_⟩
  · have hb : r ∈ sliceStab act lab Y u := hRu hr
    set K := Subgroup.closure (lab '' B) with hK
    have hgen : kerL W ⊓ fixL (L.τ z) ≤ (K.subgroupOf (sliceStab act lab Y u)).map L.φ := by
      rw [kerL_inf_fixL hW hAW hA hz, Subgroup.closure_le]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨w, rfl⟩ := L.τ.surjective p
      exact ⟨⟨lab w, hS.lab_mem_sliceStab_of_mem w.2⟩, (Subgroup.mem_subgroupOf).2
        (Subgroup.subset_closure ⟨w, (L.mem_insert_iff_tau _ w.2).2 hp, rfl⟩), L.φ_lab hS w⟩
    have hφ : L.φ ⟨r, hb⟩ ∈ kerL W ⊓ fixL (L.τ z) := by
      have h : (⟨r, hb⟩ : sliceStab act lab Y u) ∈
          (ptStab act lab Y C ⊓ actStab act (z : V)).subgroupOf (sliceStab act lab Y u) := hr
      rw [e] at h
      exact h
    obtain ⟨r', hr', he⟩ := hgen hφ
    have hk : L.φ (r'⁻¹ * ⟨r, hb⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have hlu : Subgroup.zpowers (lab u) ≤ K :=
      (Subgroup.zpowers_le).2 (Subgroup.subset_closure ⟨u, Set.mem_insert u _, rfl⟩)
    have h1 : ((r'⁻¹ * ⟨r, hb⟩ : sliceStab act lab Y u) : S) ∈ K := hlu ((L.ker _).1 hk)
    have h3 : r = (r' : S) * ((r'⁻¹ * ⟨r, hb⟩ : sliceStab act lab Y u) : S) := by simp
    rw [h3]
    exact K.mul_mem hr' h1
  · rw [Subgroup.closure_le]
    rintro _ ⟨y, hyB, rfl⟩
    rw [← hzB] at hyB
    have hyY : y ∈ Y := hC.1.1 hyB.1
    refine ⟨hS.closure_le_ptStab hC.1.1 hC.1.2 (Subgroup.subset_closure ⟨y, hyB.1, rfl⟩), ?_⟩
    exact (hS.act_lab_eq_iff hyY z.2.2.1).2 hyB.2.2.2.2.symm
  · have := hS.finite_sliceStab u
    have h := natCard_comap_of_surjective L.surj (kerL W ⊓ fixL (L.τ z))
    rw [← e, natCard_subgroupOf, inf_eq_left.2 hRu, natCard_kerL_inf_fixL hW hAW hA hz,
      hS.natCard_ker_φ (hC.1.1 hu) L] at h
    exact h

end LocalChart

end CFSG.Monster.B.TwoA.Fischer
