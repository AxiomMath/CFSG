module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
import CFSG.Mathlib.GroupTheory.ClosureSubgroupOf
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveLiftModel

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge Matrix

variable {G : Type} [Group G]

theorem exists_axis_of_fiveLocalModel {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {y : G} (hy : y ∈ commSet D v) :
    ∃ b : Fin (k + 1) → ZMod 5, fiveForm k ε b b ≠ 0 ∧
      (IsSquare (fiveForm k ε b b) ↔ π = true) ∧
      (cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ : GL (Fin (k + 1)) (ZMod 5)) =
        fiveReflOf k ε b :=
  exists_eq_fiveReflOf ((cv.mem_iff ⟨y, Subgroup.subset_closure hy⟩).1 hy)

theorem commute_fiveReflOf_ne_iff {k : ℕ} {ε : Bool} {a b : Fin (k + 1) → ZMod 5}
    (ha0 : fiveForm k ε a a ≠ 0) (hb0 : fiveForm k ε b b ≠ 0) :
    Commute (fiveReflOf k ε b) (fiveReflOf k ε a) ∧
        fiveReflOf k ε b ≠ fiveReflOf k ε a ↔
      fiveForm k ε a b = 0 := by
  constructor
  · rintro ⟨hcomm, hne⟩
    rcases (commute_fiveReflOf_iff k ε hb0 ha0).mp hcomm with hB | ⟨μ, hμ⟩
    · rw [fiveForm_comm k ε b a] at hB
      exact hB
    · exfalso
      have hμ0 : μ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hμ
        exact ha0 (by rw [hμ]; simp [fiveForm])
      refine hne ?_
      rw [hμ, fiveReflOf_smul k ε b hμ0]
  · intro hB
    constructor
    · rw [commute_fiveReflOf_iff k ε hb0 ha0]
      left
      rw [fiveForm_comm k ε a b] at hB
      exact hB
    · intro hEq
      have h1 : (fiveReflOf k ε a : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a =
          -a := fiveReflOf_mulVec_self ha0
      have h2 : (fiveReflOf k ε b : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a =
          a := (fiveReflOf_mulVec_eq_self_iff hb0).mpr hB
      rw [hEq] at h2
      have h3 : -a = a := h1.symm.trans h2
      have hsum : a + a = 0 := (add_eq_zero_iff_eq_neg).mpr h3.symm
      have h2a : (2 : ZMod 5) • a = 0 := by rw [two_smul, hsum]
      rcases smul_eq_zero.mp h2a with h2' | h0
      · exact absurd h2' (by decide)
      · exact ha0 (by rw [h0]; simp [fiveForm])

theorem mem_commSet_iff_of_fiveLocalModel {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u y : G} (hu : u ∈ commSet D v) (hy : y ∈ commSet D v)
    {a : Fin (k + 1) → ZMod 5} (ha0 : fiveForm k ε a a ≠ 0)
    (ha : (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a) :
    y ∈ commSet D u ↔
      ((cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a := by
  obtain ⟨b, hb0, _hbπ, hby⟩ := exists_axis_of_fiveLocalModel cv hy
  have hL : y ∈ commSet D u ↔ Commute y u ∧ y ≠ u := by
    simp only [commSet, Set.mem_setOf_eq, hy.1, true_and]
  rw [hL]
  have hcomm : Commute y u ↔ Commute (fiveReflOf k ε b) (fiveReflOf k ε a) := by
    have h1 : Commute y u ↔ Commute (⟨y, Subgroup.subset_closure hy⟩ :
        Subgroup.closure (commSet D v)) ⟨u, Subgroup.subset_closure hu⟩ :=
      (Submonoid.commute_coe_coe (s := Subgroup.closure (commSet D v))
        (x := ⟨y, Subgroup.subset_closure hy⟩) (y := ⟨u, Subgroup.subset_closure hu⟩))
    have h2 : Commute (⟨y, Subgroup.subset_closure hy⟩ :
        Subgroup.closure (commSet D v)) ⟨u, Subgroup.subset_closure hu⟩ ↔
        Commute (cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
          fiveReflectionGroup k ε π) (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩) :=
      (commute_map_iff cv.toMulEquiv.injective).symm
    have h3 : Commute (cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
        fiveReflectionGroup k ε π) (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩) ↔
        Commute ((cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
          fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5))
          ((cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ :
            fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) :=
      (Submonoid.commute_coe_coe (s := fiveReflectionGroup k ε π)
        (x := cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩)
        (y := cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩)).symm
    have h4 : Commute ((cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
        fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5))
        ((cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ :
          fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) ↔
        Commute (fiveReflOf k ε b) (fiveReflOf k ε a) := by
      rw [hby, ha]
    exact h1.trans (h2.trans (h3.trans h4))
  have hne : y ≠ u ↔ fiveReflOf k ε b ≠ fiveReflOf k ε a := by
    have h1 : y ≠ u ↔ (⟨y, Subgroup.subset_closure hy⟩ :
        Subgroup.closure (commSet D v)) ≠ ⟨u, Subgroup.subset_closure hu⟩ :=
      (Subtype.coe_ne_coe (a := (⟨y, Subgroup.subset_closure hy⟩ :
        Subgroup.closure (commSet D v))) (b := ⟨u, Subgroup.subset_closure hu⟩))
    have h2 : (⟨y, Subgroup.subset_closure hy⟩ : Subgroup.closure (commSet D v)) ≠
        ⟨u, Subgroup.subset_closure hu⟩ ↔
        cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ ≠
          cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ := by
      constructor
      · intro hh hEq; exact hh (cv.toMulEquiv.injective hEq)
      · intro hh hEq; exact hh (congrArg cv.toMulEquiv hEq)
    have h3 : cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ ≠
        cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ ↔
        ((cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
          fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) ≠
          ((cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ :
            fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) :=
      (Subtype.coe_ne_coe (a := (cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
        fiveReflectionGroup k ε π))
        (b := cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩)).symm
    have h4 : ((cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ :
        fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) ≠
        ((cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ :
          fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) ↔
        fiveReflOf k ε b ≠ fiveReflOf k ε a := by
      rw [hby, ha]
    exact h1.trans (h2.trans (h3.trans h4))
  rw [hcomm, hne, commute_fiveReflOf_ne_iff ha0 hb0, hby]
  exact (fiveReflOf_mulVec_eq_self_iff hb0).symm

theorem image_commSet_inter_subset_fiveReflectionsIn {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u : G} (hu : u ∈ commSet D v)
    {a : Fin (k + 1) → ZMod 5} (ha0 : fiveForm k ε a a ≠ 0)
    (ha : (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a) :
    ∀ h : Subgroup.closure (commSet D v),
      (h : G) ∈ commSet D u ∩ commSet D v →
        (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) ∈
          fiveReflectionsIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
  intro h hh
  have hhv : (h : G) ∈ commSet D v := hh.2
  have hhu : (h : G) ∈ commSet D u := hh.1
  obtain ⟨b, hb0, hbπ, hby⟩ := exists_axis_of_fiveLocalModel cv hhv
  have hby' : (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε b := by
    simpa using hby
  have hfix : ((cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a := by
    have := (mem_commSet_iff_of_fiveLocalModel cv hu hhv ha0 ha).mp hhu
    simpa using this
  have hb_fix : (fiveReflOf k ε b : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a =
      a := by
    rw [← hby']
    exact hfix
  have hB : fiveForm k ε a b = 0 := (fiveReflOf_mulVec_eq_self_iff hb0).mp hb_fix
  rw [hby']
  refine ⟨b, ?_, hb0, hbπ, fun x => fiveReflOf_mulVec k ε b x⟩
  rw [mem_fiveOrth]
  intro u' hu'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu'
  rw [fiveForm_comm k ε b (c • a), fiveForm_smul_left, hB, mul_zero]

theorem fiveReflectionsIn_subset_image_commSet_inter {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u : G} (hu : u ∈ commSet D v)
    {a : Fin (k + 1) → ZMod 5} (ha0 : fiveForm k ε a a ≠ 0)
    (ha : (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a) :
    ∀ r ∈ fiveReflectionsIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})),
      ∃ h : Subgroup.closure (commSet D v),
        (h : G) ∈ commSet D u ∩ commSet D v ∧
          (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) = r := by
  intro r hr
  obtain ⟨b, hbW, hb0, hbπ, hbform⟩ := hr
  have hrb : r = fiveReflOf k ε b := by
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [hbform (Pi.single i 1), fiveReflOf_mulVec]
  have hmem : fiveReflOf k ε b ∈ fiveReflections k ε π := fiveReflOf_mem hb0 hbπ
  obtain ⟨h, hh⟩ := cv.toMulEquiv.surjective ⟨fiveReflOf k ε b, Subgroup.subset_closure hmem⟩
  have hbW' : fiveForm k ε b a = 0 := by
    rw [mem_fiveOrth] at hbW
    exact hbW a (Submodule.subset_span (Set.mem_singleton a))
  have hB : fiveForm k ε a b = 0 := by rwa [fiveForm_comm k ε a b]
  have hhv : (h : G) ∈ commSet D v := by
    rw [cv.mem_iff h, hh]
    exact hmem
  have hhu : (h : G) ∈ commSet D u := by
    refine (mem_commSet_iff_of_fiveLocalModel cv hu hhv ha0 ha).mpr ?_
    have : ((cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a := by
      rw [hh]
      exact (fiveReflOf_mulVec_eq_self_iff hb0).mpr hB
    simpa using this
  refine ⟨h, ⟨hhu, hhv⟩, ?_⟩
  have : (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε b := by rw [hh]
  exact this.trans hrb.symm

theorem mem_closure_commSet_inter_iff_of_fiveLocalModel {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u : G} (hu : u ∈ commSet D v)
    {a : Fin (k + 1) → ZMod 5} (ha0 : fiveForm k ε a a ≠ 0)
    (ha : (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a)
    (h : Subgroup.closure (commSet D v)) :
    (h : G) ∈ Subgroup.closure (commSet D u ∩ commSet D v) ↔
      (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) ∈
        fiveReflectionGroupIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
  let Hv : Subgroup G := Subgroup.closure (commSet D v)
  let S : Set G := commSet D u ∩ commSet D v
  let S_H : Set Hv := {x | (x : G) ∈ S}
  let φ : Hv →* GL (Fin (k + 1)) (ZMod 5) :=
    (fiveReflectionGroup k ε π).subtype.comp cv.toMulEquiv.toMonoidHom
  have hS : S ⊆ Hv := fun _ hx => Subgroup.subset_closure hx.2
  have hφ : Function.Injective φ := by
    intro x y hxy
    exact cv.toMulEquiv.injective (Subtype.ext hxy)
  have himg : φ '' S_H = fiveReflectionsIn k ε π
      (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact image_commSet_inter_subset_fiveReflectionsIn cv hu ha0 ha x hx
    · intro hr
      obtain ⟨x, hx, hxr⟩ := fiveReflectionsIn_subset_image_commSet_inter cv hu ha0 ha r hr
      exact ⟨x, hx, hxr⟩
  have hL : (h : G) ∈ Subgroup.closure S ↔ h ∈ Subgroup.closure S_H := by
    rw [show Subgroup.closure S_H = (Subgroup.closure S).subgroupOf Hv from
      (Subgroup.closure_subgroupOf hS).symm, Subgroup.mem_subgroupOf]
  have hR : h ∈ Subgroup.closure S_H ↔
      (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) ∈
        fiveReflectionGroupIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    change h ∈ Subgroup.closure S_H ↔
      (cv.toMulEquiv h : GL (Fin (k + 1)) (ZMod 5)) ∈
        Subgroup.closure (fiveReflectionsIn k ε π
          (fiveOrth k ε (Submodule.span (ZMod 5) {a})))
    rw [← himg, ← MonoidHom.map_closure φ S_H]
    constructor
    · intro hh
      exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    · intro hh
      obtain ⟨x, hx, hxh⟩ := Subgroup.mem_map.mp hh
      rwa [hφ hxh] at hx
  exact hL.trans hR

theorem orderOf_mul_of_fiveLocalModel {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u y : G} (hu : u ∈ commSet D v) (hy : y ∈ commSet D v) :
    orderOf (u * y) =
      orderOf ((cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) *
        (cv.toMulEquiv ⟨y, Subgroup.subset_closure hy⟩ : GL (Fin (k + 1)) (ZMod 5))) := by
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, ← map_mul, MulEquiv.orderOf_eq,
    ← Subgroup.orderOf_coe, Subgroup.coe_mul]

end CFSG.OddTranspositions.PartThree

end
