module

public import CFSG.Monster.B.TwoA.Sp8.SubgeomDataBase

public import CFSG.Monster.B.TwoA.Sp8.Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

attribute [local instance] parAction

@[expose] def subgeomPairs :
    Set (ℕ × Subgroup Dfull) :=
  {p | 1 ≤ p.1 ∧ p.1 ≤ 4 ∧ ∃ h ∈ Xgrp, p.2 = conjSub h (Echain p.1)}

@[expose] def subgeom :
    Set ParGeom := {x | x.1 ∈ subgeomPairs}

theorem subgeom_finite :
    subgeom.Finite := Set.toFinite _

theorem mem_subgeom {x : ParGeom} :
    x ∈ subgeom ↔ parType x ≤ 4 ∧ ∃ h ∈ Xgrp, x.1.2 = conjSub h (Echain (parType x)) :=
  ⟨fun ⟨_, h4, hx⟩ => ⟨h4, hx⟩, fun ⟨h4, hx⟩ => ⟨x.2.1, h4, hx⟩⟩

@[expose] def subgeomConj
    (s : Shat) : Set ParGeom := (s • ·) '' subgeom

theorem mem_subgeomConj_iff_inv
    {s : Shat} {x : ParGeom} :
    x ∈ subgeomConj s ↔ s⁻¹ • x ∈ subgeom := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [inv_smul_smul]
  · intro hx
    exact ⟨s⁻¹ • x, hx, smul_inv_smul s x⟩

theorem mem_subgeomConj
    {s : Shat} {x : ParGeom} :
    x ∈ subgeomConj s ↔
      parType x ≤ 4 ∧ ∃ h ∈ Xgrp, x.1.2 = conjSub ((s : Dfull) * h) (Echain (parType x)) := by
  rw [mem_subgeomConj_iff_inv, mem_subgeom, parType_smul]
  refine and_congr_right fun _ => exists_congr fun h => and_congr_right fun _ => ?_
  rw [smul_obj_snd, Subgroup.coe_inv, conjSub_mul]
  constructor
  · intro e
    rw [← e, conjSub_conjSub_inv]
  · intro e
    rw [e, conjSub_inv_conjSub]

theorem smul_mem_subgeom
    {s : Shat} (hs : (s : Dfull) ∈ Xgrp) {x : ParGeom}
    (hx : x ∈ subgeom) : s • x ∈ subgeom := by
  obtain ⟨h4, h, hh, hxh⟩ := mem_subgeom.1 hx
  refine mem_subgeom.2 ⟨h4, (s : Dfull) * h, Xgrp.mul_mem hs hh, ?_⟩
  rw [smul_obj_snd, parType_smul, hxh, conjSub_mul]

theorem subgeomConj_of_mem
    {s : Shat} (hs : (s : Dfull) ∈ Xgrp) : subgeomConj s = subgeom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_subgeom hs hy
  · intro hx
    refine ⟨s⁻¹ • x, smul_mem_subgeom ?_ hx, smul_inv_smul s x⟩
    rw [Subgroup.coe_inv]
    exact Xgrp.inv_mem hs

theorem subgeomConj_one :
    subgeomConj 1 = subgeom := subgeomConj_of_mem Xgrp.one_mem

theorem subgeomConj_mul
    (s t : Shat) : subgeomConj (s * t) = (s • ·) '' subgeomConj t := by
  rw [subgeomConj, subgeomConj, Set.image_image]
  exact Set.image_congr fun x _ => mul_smul s t x

theorem subgeomConj_mul_of_mem
    (s : Shat) {t : Shat} (ht : (t : Dfull) ∈ Xgrp) :
    subgeomConj (s * t) = subgeomConj s := by
  rw [subgeomConj_mul, subgeomConj_of_mem ht]
  rfl

theorem subgeomPairs_subset_ParObj :
    subgeomPairs ⊆ ParObj := by
  rintro p ⟨h1, h4, h, hh, hp⟩
  exact ⟨h1, by omega, h, Xgrp_le_Shat hh, hp⟩

theorem image_val_subgeom :
    Subtype.val '' subgeom = subgeomPairs := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hp
    exact ⟨⟨p, subgeomPairs_subset_ParObj hp⟩, hp, rfl⟩

theorem short_symplectic_subgeometry_data :
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ h ∈ Xgrp, (i, conjSub h (Echain i)) ∈ ParObj) ∧
    (∀ x : ParGeom, x ∈ subgeom ↔
      parType x ≤ 4 ∧ ∃ h ∈ Xgrp, x.1.2 = conjSub h (Echain (parType x))) ∧
    Subtype.val '' subgeom =
      {p : ℕ × Subgroup Dfull | 1 ≤ p.1 ∧ p.1 ≤ 4 ∧ ∃ h ∈ Xgrp, p.2 = conjSub h (Echain p.1)} ∧
    subgeom.Finite ∧
    (∀ x ∈ subgeom, ∀ y ∈ subgeom, parInc x y ↔
      x = y ∨ (parType x ≠ parType y ∧ (x.1.2 ≤ y.1.2 ∨ y.1.2 ≤ x.1.2))) ∧
    (∀ (s : Shat) (x : ParGeom), x ∈ subgeomConj s ↔ s⁻¹ • x ∈ subgeom) ∧
    (∀ (s : Shat) (x : ParGeom), x ∈ subgeomConj s ↔
      parType x ≤ 4 ∧ ∃ h ∈ Xgrp, x.1.2 = conjSub ((s : Dfull) * h) (Echain (parType x))) ∧
    (∀ (s : Shat) (x : ParGeom), parType (s • x) = parType x ∧
      (s • x : ParGeom).1.2 = conjSub (s : Dfull) x.1.2) ∧
    (∀ (s : Shat) (x y : ParGeom), parInc (s • x) (s • y) ↔ parInc x y) ∧
    subgeomConj 1 = subgeom ∧
    (∀ s t : Shat, subgeomConj (s * t) = (s • ·) '' subgeomConj t) ∧
    (∀ s t : Shat, (t : Dfull) ∈ Xgrp → subgeomConj (s * t) = subgeomConj s) :=
  ⟨fun _ h1 h4 h hh => subgeomPairs_subset_ParObj ⟨h1, h4, h, hh, rfl⟩, fun _ => mem_subgeom,
    image_val_subgeom, subgeom_finite, fun _ _ _ _ => Iff.rfl,
    fun _ _ => mem_subgeomConj_iff_inv, fun _ _ => mem_subgeomConj,
    fun s x => ⟨parType_smul s x, smul_obj_snd s x⟩, parInc_smul_iff, subgeomConj_one,
    subgeomConj_mul, fun s _ ht => subgeomConj_mul_of_mem s ht⟩

end CFSG.Monster.B.TwoA.Sp8
