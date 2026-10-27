module

public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import CFSG.Monster.B.Geometry.InitialIsometryProduct
public import CFSG.Monster.B.E6.StdF4ResModel

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.E6.StdF4

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

variable (M) in
abbrev parCS (J : Set ι) : CoxeterSystem (parMatrix M J) (parMatrix M J).Group :=
  (parMatrix M J).toCoxeterSystem

@[simp] theorem parCS_simple (J : Set ι) (j : J) :
    (parCS M J).simple j = (parMatrix M J).simple j := rfl

variable (cs δ) in
open _root_.Classical in
@[expose] def parDist (J : Set ι) (x y : C) : (parMatrix M J).Group :=
  if h : δ x y ∈ cs.parabolic J then parOfGroup cs J ⟨δ x y, h⟩ else 1

theorem parDist_of_mem {J : Set ι} {x y : C} (h : δ x y ∈ cs.parabolic J) :
    parDist cs δ J x y = parOfGroup cs J ⟨δ x y, h⟩ := dite_eq_left h

theorem parToGroup_parDist {J : Set ι} {x y : C} (h : δ x y ∈ cs.parabolic J) :
    parToGroup cs J (parDist cs δ J x y) = δ x y := by
  rw [parDist_of_mem h, parToGroup_parOfGroup]

theorem parDist_eq_iff {J : Set ι} {x y : C} (h : δ x y ∈ cs.parabolic J)
    (v : (parMatrix M J).Group) : parDist cs δ J x y = v ↔ δ x y = parToGroup cs J v := by
  rw [parDist_of_mem h, parOfGroup_eq_iff]

section Building

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem parDist_mem {J : Set ι} {a x y : C} (hx : x ∈ residue cs δ J a)
    (hy : y ∈ residue cs δ J a) : δ x y ∈ cs.parabolic J :=
  mem_parabolic_of_mem_residue hδ hx hy

theorem parToGroup_parDist_res {J : Set ι} {a x y : C} (hx : x ∈ residue cs δ J a)
    (hy : y ∈ residue cs δ J a) : parToGroup cs J (parDist cs δ J x y) = δ x y :=
  parToGroup_parDist (parDist_mem hδ hx hy)

theorem parDist_eq_simple_iff {J : Set ι} {a x y : C} (hx : x ∈ residue cs δ J a)
    (hy : y ∈ residue cs δ J a) (j : J) :
    parDist cs δ J x y = (parCS M J).simple j ↔ δ x y = cs.simple j := by
  rw [parCS_simple, parDist_eq_iff (parDist_mem hδ hx hy), parToGroup_simple]

theorem parDist_eq_parDist_iff {C' : Type*} {δ' : C' → C' → W}
    (hδ' : IsWeylDistanceBuilding cs δ') {J : Set ι} {a x y : C} {a' x' y' : C'}
    (hx : x ∈ residue cs δ J a) (hy : y ∈ residue cs δ J a) (hx' : x' ∈ residue cs δ' J a')
    (hy' : y' ∈ residue cs δ' J a') :
    parDist cs δ' J x' y' = parDist cs δ J x y ↔ δ' x' y' = δ x y := by
  rw [parDist_eq_iff (parDist_mem hδ' hx' hy'), parToGroup_parDist_res hδ hx hy]

theorem isWeylDistanceBuilding_parDist (J : Set ι) (a : C) :
    IsWeylDistanceBuilding (parCS M J) fun x y : residue cs δ J a => parDist cs δ J x y where
  nonempty := ⟨⟨a, self_mem_residue J a⟩⟩
  eq_one_iff x y := by
    rw [parDist_eq_iff (parDist_mem hδ x.2 y.2), map_one, hδ.eq_one_iff, Subtype.ext_iff]
  mul_simple x y z j h := by
    rw [parDist_eq_simple_iff hδ y.2 z.2] at h
    obtain ⟨h1, h2⟩ := hδ.mul_simple x y z j h
    have e1 : parDist cs δ J x z = parDist cs δ J x y ↔ δ x z = δ x y := by
      rw [parDist_eq_iff (parDist_mem hδ x.2 z.2), parToGroup_parDist_res hδ x.2 y.2]
    have e2 : parDist cs δ J x z = parDist cs δ J x y * (parCS M J).simple j ↔
        δ x z = δ x y * cs.simple j := by
      rw [parDist_eq_iff (parDist_mem hδ x.2 z.2), map_mul, parToGroup_parDist_res hδ x.2 y.2,
        parCS_simple, parToGroup_simple]
    have e3 : (parCS M J).length (parDist cs δ J x y * (parCS M J).simple j) =
        cs.length (δ x y * cs.simple j) := by
      rw [← length_parToGroup cs J, map_mul, parToGroup_parDist_res hδ x.2 y.2, parCS_simple,
        parToGroup_simple]
    have e4 : (parCS M J).length (parDist cs δ J x y) = cs.length (δ x y) := by
      rw [← length_parToGroup cs J, parToGroup_parDist_res hδ x.2 y.2]
    refine ⟨?_, fun hl => e2.mpr (h2 (by rw [← e3, hl, e4]))⟩
    rcases h1 with h1 | h1
    · exact Or.inl (e1.mpr h1)
    · exact Or.inr (e2.mpr h1)
  exists_simple x y j := by
    obtain ⟨z, hyz, hxz⟩ := hδ.exists_simple x y j
    have hz : z ∈ residue cs δ J a :=
      mem_residue_trans y.2 (Relation.ReflTransGen.single ⟨j, j.2, hyz⟩)
    refine ⟨⟨z, hz⟩, (parDist_eq_simple_iff hδ y.2 hz j).mpr hyz, ?_⟩
    change parDist cs δ J x z = parDist cs δ J x y * (parCS M J).simple j
    rw [parDist_eq_iff (parDist_mem hδ x.2 hz), map_mul, parToGroup_parDist_res hδ x.2 y.2,
      parCS_simple, parToGroup_simple, hxz]

theorem mem_residue_parDist_iff {J : Set ι} {a : C} (I : Set J) (y z : residue cs δ J a) :
    z ∈ residue (parCS M J) (fun x y : residue cs δ J a => parDist cs δ J x y) I y ↔
      (z : C) ∈ residue cs δ (Subtype.val '' I) y := by
  rw [mem_residue_iff_mem_parabolic (isWeylDistanceBuilding_parDist hδ J a),
    mem_residue_iff_mem_parabolic hδ, parDist_of_mem (parDist_mem hδ y.2 z.2),
    parOfGroup_mem_parabolic_iff]

theorem mem_foundation_parDist_iff {J : Set ι} {a : C} (y z : residue cs δ J a) :
    z ∈ foundation (parCS M J) (fun x y : residue cs δ J a => parDist cs δ J x y) 2 y ↔
      (z : C) ∈ residueFoundation cs δ J y := by
  rw [mem_foundation_iff, mem_residueFoundation_iff]
  constructor
  · rintro ⟨I, hI, hz⟩
    refine ⟨Subtype.val '' I, ⟨fun i ⟨j, _, hj⟩ => hj ▸ j.2, ?_⟩,
      (mem_residue_parDist_iff hδ I y z).mp hz⟩
    rw [Subtype.val_injective.encard_image]
    exact_mod_cast hI
  · rintro ⟨I, ⟨hIJ, hI⟩, hz⟩
    have himg : Subtype.val '' (Subtype.val ⁻¹' I : Set J) = I := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hIJ]
    refine ⟨Subtype.val ⁻¹' I, ?_, (mem_residue_parDist_iff hδ _ y z).mpr (by rwa [himg])⟩
    rw [← Subtype.val_injective.encard_image, himg]
    exact_mod_cast hI

theorem parDist_eq_longest_iff [Finite W] {J : Set ι} {a x y : C} (hx : x ∈ residue cs δ J a)
    (hy : y ∈ residue cs δ J a) (I : Set J) :
    parDist cs δ J x y = longest (parCS M J) I ↔ δ x y = longest cs (Subtype.val '' I) := by
  rw [parDist_eq_iff (parDist_mem hδ hx hy), parToGroup_longest]

theorem parDist_eq_longest_univ_iff [Finite W] {J : Set ι} {a x y : C}
    (hx : x ∈ residue cs δ J a) (hy : y ∈ residue cs δ J a) :
    parDist cs δ J x y = longest (parCS M J) Set.univ ↔ δ x y = longest cs J := by
  rw [parDist_eq_longest_iff hδ hx hy, Set.image_univ, Subtype.range_coe]

end Building

variable (J : Set ι) in
@[expose] def resMap {C' : Type*} {R : Set C} {R' : Set C'} (G : C → C') (dflt : R')
    (x : R) : R' :=
  open _root_.Classical in if h : G x ∈ R' then ⟨G x, h⟩ else dflt

theorem coe_resMap {C' : Type*} {R : Set C} {R' : Set C'} {G : C → C'} {dflt : R'} {x : R}
    (h : G x ∈ R') : (resMap G dflt x : C') = G x := by
  rw [resMap, dite_eq_left h]

section Maps

variable {C' : Type*} {δ' : C' → C' → W} {J : Set ι} {a : C} {a' : C'}

theorem bijOn_resMap_iff {X : Set C} {X' : Set C'} (hX : X ⊆ residue cs δ J a)
    (hX' : X' ⊆ residue cs δ' J a') {G : C → C'} (hG : Set.MapsTo G X X')
    (dflt : residue cs δ' J a') :
    Set.BijOn G X X' ↔
      Set.BijOn (resMap (R := residue cs δ J a) G dflt) (Subtype.val ⁻¹' X)
        (Subtype.val ⁻¹' X') := by
  have hc : ∀ x : residue cs δ J a, (x : C) ∈ X → (resMap G dflt x : C') = G x :=
    fun x hx => coe_resMap (hX' (hG hx))
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx y hy e => Subtype.ext (h.injOn hx hy ?_), fun y hy => ?_⟩
    · change ((resMap G dflt x : residue cs δ' J a') : C') ∈ X'
      rw [hc x hx]
      exact h.mapsTo hx
    · rw [← hc x hx, ← hc y hy, e]
    · obtain ⟨x, hx, hxy⟩ := h.surjOn hy
      exact ⟨⟨x, hX hx⟩, hx, Subtype.ext ((hc _ hx).trans hxy)⟩
  · intro h
    refine ⟨hG, fun x hx y hy e => ?_, fun y hy => ?_⟩
    · have := h.injOn (show (⟨x, hX hx⟩ : residue cs δ J a) ∈ Subtype.val ⁻¹' X from hx)
        (show (⟨y, hX hy⟩ : residue cs δ J a) ∈ Subtype.val ⁻¹' X from hy)
        (Subtype.ext ((hc ⟨x, hX hx⟩ hx).trans (e.trans (hc ⟨y, hX hy⟩ hy).symm)))
      exact congrArg Subtype.val this
    · obtain ⟨x, hx, hxy⟩ :=
        h.surjOn (show (⟨y, hX' hy⟩ : residue cs δ' J a') ∈ Subtype.val ⁻¹' X' from hy)
      exact ⟨x, hx, (hc x hx).symm.trans (congrArg Subtype.val hxy)⟩

variable (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
include hδ hδ'

theorem isTypeIso_resMap_iff {X : Set C} {X' : Set C'} (hX : X ⊆ residue cs δ J a)
    (hX' : X' ⊆ residue cs δ' J a') {G : C → C'} (hG : Set.MapsTo G X X')
    (dflt : residue cs δ' J a') :
    IsTypeIso cs δ δ' X X' G ↔
      IsTypeIso (parCS M J) (fun x y : residue cs δ J a => parDist cs δ J x y)
        (fun x y : residue cs δ' J a' => parDist cs δ' J x y) (Subtype.val ⁻¹' X)
        (Subtype.val ⁻¹' X') (resMap (R := residue cs δ J a) G dflt) := by
  have hc : ∀ x : residue cs δ J a, (x : C) ∈ X → (resMap G dflt x : C') = G x :=
    fun x hx => coe_resMap (hX' (hG hx))
  rw [IsTypeIso, IsTypeIso, bijOn_resMap_iff hX hX' hG dflt]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx y hy j
    rw [parDist_eq_simple_iff hδ' (resMap G dflt x).2 (resMap G dflt y).2,
      parDist_eq_simple_iff hδ x.2 y.2, hc x hx, hc y hy]
    exact h x hx y hy j
  · intro h x hx y hy i
    by_cases hi : i ∈ J
    · have := h ⟨x, hX hx⟩ hx ⟨y, hX hy⟩ hy ⟨i, hi⟩
      rwa [parDist_eq_simple_iff hδ' (resMap G dflt _).2 (resMap G dflt _).2,
        parDist_eq_simple_iff hδ (hX hx) (hX hy), hc _ hx, hc _ hy] at this
    · exact ⟨fun e => absurd e (dist_ne_simple_of_mem_residue hδ' (hX' (hG hx)) (hX' (hG hy)) hi),
        fun e => absurd e (dist_ne_simple_of_mem_residue hδ (hX hx) (hX hy) hi)⟩

theorem isWeylIsometry_resMap_iff {X : Set C} {X' : Set C'} (hX : X ⊆ residue cs δ J a)
    (hX' : X' ⊆ residue cs δ' J a') {G : C → C'} (hG : Set.MapsTo G X X')
    (dflt : residue cs δ' J a') :
    IsWeylIsometry δ δ' X X' G ↔
      IsWeylIsometry (fun x y : residue cs δ J a => parDist cs δ J x y)
        (fun x y : residue cs δ' J a' => parDist cs δ' J x y) (Subtype.val ⁻¹' X)
        (Subtype.val ⁻¹' X') (resMap (R := residue cs δ J a) G dflt) := by
  have hc : ∀ x : residue cs δ J a, (x : C) ∈ X → (resMap G dflt x : C') = G x :=
    fun x hx => coe_resMap (hX' (hG hx))
  rw [IsWeylIsometry, IsWeylIsometry, bijOn_resMap_iff hX hX' hG dflt]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx y hy
    rw [parDist_eq_parDist_iff hδ hδ' x.2 y.2 (resMap G dflt x).2 (resMap G dflt y).2, hc x hx,
      hc y hy]
    exact h x hx y hy
  · intro h x hx y hy
    have := h ⟨x, hX hx⟩ hx ⟨y, hX hy⟩ hy
    rwa [parDist_eq_parDist_iff hδ hδ' (hX hx) (hX hy) (resMap G dflt _).2 (resMap G dflt _).2,
      hc _ hx, hc _ hy] at this

end Maps

end CFSG.Monster.B.Geometry
