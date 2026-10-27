module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalInductionDatum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCenterQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem stronglyClosed_sylow_central_witness (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) :
    ∃ w : G, w ∈ U ∧ w ≠ 1 ∧ orderOf w = 2 ∧
      ∃ hwT : w ∈ (T : Subgroup G),
        (⟨w, hwT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) := by
  let V : Subgroup (T : Subgroup G) := U.subgroupOf (T : Subgroup G)
  let : V.Normal := normal_in_sylow T U hUT hclosed
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hV : V ≠ ⊥ := by
    intro hbot
    have hmap := congrArg (Subgroup.map (T : Subgroup G).subtype) hbot
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUT, Subgroup.map_bot] at hmap
    exact hU hmap
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hV)
  let w : G := a.val.val
  have hwU : w ∈ U := a.property.1
  have hwne : w ≠ 1 := by
    intro h
    exact ha (Subtype.ext (Subtype.ext h))
  refine ⟨w, hwU, hwne, orderOf_eq_prime_iff.mpr ⟨hUel.2 w hwU, hwne⟩,
    a.val.property, ?_⟩
  exact a.property.2

theorem ti_element_not_mem_hull_center (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (hperfect : Group.IsPerfect (Subgroup.normalClosure (U : Set G)))
    (hquasi : IsQuasisimple (Subgroup.normalClosure (U : Set G)))
    {w : G} (hwU : w ∈ U) (hwne : w ≠ 1) :
    (⟨w, Subgroup.subset_normalClosure hwU⟩ : Subgroup.normalClosure (U : Set G)) ∉
      Subgroup.center (Subgroup.normalClosure (U : Set G)) := by
  let L := Subgroup.normalClosure (U : Set G)
  let Z : Subgroup G := (Subgroup.center L).map L.subtype
  let : Group.IsPerfect L := hperfect
  let : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hquasi
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  intro hwZ
  have hwZG : w ∈ Z := Subgroup.mem_map.mpr
    ⟨⟨w, Subgroup.subset_normalClosure hwU⟩, hwZ, rfl⟩
  have hclass := (localInduction_ti_family_geometry T U hUT hU hUel hclosed hTI
    hnormal hwU hwne).1
  have hDZ : conjugateInvolutions U ⊆ (Z : Set G) := by
    intro a ha
    rw [hclass] at ha
    obtain ⟨g, rfl⟩ := isConj_iff.mp ha
    exact (inferInstance : Z.Normal).conj_mem w hwZG g
  have hLZ : L ≤ Z := by
    change Subgroup.normalClosure (U : Set G) ≤ Z
    rw [← closure_conjugateInvolutions_eq_normalClosure U]
    exact (Subgroup.closure_le Z).mpr hDZ
  have hcenter : Subgroup.center L = ⊤ := by
    apply top_unique
    intro l _
    obtain ⟨z, hz, heq⟩ := Subgroup.mem_map.mp (hLZ l.property)
    exact (Subtype.ext heq) ▸ hz
  have hcomm : IsMulCommutative L := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have haZ : a ∈ Subgroup.center L := hcenter.symm ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp haZ b).symm
  exact Group.IsPerfect.not_isMulCommutative L hcomm

theorem ti_hull_odd_quotient_central_witness (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (hperfect : Group.IsPerfect (Subgroup.normalClosure (U : Set G)))
    (hquasi : IsQuasisimple (Subgroup.normalClosure (U : Set G))) :
    let L := Subgroup.normalClosure (U : Set G)
    let A : Subgroup G := (oddCenterSubgroup L).map L.subtype
    ∃ w : G, w ∈ U ∧ w ≠ 1 ∧ orderOf w = 2 ∧
      (∃ hwT : w ∈ (T : Subgroup G),
        (⟨w, hwT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G)) ∧
      (QuotientGroup.mk' A) w ∉
        (Subgroup.center (L.map (QuotientGroup.mk' A))).map
          (L.map (QuotientGroup.mk' A)).subtype := by
  let L := Subgroup.normalClosure (U : Set G)
  let A : Subgroup G := (oddCenterSubgroup L).map L.subtype
  let : Group.IsPerfect L := hperfect
  let : A.Normal := ConjAct.normal_of_characteristic_of_normal
  let q := QuotientGroup.mk' A
  let f := q.subgroupMap L
  obtain ⟨w, hwU, hwne, hworder, hwT⟩ :=
    stronglyClosed_sylow_central_witness T U hUT hU hUel hclosed
  refine ⟨w, hwU, hwne, hworder, hwT, ?_⟩
  have hnoncentral := ti_element_not_mem_hull_center T U hUT hU hUel hclosed hTI
    hnormal hperfect hquasi hwU hwne
  have hfcentral : f.ker ≤ Subgroup.center L := by
    rw [central_lift_subgroup_map_kernel, QuotientGroup.ker_mk']
    intro a ha
    obtain ⟨b, hb, heq⟩ := Subgroup.mem_map.mp ha
    exact (Subtype.ext heq) ▸ oddCenterSubgroup_le_center L hb
  have hpreimage := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
    f (q.subgroupMap_surjective L) hfcentral
  intro hcentral
  obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hcentral
  have helem : f (⟨w, Subgroup.subset_normalClosure hwU⟩ : L) = a :=
    Subtype.ext heq.symm
  apply hnoncentral
  rw [← hpreimage]
  change f (⟨w, Subgroup.subset_normalClosure hwU⟩ : L) ∈ Subgroup.center (L.map q)
  exact helem.symm ▸ ha

end CFSG.ShultStronglyClosedTI
