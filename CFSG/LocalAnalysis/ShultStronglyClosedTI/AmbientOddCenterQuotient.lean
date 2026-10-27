module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.TIHullCentralWitness
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientStrongClosure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def ambientOddCenter (L : Subgroup G) : Subgroup G :=
  (oddCenterSubgroup L).map L.subtype

instance ambientOddCenter_normal (L : Subgroup G) [L.Normal] :
    (ambientOddCenter L).Normal := ConjAct.normal_of_characteristic_of_normal

theorem ambientOddCenter_le (L : Subgroup G) : ambientOddCenter L ≤ L :=
  Subgroup.map_subtype_le _

theorem ambientOddCenter_subgroupOf (L : Subgroup G) :
    (ambientOddCenter L).subgroupOf L = oddCenterSubgroup L := by
  ext l
  constructor
  · intro hl
    obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hl
    exact (Subtype.ext heq) ▸ ha
  · intro hl
    exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩

theorem ambientOddCenter_odd_card [Finite G] (L : Subgroup G) :
    Odd (Nat.card (ambientOddCenter L)) := by
  rw [ambientOddCenter, Subgroup.card_map_of_injective L.subtype_injective]
  exact oddCenterSubgroup_odd_card L

theorem ambientOddCenter_restriction_kernel (L : Subgroup G) [L.Normal] :
    ((QuotientGroup.mk' (ambientOddCenter L)).subgroupMap L).ker =
      oddCenterSubgroup L := by
  rw [central_lift_subgroup_map_kernel, QuotientGroup.ker_mk',
    ambientOddCenter_subgroupOf]

@[expose] def ambientOddCenterHullEquiv (L : Subgroup G) [L.Normal] :
    (L ⧸ oddCenterSubgroup L) ≃*
      L.map (QuotientGroup.mk' (ambientOddCenter L)) :=
  QuotientGroup.liftEquiv (oddCenterSubgroup L)
    ((QuotientGroup.mk' (ambientOddCenter L)).subgroupMap_surjective L)
    (ambientOddCenter_restriction_kernel L).symm

theorem ambientOddCenterHullEquiv_mk (L : Subgroup G) [L.Normal] (l : L) :
    ambientOddCenterHullEquiv L (QuotientGroup.mk' (oddCenterSubgroup L) l) =
      (QuotientGroup.mk' (ambientOddCenter L)).subgroupMap L l :=
  QuotientGroup.liftEquiv_mk _ _ _ l

theorem ambientOddCenter_center_image (L : Subgroup G) [L.Normal]
    [Group.IsPerfect L] :
    (Subgroup.center L).map
        ((QuotientGroup.mk' (ambientOddCenter L)).subgroupMap L) =
      Subgroup.center (L.map (QuotientGroup.mk' (ambientOddCenter L))) := by
  apply CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
    _ ((QuotientGroup.mk' (ambientOddCenter L)).subgroupMap_surjective L)
  rw [ambientOddCenter_restriction_kernel]
  exact oddCenterSubgroup_le_center L

theorem ambient_odd_center_hull_structure [Finite G] (L : Subgroup G) [L.Normal]
    [Group.IsPerfect L] (hquasi : IsQuasisimple L)
    (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L)) :
    let q := QuotientGroup.mk' (ambientOddCenter L)
    (L.map q).Normal ∧ Group.IsPerfect (L.map q) ∧ IsQuasisimple (L.map q) ∧
      IsPGroup 2 (Subgroup.center (L.map q)) ∧
      fusionIsBenderGroup ((L.map q) ⧸ Subgroup.center (L.map q)) := by
  let q := QuotientGroup.mk' (ambientOddCenter L)
  let f := q.subgroupMap L
  let e := ambientOddCenterHullEquiv L
  have hquot := odd_center_quotient_structure L hquasi hmodel
  have hpcenter : IsPGroup 2 (Subgroup.center (L.map q)) := by
    rw [← Subgroup.map_center_eq e]
    exact hquot.2.2.1.map e.toMonoidHom
  have hcentral : f.ker ≤ Subgroup.center L := by
    rw [ambientOddCenter_restriction_kernel]
    exact oddCenterSubgroup_le_center L
  refine ⟨Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _),
    Group.IsPerfect.map q,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hquot.1,
    hpcenter, ?_⟩
  exact central_lift_model_transport
    (centralLiftCenterQuotientEquiv f (q.subgroupMap_surjective L) hcentral).symm hmodel

theorem ambient_odd_center_subgroup_images [Finite G] (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (U : Subgroup G) (hUL : U ≤ L)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) :
    let q := QuotientGroup.mk' (ambientOddCenter L)
    let T₁ := T.mapSurjective (QuotientGroup.mk'_surjective (ambientOddCenter L))
    IsElemAbelian 2 (U.map q) ∧ Nat.card (U.map q) = Nat.card U ∧
      U.map q ≤ (T₁ : Subgroup (G ⧸ ambientOddCenter L)) ∧
      U.map q ≤ L.map q ∧
      fusionStronglyClosed (U.map q : Set (G ⧸ ambientOddCenter L))
        (T₁ : Subgroup (G ⧸ ambientOddCenter L)) := by
  let q := QuotientGroup.mk' (ambientOddCenter L)
  have hinj := odd_quotient_injective_on_elementary U (ambientOddCenter L)
    hUel (ambientOddCenter_odd_card L)
  have hcard : Nat.card (U.map q) = Nat.card U := by
    apply (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap U)
      ⟨?_, q.subgroupMap_surjective U⟩).toEquiv).symm
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  refine ⟨CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U hUel q, hcard,
    ?_, Subgroup.map_mono hUL, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hUT
  · exact stronglyClosed_map_surjective q (QuotientGroup.mk'_surjective _)
      T U hUT hclosed

theorem ambient_odd_center_witness_image [Finite G] (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (U : Subgroup G) (hUL : U ≤ L) {w : G} (hwU : w ∈ U)
    (hwT : w ∈ (T : Subgroup G))
    (hwcentral : (⟨w, hwT⟩ : (T : Subgroup G)) ∈
      Subgroup.center (T : Subgroup G)) :
    let q := QuotientGroup.mk' (ambientOddCenter L)
    let T₁ := T.mapSurjective (QuotientGroup.mk'_surjective (ambientOddCenter L))
    q w ∈ U.map q ∧ q w ∈ L.map q ∧
      ∃ hw₁ : q w ∈ (T₁ : Subgroup (G ⧸ ambientOddCenter L)),
        (⟨q w, hw₁⟩ : (T₁ : Subgroup (G ⧸ ambientOddCenter L))) ∈
          Subgroup.center (T₁ : Subgroup (G ⧸ ambientOddCenter L)) := by
  let q := QuotientGroup.mk' (ambientOddCenter L)
  let T₁ := T.mapSurjective (QuotientGroup.mk'_surjective (ambientOddCenter L))
  have hw₁ : q w ∈ (T₁ : Subgroup (G ⧸ ambientOddCenter L)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem q hwT
  refine ⟨Subgroup.mem_map_of_mem q hwU, Subgroup.mem_map_of_mem q (hUL hwU),
    hw₁, Subgroup.mem_center_iff.mpr ?_⟩
  intro t
  have ht : (t : G ⧸ ambientOddCenter L) ∈ (T : Subgroup G).map q := by
    simpa only [T₁, Sylow.coe_mapSurjective] using t.property
  obtain ⟨s, hs, heq⟩ := Subgroup.mem_map.mp ht
  apply Subtype.ext
  change t.val * q w = q w * t.val
  rw [← heq, ← map_mul, ← map_mul]
  exact congrArg q (congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hwcentral (⟨s, hs⟩ : (T : Subgroup G))))

theorem ambient_odd_center_ti_hull_witness [Finite G] (T : Sylow 2 G)
    (U : Subgroup G) (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (hperfect : Group.IsPerfect (Subgroup.normalClosure (U : Set G)))
    (hquasi : IsQuasisimple (Subgroup.normalClosure (U : Set G))) :
    let L := Subgroup.normalClosure (U : Set G)
    let q := QuotientGroup.mk' (ambientOddCenter L)
    let T₁ := T.mapSurjective (QuotientGroup.mk'_surjective (ambientOddCenter L))
    ∃ w : G, w ∈ U ∧ orderOf w = 2 ∧ orderOf (q w) = 2 ∧
      q w ∈ U.map q ∧ q w ∈ L.map q ∧
      (∃ hw₁ : q w ∈ (T₁ : Subgroup (G ⧸ ambientOddCenter L)),
        (⟨q w, hw₁⟩ : (T₁ : Subgroup (G ⧸ ambientOddCenter L))) ∈
          Subgroup.center (T₁ : Subgroup (G ⧸ ambientOddCenter L))) ∧
      q w ∉ (Subgroup.center (L.map q)).map (L.map q).subtype := by
  let L := Subgroup.normalClosure (U : Set G)
  let q := QuotientGroup.mk' (ambientOddCenter L)
  obtain ⟨w, hwU, _, horder, ⟨hwT, hwcentral⟩, hwnoncentral⟩ :=
    ti_hull_odd_quotient_central_witness T U hUT hU hUel hclosed hTI hnormal
      hperfect hquasi
  have hwnoncentral' : q w ∉
      (Subgroup.center (L.map q)).map (L.map q).subtype := hwnoncentral
  have hwne : q w ≠ 1 := by
    intro heq
    exact hwnoncentral' (heq.symm ▸ Subgroup.one_mem _)
  have hqorder : orderOf (q w) = 2 := orderOf_eq_prime_iff.mpr ⟨by
    rw [← map_pow, (orderOf_eq_prime_iff.mp horder).1, map_one], hwne⟩
  have himages := ambient_odd_center_witness_image L T U Subgroup.subset_normalClosure
    hwU hwT hwcentral
  exact ⟨w, hwU, horder, hqorder, himages.1, himages.2.1, himages.2.2,
    hwnoncentral'⟩

end CFSG.ShultStronglyClosedTI
