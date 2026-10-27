module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaCentralExtension

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFchapter1section1
open scoped commutatorElement IsMulCommutative

universe u v

variable {G : Type u} [Group G]

theorem elementary_image_descends_quotient
    {F : Type v} [Group F] (f : G →* F) (I R : Subgroup G) [R.Normal]
    (hkernel : f.ker ≤ R) [IsElementaryAbelian 2 (I.map f)] :
    IsElementaryAbelian 2 (I.map (QuotientGroup.mk' R)) := by
  let q := QuotientGroup.mk' R
  have hcomm : IsMulCommutative (I.map q) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨i, hi, hix⟩ := Subgroup.mem_map.mp x.property
    obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.mp y.property
    have hfi : f i ∈ I.map f := Subgroup.mem_map.mpr ⟨i, hi, rfl⟩
    have hfj : f j ∈ I.map f := Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
    have hcommf : f i * f j = f j * f i := congrArg Subtype.val
      (mul_comm (⟨f i, hfi⟩ : I.map f) (⟨f j, hfj⟩ : I.map f))
    have hker : ⁅i, j⁆ ∈ f.ker := by
      change f ⁅i, j⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcommf
    have hcommq : q i * q j = q j * q i :=
      commutatorElement_eq_one_iff_mul_comm.mp (by
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr (hkernel hker))
    apply Subtype.ext
    change x.val * y.val = y.val * x.val
    rw [← hix, ← hjy]
    exact hcommq
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  obtain ⟨i, hi, hix⟩ := Subgroup.mem_map.mp x.property
  have hfi : f i ∈ I.map f := Subgroup.mem_map.mpr ⟨i, hi, rfl⟩
  have hker : i ^ 2 ∈ f.ker := by
    change f (i ^ 2) = 1
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian _ hfi
  apply Subtype.ext
  change x.val ^ 2 = 1
  rw [← hix, ← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (hkernel hker)

theorem normal_quotient_class_centralizer
    (R N T : Subgroup G) [R.Normal] [N.Normal] {z : G}
    (hcomm : ∀ r ∈ R, ⁅r, z⁆ ∈ N) :
    R.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer
      ((Subgroup.closure (conjugacyWithin T z)).map (QuotientGroup.mk' N) : Set (G ⧸ N)) := by
  let q := QuotientGroup.mk' N
  let C := Subgroup.centralizer (R.map q : Set (G ⧸ N))
  let : (R.map q).Normal := (inferInstance : R.Normal).map q
    (QuotientGroup.mk'_surjective N)
  have hzC : q z ∈ C := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro a ⟨r, hr, rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm r hr)
  have hIC : (Subgroup.closure (conjugacyWithin T z)).map q ≤ C := by
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨i, ⟨t, rfl⟩, rfl⟩
    change q ((t : G)⁻¹ * z * t) ∈ C
    rw [map_mul, map_mul, map_inv]
    have hh := (inferInstance : C.Normal).conj_mem (q z) hzC (q (t : G))⁻¹
    simpa only [inv_inv] using hh
  exact Subgroup.le_centralizer_iff.mp hIC

theorem odd_central_class_image_intersection_le [Finite G]
    (R N : Subgroup G) [R.Normal] [N.Normal] (hNR : N ≤ R)
    (hRodd : Odd (Nat.card R)) (s : Set G)
    [IsElementaryAbelian 2 ((Subgroup.closure s).map (QuotientGroup.mk' R))]
    (hsquare : ∀ x ∈ s, x ^ 2 = 1)
    (hcentral : R.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer
      ((Subgroup.closure s).map (QuotientGroup.mk' N) : Set (G ⧸ N))) :
    Subgroup.closure s ⊓ R ≤ N := by
  let I := Subgroup.closure s
  let q := QuotientGroup.mk' N
  let r := QuotientGroup.mk' R
  let IN := I.map q
  let IR := I.map r
  let lift := QuotientGroup.map N R (MonoidHom.id G) hNR
  let e : IN →* IR := (lift.comp IN.subtype).codRestrict _ (by
    rintro ⟨a, ha⟩
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨i, hi, rfl⟩)
  have hkerR : ∀ a : e.ker, (a.val.val : G ⧸ N) ∈ R.map q := by
    intro a
    obtain ⟨i, hi, hia⟩ := Subgroup.mem_map.mp a.val.property
    have hir : r i = 1 := by
      have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp a.property)
      change lift a.val.val = 1 at hh
      rw [← hia] at hh
      exact hh
    exact Subgroup.mem_map.mpr ⟨i, (QuotientGroup.eq_one_iff i).mp hir, hia⟩
  let kR : e.ker →* R.map q := (IN.subtype.comp e.ker.subtype).codRestrict _ hkerR
  have hkRinj : Function.Injective kR := by
    intro a b hab
    have hh : (a.val.val : G ⧸ N) = b.val.val :=
      congrArg (fun x : R.map q => (x : G ⧸ N)) hab
    exact e.ker.subtype_injective (IN.subtype_injective hh)
  have hkerodd : Odd (Nat.card e.ker) :=
    (hRodd.of_dvd_nat (Subgroup.card_map_dvd R q)).of_dvd_nat
      (Subgroup.card_dvd_of_injective kR hkRinj)
  have hkercentral : e.ker ≤ Subgroup.center IN := by
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcentral (hkerR ⟨a, ha⟩))) b.val b.property
  let t : I →* IN := q.subgroupMap I
  let sN : Set IN := t '' (I.subtype ⁻¹' s)
  have hgen : Subgroup.closure sN = ⊤ := by
    rw [← MonoidHom.map_closure, Subgroup.closure_preimage_eq_top s,
      Subgroup.map_top, t.range_eq_top_of_surjective (q.subgroupMap_surjective I)]
  have hsN : ∀ a ∈ sN, a ^ 2 = 1 := by
    rintro a ⟨i, hi, rfl⟩
    apply Subtype.ext
    change q (i : G) ^ 2 = 1
    rw [← map_pow, hsquare i hi, map_one]
  obtain ⟨_helem, heinj⟩ := involution_generated_odd_central_hom e hkerodd hkercentral
    sN hgen hsN
  intro i hi
  have hqi : q i ∈ IN := Subgroup.mem_map.mpr ⟨i, hi.1, rfl⟩
  have heone : e (⟨q i, hqi⟩ : IN) = 1 := by
    apply Subtype.ext
    change r i = 1
    exact (QuotientGroup.eq_one_iff i).mpr hi.2
  have hione : (⟨q i, hqi⟩ : IN) = 1 := heinj (heone.trans e.map_one.symm)
  exact (QuotientGroup.eq_one_iff i).mp (congrArg Subtype.val hione)

end CFSG.ShultStronglyClosedTI.LocalTheta
