module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairCommutators

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailurePairActionPointHull (H : Subgroup G) (z : G) :
    Subgroup G := Subgroup.closure (conjugacyWithin H z)

theorem minimalLocalFailurePairActionPointHull_le_point (H : Subgroup G)
    {z : G} (hz : z ∈ H) : minimalLocalFailurePairActionPointHull H z ≤ H := by
  apply (Subgroup.closure_le _).mpr
  rintro a ⟨g, rfl⟩
  exact H.mul_mem (H.mul_mem (H.inv_mem g.property) hz) g.property

theorem minimalLocalFailurePairActionClassCommutators_le_pointHull
    (H : Subgroup G) (z : G) :
    minimalLocalFailureProperPairClassCommutators H z ≤
      minimalLocalFailurePairActionPointHull H z := by
  apply (Subgroup.closure_le _).mpr
  rintro c ⟨a, ha, b, hb, rfl⟩
  let Q := minimalLocalFailurePairActionPointHull H z
  have haQ : a ∈ Q := Subgroup.subset_closure ha
  have hbQ : b ∈ Q := Subgroup.subset_closure hb
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.inv_mem haQ) (Q.inv_mem hbQ)) haQ) hbQ

private theorem pointHull_conj_le (H : Subgroup G) (z : G) {g : G} (hg : g ∈ H) :
    (minimalLocalFailurePairActionPointHull H z).map (MulAut.conj g).toMonoidHom ≤
      minimalLocalFailurePairActionPointHull H z := by
  rw [minimalLocalFailurePairActionPointHull, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro a ⟨b, ⟨k, rfl⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨k * (⟨g, hg⟩ : H)⁻¹, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
  change g * (k : G)⁻¹ * z * ((k : G) * g⁻¹) =
    g * ((k : G)⁻¹ * z * k) * g⁻¹
  group

theorem minimalLocalFailurePairActionPointHull_normal_in_point (H : Subgroup G)
    {z : G} (hzH : z ∈ H) :
    ((minimalLocalFailurePairActionPointHull H z).subgroupOf H).Normal := by
  let Q := minimalLocalFailurePairActionPointHull H z
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (minimalLocalFailurePairActionPointHull_le_point H hzH)).mpr
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm (pointHull_conj_le H z hg)
  intro a ha
  have hback : g⁻¹ * a * g ∈ Q := by
    have hmem := pointHull_conj_le H z (H.inv_mem hg)
      (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ha)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem
  refine Subgroup.mem_map.mpr ⟨g⁻¹ * a * g, hback, ?_⟩
  change g * (g⁻¹ * a * g) * g⁻¹ = a
  group

private theorem elementary_two_closure_of_generators (k : Set G)
    (hcomm : k.Pairwise Commute) (hsquare : ∀ a ∈ k, a ^ 2 = 1) :
    IsElemAbelian 2 (Subgroup.closure k) := by
  let : IsMulCommutative (Subgroup.closure k) := Subgroup.isMulCommutative_closure hcomm
  refine ⟨inferInstance, ?_⟩
  intro a ha
  exact Subgroup.closure_induction (k := k) (p := fun x _ => x ^ 2 = 1)
    hsquare (by simp) (by
      intro x y hx hy hxsq hysq
      have hxy : Commute x y := congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : Subgroup.closure k) (⟨y, hy⟩ : Subgroup.closure k))
      rw [hxy.mul_pow, hxsq, hysq, mul_one]) (by
      intro x _ hxsq
      simpa only [inv_pow, inv_one] using congrArg Inv.inv hxsq) ha

theorem minimalLocalFailurePairActionPointHull_elementary_of_commutators_bot
    (H : Subgroup G) {z : G} (hz : orderOf z = 2)
    (hW : minimalLocalFailureProperPairClassCommutators H z = ⊥) :
    IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z) := by
  apply elementary_two_closure_of_generators
  · intro a ha b hb _
    have hmem : a⁻¹ * b⁻¹ * a * b ∈ minimalLocalFailureProperPairClassCommutators H z :=
      Subgroup.subset_closure ⟨a, ha, b, hb, rfl⟩
    rw [hW, Subgroup.mem_bot] at hmem
    have hh : (b * a)⁻¹ * (a * b) = 1 := by
      simpa only [mul_inv_rev, mul_assoc] using hmem
    exact (inv_mul_eq_one.mp hh).symm
  · intro a ha
    have haambient : a ∈ involutionPointClass z := by
      obtain ⟨g, hg⟩ := ha
      exact ⟨g, hg⟩
    exact (orderOf_eq_prime_iff.mp (order_two_of_mem_pointClass hz haambient)).1

theorem minimalLocalFailurePairActionPointHull_subgroupOf (H : Subgroup G)
    {z : G} (hz : z ∈ H) :
    (minimalLocalFailurePairActionPointHull H z).subgroupOf H =
      Subgroup.closure {a : H | (a : G) ∈ conjugacyWithin H z} := by
  let T := Subgroup.closure {a : H | (a : G) ∈ conjugacyWithin H z}
  have himage : H.subtype '' {a : H | (a : G) ∈ conjugacyWithin H z} =
      conjugacyWithin H z := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      have haH := minimalLocalFailurePairActionPointHull_le_point H hz
        (Subgroup.subset_closure ha)
      exact ⟨⟨a, haH⟩, ha, rfl⟩
  have hmap : T.map H.subtype = minimalLocalFailurePairActionPointHull H z := by
    rw [MonoidHom.map_closure, himage]
    rfl
  have hcomap := Subgroup.comap_map_eq_self_of_injective H.subtype_injective T
  rw [hmap] at hcomap
  exact hcomap

theorem minimalLocalFailurePairActionPointHull_quotient_elementary
    (H : Subgroup G) {z : G} (hzH : z ∈ H) (hz : orderOf z = 2) :
    let W := (minimalLocalFailureProperPairClassCommutators H z).subgroupOf H
    letI : W.Normal := minimalLocalFailureProperPairClassCommutators_normal_in_point H hzH
    IsElemAbelian 2 (((minimalLocalFailurePairActionPointHull H z).subgroupOf H).map
      (QuotientGroup.mk' W)) := by
  let W := (minimalLocalFailureProperPairClassCommutators H z).subgroupOf H
  let : W.Normal := minimalLocalFailureProperPairClassCommutators_normal_in_point H hzH
  let f := QuotientGroup.mk' W
  change IsElemAbelian 2 (((minimalLocalFailurePairActionPointHull H z).subgroupOf H).map f)
  rw [minimalLocalFailurePairActionPointHull_subgroupOf H hzH, MonoidHom.map_closure]
  apply elementary_two_closure_of_generators
  · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ _
    have hmem : a⁻¹ * b⁻¹ * a * b ∈ W :=
      Subgroup.subset_closure ⟨(a : G), ha, (b : G), hb, rfl⟩
    have hone : (f a)⁻¹ * (f b)⁻¹ * f a * f b = 1 := by
      have hh : f (a⁻¹ * b⁻¹ * a * b) = 1 :=
        (QuotientGroup.eq_one_iff (a⁻¹ * b⁻¹ * a * b)).mpr hmem
      simpa only [map_mul, map_inv] using hh
    have hright : (f b * f a)⁻¹ * (f a * f b) = 1 := by
      simpa only [mul_inv_rev, mul_assoc] using hone
    exact (inv_mul_eq_one.mp hright).symm
  · rintro x ⟨a, ha, rfl⟩
    have haambient : (a : G) ∈ involutionPointClass z := by
      obtain ⟨g, hg⟩ := ha
      exact ⟨g, hg⟩
    have haorder : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans
      (order_two_of_mem_pointClass hz haambient)
    rw [← map_pow, (orderOf_eq_prime_iff.mp haorder).1, map_one]

theorem minimalLocalFailurePairActionPointHull_quotient_two
    (H : Subgroup G) {z : G} (hzH : z ∈ H) (hz : orderOf z = 2) :
    let W := (minimalLocalFailureProperPairClassCommutators H z).subgroupOf H
    letI : W.Normal := minimalLocalFailureProperPairClassCommutators_normal_in_point H hzH
    IsPGroup 2 (((minimalLocalFailurePairActionPointHull H z).subgroupOf H).map
      (QuotientGroup.mk' W)) := by
  have he := minimalLocalFailurePairActionPointHull_quotient_elementary H hzH hz
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro a
  exact ⟨1, by simpa only [pow_one] using (Subtype.ext (he.2 a a.property) : a ^ 2 = 1)⟩

theorem minimalLocalFailurePairAction_odd_prime_commutator_mem
    (H : Subgroup G) {z : G} (hzH : z ∈ H) (hz : orderOf z = 2)
    (p : ℕ) (hodd : Odd p) (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup p A)
    (hznorm : z ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    z⁻¹ * a⁻¹ * z * a ∈ minimalLocalFailureProperPairClassCommutators H z := by
  let Q := minimalLocalFailurePairActionPointHull H z
  let W := (minimalLocalFailureProperPairClassCommutators H z).subgroupOf H
  let : W.Normal := minimalLocalFailureProperPairClassCommutators_normal_in_point H hzH
  let f := QuotientGroup.mk' W
  let c := z⁻¹ * a⁻¹ * z * a
  have hcQ : c ∈ Q := by
    have hzQ : z ∈ Q := Subgroup.subset_closure ⟨1, by simp⟩
    have hzaQ : a⁻¹ * z * a ∈ Q := Subgroup.subset_closure ⟨⟨a, hAH ha⟩, rfl⟩
    simpa only [c, mul_assoc] using Q.mul_mem (Q.inv_mem hzQ) hzaQ
  have hcA : c ∈ A := by
    have hconj := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (A : Set G)).inv_mem hznorm) a⁻¹).mp (A.inv_mem ha)
    simpa only [inv_inv, c] using A.mul_mem hconj ha
  let cH : H := ⟨c, hAH hcA⟩
  let Qbar := (Q.subgroupOf H).map f
  let Abar := (A.subgroupOf H).map f
  have hQtwo : IsPGroup 2 Qbar := minimalLocalFailurePairActionPointHull_quotient_two H hzH hz
  have hAp : IsPGroup p Abar :=
    (hA.of_injective (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAH).injective).map f
  have hdisjoint : Disjoint Qbar Abar := IsPGroup.disjoint_of_coprime hQtwo hAp
    (by simpa only [Nat.coprime_two_left] using hodd)
  have hzero : f cH = 1 := Subgroup.mem_bot.mp
    (hdisjoint.le_bot ⟨Subgroup.mem_map_of_mem f hcQ, Subgroup.mem_map_of_mem f hcA⟩)
  exact (QuotientGroup.eq_one_iff cH).mp hzero

theorem minimalLocalFailurePairAction_odd_subgroup_commutator_mem [Finite G]
    (H : Subgroup G) {z : G} (hzH : z ∈ H) (hz : orderOf z = 2)
    (A : Subgroup G) (hAH : A ≤ H) (hAodd : Odd (Nat.card A))
    (hznorm : z ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    z⁻¹ * a⁻¹ * z * a ∈ minimalLocalFailureProperPairClassCommutators H z := by
  let Q := minimalLocalFailurePairActionPointHull H z
  let W := (minimalLocalFailureProperPairClassCommutators H z).subgroupOf H
  let : W.Normal := minimalLocalFailureProperPairClassCommutators_normal_in_point H hzH
  let f := QuotientGroup.mk' W
  let c := z⁻¹ * a⁻¹ * z * a
  have hcQ : c ∈ Q := by
    have hzQ : z ∈ Q := Subgroup.subset_closure ⟨1, by simp⟩
    have hzaQ : a⁻¹ * z * a ∈ Q := Subgroup.subset_closure ⟨⟨a, hAH ha⟩, rfl⟩
    simpa only [c, mul_assoc] using Q.mul_mem (Q.inv_mem hzQ) hzaQ
  have hcA : c ∈ A := by
    have hconj := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (A : Set G)).inv_mem hznorm) a⁻¹).mp (A.inv_mem ha)
    simpa only [inv_inv, c] using A.mul_mem hconj ha
  let cH : H := ⟨c, hAH hcA⟩
  let Abar := (A.subgroupOf H).map f
  have hAbarodd : Odd (Nat.card Abar) := by
    have hAinternal : Odd (Nat.card (A.subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
      exact hAodd
    exact hAinternal.of_dvd_nat ((A.subgroupOf H).card_map_dvd f)
  have he := minimalLocalFailurePairActionPointHull_quotient_elementary H hzH hz
  have hcsquare : (f cH) ^ 2 = 1 := he.2 _ (Subgroup.mem_map_of_mem f hcQ)
  have hzero : f cH = 1 := square_one_eq_one_of_mem_odd_subgroup Abar hAbarodd
    (Subgroup.mem_map_of_mem f hcA) hcsquare
  exact (QuotientGroup.eq_one_iff cH).mp hzero

end CFSG.ShultStronglyClosedTI
