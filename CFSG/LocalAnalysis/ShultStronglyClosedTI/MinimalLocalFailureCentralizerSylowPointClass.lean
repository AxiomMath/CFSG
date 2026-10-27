module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowFrattini
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem local_point_involution_class_ambient
    (H F : Subgroup G) (hA : CFSG.BenderSuzuki.IsStronglyEmbedded (H.subgroupOf F))
    (z : G) (hzH : z ∈ H) (hzF : z ∈ F) (hz : orderOf z = 2) :
    ∀ v ∈ H ⊓ F, orderOf v = 2 → v ∈ conjugacyWithin (H ⊓ F) z := by
  intro v hv hvi
  let zF : F := ⟨z, hzF⟩
  let vF : F := ⟨v, hv.2⟩
  have hzFi : IsInvolution zF := by
    have hh : orderOf zF = 2 := (Subgroup.orderOf_coe zF).symm.trans hz
    exact ⟨(orderOf_eq_prime_iff.mp hh).2, (orderOf_eq_prime_iff.mp hh).1⟩
  have hvFi : IsInvolution vF := by
    have hh : orderOf vF = 2 := (Subgroup.orderOf_coe vF).symm.trans hvi
    exact ⟨(orderOf_eq_prime_iff.mp hh).2, (orderOf_eq_prime_iff.mp hh).1⟩
  obtain ⟨a, ha, hconj⟩ := hA.involutions_conjugate_in hzH hzFi hv.1 hvFi
  exact ⟨⟨a.val, ha, a.property⟩, congrArg Subtype.val hconj⟩

theorem point_class_full_centralizer_odd
    (A X : Subgroup G) (hAX : A ≤ Subgroup.normalizer (X : Set G)) (z : G)
    (hclass : ∀ v ∈ A, orderOf v = 2 → v ∈ conjugacyWithin A z)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G)) :
    Odd (Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  let D := A ⊓ Subgroup.centralizer (X : Set G)
  let DA := D.subgroupOf A
  let : DA.Normal := full_point_centralizer_normal A X hAX
  by_contra hnot
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := D) 2
    (Nat.not_odd_iff_even.mp hnot).two_dvd
  have hvG : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hv
  obtain ⟨a, ha⟩ := hclass v.val v.property.1 hvG
  let vA : A := ⟨v.val, v.property.1⟩
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    have hh := (inferInstance : DA.Normal).conj_mem vA
      (show vA ∈ DA from v.property) a
    have hvalue : (a : G) * v.val * (a : G)⁻¹ = z := by
      rw [← ha]
      group
    have hzD : z ∈ D := by
      change (a : G) * v.val * (a : G)⁻¹ ∈ D at hh
      rwa [hvalue] at hh
    exact hzD.2
  apply hnoncentral
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hzC x hx)

theorem point_class_centralizer_sylow_normalizer
    (A X : Subgroup G) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2)
    (hclass : ∀ v ∈ A, orderOf v = 2 → v ∈ conjugacyWithin A z)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G))
    (p : ℕ) (hp : p.Prime)
    (P : Sylow p (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :
    (conjugacyWithin A z ∩ (Subgroup.normalizer
      (((P : Subgroup (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)).map
        (A ⊓ Subgroup.centralizer (X : Set G)).subtype : Subgroup G) : Set G) : Set G)).Nonempty := by
  let D := A ⊓ Subgroup.centralizer (X : Set G)
  let DA := D.subgroupOf A
  let : DA.Normal := full_point_centralizer_normal A X hAX
  have hDodd : Odd (Nat.card D) := point_class_full_centralizer_odd A X hAX z hclass hnoncentral
  have hDAodd : Odd (Nat.card DA) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ≤ A)).toEquiv]
    exact hDodd
  have heven : Even (Nat.card A) := by
    let zA : A := ⟨z, hzA⟩
    have hzAorder : orderOf zA = 2 := (Subgroup.orderOf_coe zA).symm.trans hz
    exact even_iff_two_dvd.mpr (hzAorder ▸ orderOf_dvd_natCard zA)
  obtain ⟨PA, hPA⟩ := sylow_subgroupOf_restriction_ambient_image p hp D A inf_le_left P
  let Q := (PA : Subgroup DA).map DA.subtype
  let N := Subgroup.normalizer (Q : Set A)
  have hNeven : Even (Nat.card N) := odd_normal_sylow_normalizer_even DA hDAodd heven p hp PA
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hNeven.two_dvd
  have hvA : orderOf (v.val : A) = 2 := (Subgroup.orderOf_coe v).trans hv
  have hvG : orderOf (v.val.val : G) = 2 := (Subgroup.orderOf_coe v.val).trans hvA
  refine ⟨v.val.val, hclass v.val.val v.val.property hvG, ?_⟩
  rw [← hPA]
  exact Q.le_normalizer_map A.subtype (Subgroup.mem_map_of_mem A.subtype v.property)

end CFSG.ShultStronglyClosedTI.CentralizerSylow
