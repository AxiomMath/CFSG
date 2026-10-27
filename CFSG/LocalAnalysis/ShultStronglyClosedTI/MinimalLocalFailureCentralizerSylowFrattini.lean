module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem full_point_centralizer_normal
    (A X : Subgroup G) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ((A ⊓ Subgroup.centralizer (X : Set G)).subgroupOf A).Normal := by
  let C := Subgroup.centralizer (X : Set G)
  let Y := Subgroup.normalizer (X : Set G)
  have hCY : C ≤ Y := Subgroup.centralizer_le_normalizer _
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCY).mp
      (inferInstance : (C.subgroupOf Y).Normal)
  have hAC : A ≤ Subgroup.normalizer (A ⊓ C : Set G) :=
    (le_inf A.le_normalizer (hAX.trans hYC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact Subgroup.normal_subgroupOf_of_le_normalizer hAC

theorem full_point_centralizer_odd
    (A X : Subgroup G) (hA : CFSG.BenderSuzuki.IsStronglyEmbedded A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G)) :
    Odd (Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  let D := A ⊓ Subgroup.centralizer (X : Set G)
  let DA := D.subgroupOf A
  let : DA.Normal := full_point_centralizer_normal A X hAX
  by_contra hnot
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := D) 2
    (Nat.not_odd_iff_even.mp hnot).two_dvd
  have hvG : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hv
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  have hvI : IsInvolution (v : G) :=
    ⟨(orderOf_eq_prime_iff.mp hvG).2, (orderOf_eq_prime_iff.mp hvG).1⟩
  obtain ⟨a, ha, hconj⟩ := hA.involutions_conjugate_in hzA hzI v.property.1 hvI
  let aA : A := ⟨a, ha⟩
  let vA : A := ⟨v.val, v.property.1⟩
  have hvDA : vA ∈ DA := v.property
  have hzDA : (⟨z, hzA⟩ : A) ∈ DA := by
    have hh := (inferInstance : DA.Normal).conj_mem vA hvDA aA
    have heq : aA * vA * aA⁻¹ = (⟨z, hzA⟩ : A) := by
      apply Subtype.ext
      change a * (v : G) * a⁻¹ = z
      rw [← hconj]
      simp only [rightConjugateElem]
      group
    rwa [heq] at hh
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := hzDA.2
  apply hnoncentral
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hzC x hx)

theorem odd_normal_sylow_normalizer_even
    (D : Subgroup G) [D.Normal] (hDodd : Odd (Nat.card D))
    (heven : Even (Nat.card G)) (p : ℕ) (hp : p.Prime) (P : Sylow p D) :
    Even (Nat.card (Subgroup.normalizer
      (((P : Subgroup D).map D.subtype : Subgroup G) : Set G))) := by
  let : Fact p.Prime := ⟨hp⟩
  let N := Subgroup.normalizer (((P : Subgroup D).map D.subtype : Subgroup G) : Set G)
  have hgen : D ⊔ N = ⊤ := by
    rw [sup_comm]
    exact P.normalizer_sup_eq_top
  have hindexodd : Odd N.index := hDodd.of_dvd_nat (by
    rw [← Subgroup.relIndex_top_right N, ← hgen, sup_comm D N,
      LocalTheta.normal_factor_relative_index D N]
    exact N.relIndex_dvd_card D)
  apply Nat.not_odd_iff_even.mp
  intro hNodd
  have hGodd : Odd (Nat.card G) := by
    rw [← N.card_mul_index]
    exact hNodd.mul hindexodd
  exact (Nat.not_even_iff_odd.mpr hGodd) heven

theorem odd_point_centralizer_sylow_class_normalizer
    (A X : Subgroup G) (hA : CFSG.BenderSuzuki.IsStronglyEmbedded A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G))
    (p : ℕ) (hp : p.Prime)
    (P : Sylow p (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :
    (conjugacyWithin A z ∩ (Subgroup.normalizer
      (((P : Subgroup (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)).map
        (A ⊓ Subgroup.centralizer (X : Set G)).subtype : Subgroup G) : Set G) : Set G)).Nonempty := by
  let : Fact p.Prime := ⟨hp⟩
  let D := A ⊓ Subgroup.centralizer (X : Set G)
  let DA := D.subgroupOf A
  let : DA.Normal := full_point_centralizer_normal A X hAX
  have hDodd : Odd (Nat.card D) := full_point_centralizer_odd A X hA hAX z hzA hz hnoncentral
  have hDAodd : Odd (Nat.card DA) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ≤ A)).toEquiv]
    exact hDodd
  let e : D ≃* DA := (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ≤ A)).symm
  have he : Function.Surjective e.toMonoidHom := e.surjective
  let PA : Sylow p DA := P.mapSurjective (f := e.toMonoidHom) he
  let Q := (PA : Subgroup DA).map DA.subtype
  have hQA : Q.map A.subtype = (P : Subgroup D).map D.subtype := by
    change ((PA : Subgroup DA).map DA.subtype).map A.subtype = _
    dsimp only [PA]
    rw [Subgroup.map_map, Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : (A.subtype.comp DA.subtype).comp e.toMonoidHom = D.subtype := by
      ext x
      rfl
    rw [hcomp]
  let N := Subgroup.normalizer (Q : Set A)
  have hNeven : Even (Nat.card N) :=
    odd_normal_sylow_normalizer_even DA hDAodd hA.card_even p hp PA
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hNeven.two_dvd
  have hvA : orderOf (v.val : A) = 2 := (Subgroup.orderOf_coe v).trans hv
  have hvG : orderOf (v.val.val : G) = 2 := (Subgroup.orderOf_coe v.val).trans hvA
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  have hvI : IsInvolution (v.val.val : G) :=
    ⟨(orderOf_eq_prime_iff.mp hvG).2, (orderOf_eq_prime_iff.mp hvG).1⟩
  obtain ⟨a, ha, hconj⟩ := hA.involutions_conjugate_in hzA hzI v.val.property hvI
  refine ⟨v.val.val, ⟨⟨⟨a, ha⟩, hconj⟩, ?_⟩⟩
  rw [← hQA]
  exact Q.le_normalizer_map A.subtype (Subgroup.mem_map_of_mem A.subtype v.property)

end CFSG.ShultStronglyClosedTI.CentralizerSylow
