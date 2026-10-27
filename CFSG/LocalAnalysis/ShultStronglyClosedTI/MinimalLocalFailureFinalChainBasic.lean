module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupSylow
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairModelAlignment

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G]

theorem localHull_map_conj (z u g : G) :
    (Subgroup.closure (involutionPointClass z ∩
        (Subgroup.centralizer ({u} : Set G) : Set G))).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.closure (involutionPointClass z ∩
        (Subgroup.centralizer ({g⁻¹ * u * g} : Set G) : Set G)) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_inter_iff, SetLike.mem_coe,
    Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  constructor
  · rintro ⟨y, ⟨hyD, hyu⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [rightConjugateElem] using pointClass_right_conjugate_mem hyD g
    · calc g⁻¹ * y * g * (g⁻¹ * u * g) = g⁻¹ * (y * u) * g := by group
        _ = g⁻¹ * (u * y) * g := by rw [hyu]
        _ = g⁻¹ * u * g * (g⁻¹ * y * g) := by group
  · rintro ⟨hxD, hxu⟩
    refine ⟨g * x * g⁻¹, ⟨?_, ?_⟩, by group⟩
    · have := pointClass_right_conjugate_mem hxD g⁻¹
      simpa only [rightConjugateElem, inv_inv] using this
    · calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * u * g * x) * g⁻¹ := by rw [hxu]
        _ = u * (g * x * g⁻¹) := by group

theorem mem_normalizer_of_localHull_eq {z j k g : G} {K : Subgroup G}
    (hj : Subgroup.closure (involutionPointClass z ∩
      (Subgroup.centralizer ({j} : Set G) : Set G)) = K)
    (hk : Subgroup.closure (involutionPointClass z ∩
      (Subgroup.centralizer ({k} : Set G) : Set G)) = K)
    (hjk : g⁻¹ * j * g = k) : g ∈ Subgroup.normalizer (K : Set G) := by
  have hmap : K.map (MulAut.conj g⁻¹).toMonoidHom = K := by
    have h0 := localHull_map_conj z j g
    rw [hj, hjk, hk] at h0
    exact h0
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hy := Subgroup.mem_map_equiv (f := MulAut.conj g⁻¹) (K := K) (x := y)
  rw [hmap, MulAut.conj_symm_apply, inv_inv] at hy
  exact hy

theorem centralizer_le_normalizer_of_localHull_eq {z u : G} {K : Subgroup G}
    (hu : Subgroup.closure (involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G)) = K) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  apply mem_normalizer_of_localHull_eq hu hu
  rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hg, inv_mul_cancel_left]

theorem exists_mul_of_mem_sup {H Q B : Subgroup G} (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal)
    (hBH : B ≤ H) {x : G} (hx : x ∈ Q ⊔ B) : ∃ y ∈ Q, ∃ b ∈ B, y * b = x := by
  have hmap : (Q.subgroupOf H ⊔ B.subgroupOf H).map H.subtype = Q ⊔ B := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQH, inf_eq_left.mpr hBH]
  rw [← hmap] at hx
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
  have hw' : w ∈ ((Q.subgroupOf H ⊔ B.subgroupOf H : Subgroup H) : Set H) := hw
  rw [Subgroup.normal_mul] at hw'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hw'
  exact ⟨y, hy, b, hb, rfl⟩

theorem card_conjugacyWithin_mul [Finite G] {H : Subgroup G} {j : G} (hj : j ∈ H) :
    Nat.card (conjugacyWithin H j) * Nat.card (H ⊓ Subgroup.centralizer ({j} : Set G) :
      Subgroup G) = Nat.card H := by
  have h1 := conjugacy_class_card_mul_centralizer (⟨j, hj⟩ : H)
  rw [Nat.card_congr (conjugacyWithinEquiv H ⟨j, hj⟩)] at h1
  rw [← h1]
  congr 1
  have hmap : (Subgroup.centralizer ({⟨j, hj⟩} : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({j} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hxH, hx⟩
      exact ⟨⟨x, hxH⟩, Subtype.ext hx, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective]

theorem psl2_two_subgroup_elemAbelian {k : Type} [Field k] [Finite k] {f : ℕ}
    (hcard : Nat.card k = 2 ^ f) {P : Subgroup (PSL2MatrixGroup k)} (hP : IsPGroup 2 P) :
    (∀ x ∈ P, x ^ 2 = 1) ∧ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP k 2 := LinearModel.charP_two_of_card hcard
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := LinearModel.exists_sylow_eq_conj_rootGroup hcard S
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hx' : x ∈ (CFSG.GorensteinWalter.psl2UpperUnipotentSubgroup k).map
        (MulAut.conj g).toMonoidHom := hg ▸ hPS hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx'
    by_cases h1 : x₀ = 1
    · rw [h1, map_one, one_pow]
    · have h2 := LinearModel.orderOf_eq_two_of_mem_rootGroup hx₀ h1
      have h3 : x₀ ^ 2 = 1 := (orderOf_eq_prime_iff.mp h2).1
      rw [← map_pow, h3, map_one]
  · by_cases h1 : x = 1
    · rw [h1, one_mul, mul_one]
    · have hC := LinearModel.sylow_centralizer_eq hcard S (hPS hx) h1
      have hyC : y ∈ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup k)) := hC ▸ hPS hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm

theorem isElemAbelian_of_injective_psl2 {k : Type} [Field k] [Finite k] {f : ℕ}
    (hcard : Nat.card k = 2 ^ f) {J : Subgroup G} (hJ : IsPGroup 2 J) {L : Type*} [Group L]
    (e : L ≃* PSL2MatrixGroup k) (φ : J →* L) (hφ : Function.Injective φ) :
    IsElemAbelian 2 J := by
  let ψ : J →* PSL2MatrixGroup k := e.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := e.injective.comp hφ
  have hP : IsPGroup 2 ψ.range := hJ.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨hsq, hcomm⟩ := psl2_two_subgroup_elemAbelian hcard hP
  refine ⟨isMulCommutative_iff.mpr fun a b => hψ ?_, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact hcomm _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  · have h := hsq (ψ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    rw [← map_pow, ← map_one ψ] at h
    exact congrArg Subtype.val (hψ h)

end CFSG.ShultStronglyClosedTI.FinalChain
