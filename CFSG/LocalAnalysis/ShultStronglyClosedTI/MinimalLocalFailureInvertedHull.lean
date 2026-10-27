module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullAlgebra

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem invertedHull_full_stabilizer_supplement
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (hPodd : Odd (Nat.card P))
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1)
    (hescape : ¬ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H) :
    let A := minimalLocalFailureInvertedOvergroup P z
    let L := minimalLocalFailureInvertedHull P z
    ∃ X : Subgroup G, X ≤ H ⊓ L ∧ Odd (Nat.card X) ∧
      (X.subgroupOf (H ⊓ L)).Normal ∧
      (H ⊓ L : Set G) = (X : Set G) *
        (H ⊓ L ⊓ Subgroup.centralizer ({z} : Set G) : Set G) ∧
      ¬ Subgroup.normalizer (X : Set G) ⊓ L ≤ H ∧
      (H ⊓ A : Set G) = (A ⊓ Subgroup.centralizer ({z} : Set G) : Set G) * (X : Set G) ∧
      ⁅Subgroup.zpowers z, H ⊓ A⁆ ≤ X ∧
      (∀ a ∈ H ⊓ A, z⁻¹ * a⁻¹ * z * a ∈ X) := by
  let A := minimalLocalFailureInvertedOvergroup P z
  let L := minimalLocalFailureInvertedHull P z
  let K := H ⊓ L
  let C := H ⊓ L ⊓ Subgroup.centralizer ({z} : Set G)
  let D := A ⊓ Subgroup.centralizer ({z} : Set G)
  have hzL : z ∈ L := invertedHull_distinguished_mem P z
  have hstrong := invertedHull_strong_embedding h P hPodd hI hescape
  obtain ⟨_, _, _, _, _, _, hsolvable⟩ := invertedHull_odd_core_structure h P hPodd hI hescape
  let : Group.IsSolvable L := hsolvable
  obtain ⟨X, hXK, hXodd, hXnormal, hKproduct, hXescape⟩ :=
    invertedHull_ambient_solvable_supplement L H hstrong z hzL
      h.local_datum.distinguished_mem h.local_datum.distinguished_order
  let : (X.subgroupOf K).Normal := hXnormal
  have hreverse : (K : Set G) = (C : Set G) * (X : Set G) :=
    invertedHull_normal_supplement_reverse K X C hXK inf_le_left hKproduct
  have hLA : L ≤ A := by
    let zA : A := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
    exact Subgroup.map_subtype_le (involutionPointHull zA)
  have hCD : C ≤ D := le_inf (inf_le_left.trans (inf_le_right.trans hLA)) inf_le_right
  have hDK : D ≤ H ⊓ A := by
    intro d hd
    have hdH : d ∈ H := by
      have heq := invertedHull_point_intersection_product h P hescape
      change (H ⊓ A : Set G) = (D : Set G) * (K : Set G) at heq
      have hm : d ∈ (D : Set G) * (K : Set G) := Set.mem_mul.mpr
        ⟨d, hd, 1, K.one_mem, mul_one d⟩
      rw [← heq] at hm
      exact hm.1
    exact ⟨hdH, hd.1⟩
  have hfull : (H ⊓ A : Set G) = (D : Set G) * (X : Set G) := by
    ext a
    constructor
    · intro ha
      have ha' : a ∈ (H ⊓ A : Set G) := ha
      rw [invertedHull_point_intersection_product h P hescape] at ha'
      obtain ⟨d, hd, k, hk, hdk⟩ := ha'
      have hk' : k ∈ (K : Set G) := hk
      rw [hreverse] at hk'
      obtain ⟨c, hc, x, hx, hcx⟩ := hk'
      change c * x = k at hcx
      change d * k = a at hdk
      refine Set.mem_mul.mpr ⟨d * c, D.mul_mem hd (hCD hc), x, hx, ?_⟩
      rw [mul_assoc, hcx, hdk]
    · rintro ⟨d, hd, x, hx, rfl⟩
      exact (H ⊓ A).mul_mem (hDK hd) ⟨(hXK hx).1, hLA (hXK hx).2⟩
  have hzK : z ∈ K := ⟨h.local_datum.distinguished_mem, hzL⟩
  have hzX : z ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mp hXnormal hzK
  obtain ⟨hcomm, hright⟩ := invertedHull_stabilizer_commutators z
    h.local_datum.distinguished_order (H ⊓ A) X D hzX inf_le_right hfull
  exact ⟨X, hXK, hXodd, hXnormal, hKproduct, hXescape, hfull, hcomm, hright⟩

theorem minimal_local_embedding_inverted_set_solvable_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (_hPH : P ≤ H) (hPodd : Odd (Nat.card P))
    (_hPz : CFSG.conjugate P z = P)
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1)
    (hescape : ¬ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H) :
    let I := minimalLocalFailureInvertedSet P z
    let M := Subgroup.centralizer I
    let A := minimalLocalFailureInvertedOvergroup P z
    let L := minimalLocalFailureInvertedHull P z
    let V := L ⊓ M
    (M.subgroupOf A).Normal ∧ (M.subgroupOf A).index = 2 ∧ A ≠ ⊤ ∧
      fusionStronglyEmbedded (H.subgroupOf L) ∧
      (V.subgroupOf L).Normal ∧ Odd (Nat.card V) ∧ V.relIndex L = 2 ∧
      V = (oddCore L).map L.subtype ∧ L = V ⊔ Subgroup.zpowers z ∧
      (L : Set G) = (V : Set G) * (Subgroup.zpowers z : Set G) ∧
      Group.IsSolvable L ∧
      (∃ X : Subgroup G, X ≤ H ⊓ L ∧ Odd (Nat.card X) ∧
        (X.subgroupOf (H ⊓ L)).Normal ∧
        (H ⊓ L : Set G) = (X : Set G) *
          (H ⊓ L ⊓ Subgroup.centralizer ({z} : Set G) : Set G) ∧
        ¬ Subgroup.normalizer (X : Set G) ⊓ L ≤ H ∧
        (H ⊓ A : Set G) = (A ⊓ Subgroup.centralizer ({z} : Set G) : Set G) * (X : Set G) ∧
        ⁅Subgroup.zpowers z, H ⊓ A⁆ ≤ X ∧
        (∀ a ∈ H ⊓ A, z⁻¹ * a⁻¹ * z * a ∈ X)) ∧
      A ≤ Subgroup.normalizer I ∧
      (∀ a ∈ A, ∀ x ∈ I, rightConjugateElem x (rightConjugateElem z a) = x⁻¹) ∧
      (∀ t ∈ A.subtype '' involutionPointClass
        (⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩ : A),
        ∀ x ∈ I, rightConjugateElem x t = x⁻¹) := by
  have hz := h.local_datum.distinguished_order
  obtain ⟨hVnormal, hVodd, hVindex, hcore, hsup, hproduct, hsolvable⟩ :=
    invertedHull_odd_core_structure h P hPodd hI hescape
  refine ⟨invertedHull_centralizer_normal P z hz,
    invertedHull_centralizer_index_two P hPodd z hz hI,
    invertedHull_overgroup_proper h P hPodd hI,
    invertedHull_strong_embedding h P hPodd hI hescape,
    hVnormal, hVodd, hVindex, hcore, hsup, hproduct, hsolvable,
    invertedHull_full_stabilizer_supplement h P hPodd hI hescape,
    invertedHull_overgroup_normalizes_set P z hz, ?_, ?_⟩
  · intro a ha x hx
    exact invertedHull_conjugates_invert_set P z hz a ha x hx
  · rintro t ⟨tA, ⟨a, rfl⟩, rfl⟩ x hx
    exact invertedHull_conjugates_invert_set P z hz a a.property x hx

end CFSG.ShultStronglyClosedTI
