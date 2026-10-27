module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowExtension

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalIntersection_join_quotient_surjective
    (C E : Subgroup G) (hC : (C.subgroupOf (C ⊔ E)).Normal) :
    Function.Surjective ((QuotientGroup.mk' (C.subgroupOf (C ⊔ E))).domRestrict
      (E.subgroupOf (C ⊔ E))) := by
  let D := C ⊔ E
  let CD := C.subgroupOf D
  let ED := E.subgroupOf D
  let _ : CD.Normal := hC
  let q := QuotientGroup.mk' CD
  intro a
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective CD a
  have hd : d ∈ CD ⊔ ED := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact d.property
  obtain ⟨c, hc, e, he, hce⟩ := Subgroup.mem_sup_of_normal_left.mp hd
  let e₀ : ED := ⟨e, he⟩
  have hqc : q c = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [QuotientGroup.ker_mk']
    exact hc
  refine ⟨e₀, ?_⟩
  change q e = q d
  rw [← hce, map_mul, hqc, one_mul]

theorem normalIntersection_triple_sylow_intersection
    (p : ℕ) (hp : p.Prime) (C E : Subgroup G)
    (hC : E ≤ Subgroup.normalizer (C : Set G))
    (Q : Sylow p (C ⊓ E : Subgroup G)) (A : Sylow p E)
    (hQA : (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype ≤
      (A : Subgroup E).map E.subtype) :
    (A : Subgroup E).map E.subtype ⊓ C =
      (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype := by
  let CE := C.subgroupOf E
  let _ : CE.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hC
  have hCE : CE.map E.subtype = C ⊓ E := Subgroup.subgroupOf_map_subtype C E
  have hfull := noncentralSylow_normal_intersection_eq_of_containment
    p hp E CE
  rw [hCE] at hfull
  have hinter := hfull Q A hQA
  have hAE : (A : Subgroup E).map E.subtype ≤ E := Subgroup.map_subtype_le _
  calc
    (A : Subgroup E).map E.subtype ⊓ C =
        (A : Subgroup E).map E.subtype ⊓ (C ⊓ E) := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2, hAE hx.1⟩,
        fun hx => ⟨hx.1, hx.2.1⟩⟩
    _ = (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype := hinter

theorem normalIntersection_join_sylow_deficiency
    (p : ℕ) (hp : p.Prime) (C E : Subgroup G)
    (hC : (C ⊔ E) ≤ Subgroup.normalizer (C : Set G))
    (Q : Sylow p (C ⊓ E : Subgroup G)) (A : Sylow p E)
    (hQA : (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype ≤
      (A : Subgroup E).map E.subtype)
    (hdeficient : ¬ ∃ R : Sylow p C,
      (R : Subgroup C).map C.subtype =
        (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype) :
    ¬ ∃ T : Sylow p (C ⊔ E : Subgroup G),
      (T : Subgroup (C ⊔ E : Subgroup G)).map (C ⊔ E).subtype =
        (A : Subgroup E).map E.subtype := by
  let D := C ⊔ E
  let CD := C.subgroupOf D
  let _ : CD.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hC
  have hCD : CD.map D.subtype = C :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hinter := normalIntersection_triple_sylow_intersection
    p hp C E (le_sup_right.trans hC) Q A hQA
  rintro ⟨T, hT⟩
  have hexists := normal_subgroup_image_sylow_intersection p hp D CD T
  rw [hCD] at hexists
  obtain ⟨R, hR⟩ := hexists
  apply hdeficient
  refine ⟨R, ?_⟩
  exact hR.trans (hT ▸ hinter)

end CFSG.ShultStronglyClosedTI
