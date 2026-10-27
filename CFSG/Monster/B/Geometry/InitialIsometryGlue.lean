module

public import CFSG.Monster.B.Geometry.InitialIsometryProduct

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}
  (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
include hδ hδ'

theorem dist_eq_of_mem_residues {c : C} {f : C → C'} {J K : Set ι}
    (hJ : ∀ x ∈ residue cs δ J c, ∀ y ∈ residue cs δ J c, δ' (f x) (f y) = δ x y)
    (hK : ∀ x ∈ residue cs δ K c, ∀ y ∈ residue cs δ K c, δ' (f x) (f y) = δ x y)
    {x y : C} (hx : x ∈ residue cs δ J c) (hy : y ∈ residue cs δ K c) :
    δ' (f x) (f y) = δ x y := by
  obtain ⟨q, hq⟩ := exists_isProjection hδ K c x
  have hqJ : q ∈ residue cs δ J c := hq.mem_residue_of_mem hδ hx
  obtain ⟨hmul, hlen⟩ := hq.gate hδ hy
  have h1 := hJ x hx q hqJ
  have h2 := hK q hq.1 y hy
  rw [dist_eq_mul_of_length_add hδ' (y := f q) (by rw [h1, h2, ← hmul, hlen]), h1, h2, hmul]

theorem dist_eq_of_isProjection {c d p : C} {f : C → C'} {J : Set ι}
    (hJ : ∀ x ∈ residue cs δ J c, ∀ y ∈ residue cs δ J c, δ' (f x) (f y) = δ x y)
    (hp : IsProjection cs δ (residue cs δ J c) d p) (hdp : δ' (f d) (f p) = δ d p)
    {y : C} (hy : y ∈ residue cs δ J c) : δ' (f d) (f y) = δ d y := by
  obtain ⟨hmul, hlen⟩ := hp.gate hδ hy
  have h2 := hJ p hp.1 y hy
  rw [dist_eq_mul_of_length_add hδ' (y := f p) (by rw [hdp, h2, ← hmul, hlen]), hdp, h2, hmul]

theorem isWeylIsometry_glue (P : Set ι → Prop) {c d : C} {c' d' : C'} {f : C → C'}
    (hbij : ∀ J, P J → Set.BijOn f (residue cs δ J c) (residue cs δ' J c'))
    (hdist : ∀ J, P J → ∀ x ∈ residue cs δ J c, ∀ y ∈ residue cs δ J c,
      δ' (f x) (f y) = δ x y)
    (hfd : f d = d')
    (hproj : ∀ J, P J → δ' d' (f (resProj cs δ J c d)) = δ d (resProj cs δ J c d)) :
    IsWeylIsometry δ δ' ((⋃ J, ⋃ (_ : P J), residue cs δ J c) ∪ {d})
      ((⋃ J, ⋃ (_ : P J), residue cs δ' J c') ∪ {d'}) f := by
  have hdp : ∀ J, P J → ∀ y ∈ residue cs δ J c, δ' (f d) (f y) = δ d y := fun J hJ y hy =>
    dist_eq_of_isProjection hδ hδ' (hdist J hJ) (isProjection_resProj hδ J c d)
      (by rw [hfd]; exact hproj J hJ) hy
  refine isWeylIsometry_of hδ hδ' ?_ ?_ ?_
  · rintro x (hx | hx)
    · obtain ⟨J, hJ, hxJ⟩ : ∃ J, P J ∧ x ∈ residue cs δ J c := by simpa using hx
      exact Or.inl (Set.mem_biUnion (x := J) hJ ((hbij J hJ).mapsTo hxJ))
    · rw [Set.mem_singleton_iff.mp hx, hfd]
      exact Or.inr rfl
  · rintro y (hy | hy)
    · obtain ⟨J, hJ, hyJ⟩ : ∃ J, P J ∧ y ∈ residue cs δ' J c' := by simpa using hy
      obtain ⟨x, hx, rfl⟩ := (hbij J hJ).surjOn hyJ
      exact ⟨x, Or.inl (Set.mem_biUnion (x := J) hJ hx), rfl⟩
    · exact ⟨d, Or.inr rfl, by rw [hfd, Set.mem_singleton_iff.mp hy]⟩
  · rintro x (hx | hx) y (hy | hy)
    · obtain ⟨J, hJ, hxJ⟩ : ∃ J, P J ∧ x ∈ residue cs δ J c := by simpa using hx
      obtain ⟨K, hK, hyK⟩ : ∃ K, P K ∧ y ∈ residue cs δ K c := by simpa using hy
      exact dist_eq_of_mem_residues hδ hδ' (hdist J hJ) (hdist K hK) hxJ hyK
    · obtain ⟨J, hJ, hxJ⟩ : ∃ J, P J ∧ x ∈ residue cs δ J c := by simpa using hx
      rw [Set.mem_singleton_iff.mp hy, dist_inv hδ', hdp J hJ x hxJ, ← dist_inv hδ]
    · obtain ⟨K, hK, hyK⟩ : ∃ K, P K ∧ y ∈ residue cs δ K c := by simpa using hy
      rw [Set.mem_singleton_iff.mp hx]
      exact hdp K hK y hyK
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy, hδ.eq_one_self,
        hδ'.eq_one_self]

theorem isWeylIsometry_foundation_glue {c d : C} {c' d' : C'} {f : C → C'}
    (hbij : ∀ J : Set ι, J.encard ≤ 2 → Set.BijOn f (residue cs δ J c) (residue cs δ' J c'))
    (hdist : ∀ J : Set ι, J.encard ≤ 2 → ∀ x ∈ residue cs δ J c, ∀ y ∈ residue cs δ J c,
      δ' (f x) (f y) = δ x y)
    (hfd : f d = d')
    (hproj : ∀ J : Set ι, J.encard ≤ 2 →
      δ' d' (f (resProj cs δ J c d)) = δ d (resProj cs δ J c d)) :
    IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d}) (foundation cs δ' 2 c' ∪ {d'}) f :=
  isWeylIsometry_glue hδ hδ' (fun J => J.encard ≤ ((2 : ℕ) : ℕ∞)) (fun J hJ => hbij J hJ)
    (fun J hJ => hdist J hJ) hfd (fun J hJ => hproj J hJ)

theorem isWeylIsometry_residueFoundation_glue (K : Set ι) {c d : C} {c' d' : C'} {f : C → C'}
    (hbij : ∀ J : Set ι, J ⊆ K → J.encard ≤ 2 →
      Set.BijOn f (residue cs δ J c) (residue cs δ' J c'))
    (hdist : ∀ J : Set ι, J ⊆ K → J.encard ≤ 2 → ∀ x ∈ residue cs δ J c,
      ∀ y ∈ residue cs δ J c, δ' (f x) (f y) = δ x y)
    (hfd : f d = d')
    (hproj : ∀ J : Set ι, J ⊆ K → J.encard ≤ 2 →
      δ' d' (f (resProj cs δ J c d)) = δ d (resProj cs δ J c d)) :
    IsWeylIsometry δ δ' (residueFoundation cs δ K c ∪ {d})
      (residueFoundation cs δ' K c' ∪ {d'}) f :=
  isWeylIsometry_glue hδ hδ' (fun J => J ⊆ K ∧ J.encard ≤ 2) (fun J hJ => hbij J hJ.1 hJ.2)
    (fun J hJ => hdist J hJ.1 hJ.2) hfd (fun J hJ => hproj J hJ.1 hJ.2)

end CFSG.Monster.B.Geometry
