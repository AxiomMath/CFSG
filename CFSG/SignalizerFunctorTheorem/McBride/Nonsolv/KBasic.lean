module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G] [Finite G]

theorem kOf_map_mulEquiv (e : G ≃* G) (X : Subgroup G) :
    kOf (X.map (e : G →* G)) = (kOf X).map (e : G →* G) := by
  have h1 : (oStar ↥X).map (e.subgroupMap X).toMonoidHom = oStar ↥(X.map (e : G →* G)) :=
    oStar_map_mulEquiv _
  have hcomp : (X.map (e : G →* G)).subtype.comp (e.subgroupMap X).toMonoidHom =
      (e : G →* G).comp X.subtype := by
    ext x
    rfl
  calc kOf (X.map (e : G →* G))
      = ((oStar ↥X).map (e.subgroupMap X).toMonoidHom).map (X.map (e : G →* G)).subtype := by
        rw [h1]
        rfl
    _ = (oStar ↥X).map ((X.map (e : G →* G)).subtype.comp (e.subgroupMap X).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (oStar ↥X).map ((e : G →* G).comp X.subtype) := by rw [hcomp]
    _ = (kOf X).map (e : G →* G) := by
        rw [← Subgroup.map_map]
        rfl

theorem conj_mem_kOf {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {x : G} (hx : x ∈ kOf X) : g * x * g⁻¹ ∈ kOf X := by
  have hmap : X.map ((MulAut.conj g : G ≃* G) : G →* G) = X := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy
  have h1 := kOf_map_mulEquiv (MulAut.conj g) X
  rw [hmap] at h1
  rw [h1]
  exact ⟨x, hx, rfl⟩

theorem mem_normalizer_kOf_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : g ∈ Subgroup.normalizer (kOf X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_kOf hg hx, fun hx => ?_⟩
  simpa [mul_assoc] using conj_mem_kOf (inv_mem hg) hx

theorem le_normalizer_kOf_of_le_normalizer {B X : Subgroup G}
    (h : B ≤ Subgroup.normalizer (X : Set G)) : B ≤ Subgroup.normalizer (kOf X : Set G) :=
  fun _ hg => mem_normalizer_kOf_of_mem_normalizer (h hg)

theorem le_normalizer_kOf (X : Subgroup G) : X ≤ Subgroup.normalizer (kOf X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (kOf_le X)).mp (normal_kOf_subgroupOf X)

theorem kOf_eq_bot_iff (X : Subgroup G) : kOf X = ⊥ ↔ X = ⊥ := by
  constructor
  · intro h
    have hsol : sol X = ⊥ := le_bot_iff.mp (h ▸ sol_le_kOf X)
    have h2 := centralizer_kOf_eq_bot hsol
    have h3 : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr fun x hx => by
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
        rw [hx]
        exact one_mem _
    rwa [h, h3, inf_top_eq] at h2
  · rintro rfl
    exact le_bot_iff.mp (kOf_le ⊥)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
