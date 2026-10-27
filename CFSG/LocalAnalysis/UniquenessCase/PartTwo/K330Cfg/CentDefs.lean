module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Equiv.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

@[expose] def E9C7Rel {G : Type*} [Group G] (a b r : G) : Prop :=
  a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 ∧ a * b ^ 2 ≠ 1 ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ r ≠ 1 ∧ r ^ 7 = 1 ∧
    a * b = b * a ∧ a * r = r * a ∧ b * r = r * b

@[expose] def E9C7Free (G : Type*) [Group G] : Prop := ∀ a b r : G, ¬ E9C7Rel a b r

theorem E9C7Rel.map {G G' : Type*} [Group G] [Group G'] (f : G →* G') (hf : Function.Injective f)
    {a b r : G} (h : E9C7Rel a b r) : E9C7Rel (f a) (f b) (f r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [Ne, ← map_one f, hf.eq_iff]
  · rwa [Ne, ← map_one f, hf.eq_iff]
  · rwa [Ne, ← map_mul, ← map_one f, hf.eq_iff]
  · rwa [Ne, ← map_pow, ← map_mul, ← map_one f, hf.eq_iff]
  · rw [← map_pow, h5, map_one]
  · rw [← map_pow, h6, map_one]
  · rwa [Ne, ← map_one f, hf.eq_iff]
  · rw [← map_pow, h8, map_one]
  · rw [← map_mul, ← map_mul, h9]
  · rw [← map_mul, ← map_mul, h10]
  · rw [← map_mul, ← map_mul, h11]

theorem e9c7Free_of_injective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (h : E9C7Free G') : E9C7Free G :=
  fun a b r hrel => h (f a) (f b) (f r) (hrel.map f hf)

theorem e9c7Free_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : E9C7Free G') : E9C7Free G :=
  e9c7Free_of_injective e.toMonoidHom e.injective h

theorem e9c7Free_subgroup {G : Type*} [Group G] (H : Subgroup G) (h : E9C7Free G) :
    E9C7Free ↥H :=
  e9c7Free_of_injective H.subtype H.subtype_injective h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
