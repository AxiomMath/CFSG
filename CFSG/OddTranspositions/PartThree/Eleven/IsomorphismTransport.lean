module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.OddTranspositions.PartThree

namespace IsoTransport

lemma conj_hom {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (r₀ : X) :
    ((MulAut.conj (e r₀)).toMonoidHom).comp e.toMonoidHom =
      e.toMonoidHom.comp ((MulAut.conj r₀).toMonoidHom) := by
  ext a
  simp [map_mul]

lemma conj_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (A : Subgroup X)
    (r₀ : X) :
    (A.map e.toMonoidHom).map (MulAut.conj (e r₀)).toMonoidHom =
      (A.map (MulAut.conj r₀).toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, conj_hom]

lemma conj_symm_image {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (B' : Set Y)
    (g : X) :
    e.symm '' ((fun y => e g * y * (e g)⁻¹) '' B') =
      (fun y => g * y * g⁻¹) '' (e.symm '' B') := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro y _
  simp [map_mul]

lemma aut_image {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (φ' : Y ≃* Y)
    (Θ : Set X) :
    ((e.trans φ').trans e.symm) '' Θ = e.symm '' (φ' '' (e '' Θ)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ' (e x), ⟨e x, ⟨x, hx, rfl⟩, rfl⟩, by simp⟩
  · rintro ⟨z, ⟨w, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp⟩

lemma map_commutator {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (commutator X).map e.toMonoidHom = commutator Y := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

end IsoTransport

end CFSG.OddTranspositions.PartThree
