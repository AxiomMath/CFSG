module

public import CFSG.RankThree.PartOne.KLC.Transport

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG
open CFSG.RankThree.PartOne.KLC (map_centralizer_singleton_mulEquiv')

variable {T G : Type} [Group T] [Group G]

theorem no_component_of_comm {X : Subgroup T} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    {D : Subgroup T} (hD : IsComponentOf X D) : False := by
  obtain ⟨hle, hq, -⟩ := hD
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hX _ (hle a'.2) _ (hle b'.2))

theorem centralizer_comm_of_map {x : T} (φ : T ≃* G)
    (h : ∀ a ∈ Subgroup.centralizer ({φ x} : Set G), ∀ b ∈ Subgroup.centralizer ({φ x} : Set G),
      a * b = b * a) :
    ∀ a ∈ Subgroup.centralizer ({x} : Set T), ∀ b ∈ Subgroup.centralizer ({x} : Set T),
      a * b = b * a := by
  intro a ha b hb
  apply φ.injective
  rw [map_mul, map_mul]
  have h1 := map_centralizer_singleton_mulEquiv' φ x
  exact h _ (h1 ▸ Subgroup.mem_map_of_mem φ.toMonoidHom ha) _
    (h1 ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hb)

theorem normalizer_map_of_mem {x : T} {S : Subgroup T} (φ : T ≃* G)
    (hxS : x ∈ Subgroup.normalizer (S : Set T)) :
    φ x ∈ Subgroup.normalizer ((S.map φ.toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hxS ⊢
  intro h
  have e : φ x * h * (φ x)⁻¹ = φ (x * φ.symm h * x⁻¹) := by simp
  rw [e]
  have h1 : h ∈ S.map φ.toMonoidHom ↔ φ.symm h ∈ S := by
    rw [Subgroup.mem_map_equiv]
  have h2 : φ (x * φ.symm h * x⁻¹) ∈ S.map φ.toMonoidHom ↔ x * φ.symm h * x⁻¹ ∈ S := by
    rw [Subgroup.mem_map_equiv]
    simp
  rw [h1, h2]
  exact hxS _

end CFSG.RankThree.PartOne.TCX
