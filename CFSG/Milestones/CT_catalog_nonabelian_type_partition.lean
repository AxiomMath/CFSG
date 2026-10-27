module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint

open Assembly.LowTwoRank

theorem suzukiModel_admissible {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    StatedLieAdmissible .twistedB2 0 p f := by
  obtain ⟨rfl, a, ha, -, -, -, rfl, -, -⟩ := h
  exact ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩

theorem oddLieType_or_evenLieType_of_lieModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (h : LieModel X t n p f) :
    OddLieType X ∨ EvenLieType X := by
  by_cases hp : p = 2
  · subst hp
    exact .inr ⟨t, n, f, hadm, h⟩
  · exact .inl ⟨t, n, p, f, hadm.1, hp, hadm, h⟩

end CFSG.Blueprint

namespace CFSG.Milestones

open Blueprint Assembly.LowTwoRank

private theorem not_nonabelian_of_mulEquiv_zmod {X : Type} [Group X] {p : ℕ}
    (e : X ≃* Multiplicative (ZMod p)) (hnonab : ∃ a b : X, a * b ≠ b * a) : False := by
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))

theorem ct_catalog_nonabelian_type_partition_converse (X : Type) [Group X]
    (h : (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      OddLieType X ∨ EvenLieType X ∨ NativeSporadic.SporadicRep X) : Catalog X := by
  rcases h with hA | ⟨t, n, p, f, -, -, -, h⟩ | ⟨t, n, f, -, h⟩ | hS
  · exact .inr (.inl hA)
  · exact lieModel_catalog X t n p f h
  · exact lieModel_catalog X t n 2 f h
  · exact .inr (.inr (.inr (.inr hS)))

theorem ct_catalog_nonabelian_type_partition (X : Type) [Group X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) :
    Catalog X ↔
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
        OddLieType X ∨ EvenLieType X ∨ NativeSporadic.SporadicRep X := by
  refine ⟨fun hX => ?_, ct_catalog_nonabelian_type_partition_converse X⟩
  have lie : ∀ {t : StatedLieTag} {n p f : ℕ}, StatedLieAdmissible t n p f →
      LieModel X t n p f →
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
        OddLieType X ∨ EvenLieType X ∨ NativeSporadic.SporadicRep X := fun hadm h =>
    (oddLieType_or_evenLieType_of_lieModel hadm h).elim (fun h => .inr (.inl h))
      (fun h => .inr (.inr (.inl h)))
  rcases hX with ⟨p, -, ⟨e⟩⟩ | hA | ⟨t, n, p, f, h⟩ | hE | hS
  · exact (not_nonabelian_of_mulEquiv_zmod e hnonab).elim
  · exact .inl hA
  · have ht : t ∈ classicalTags := by
      obtain ⟨-, h⟩ := h
      cases t <;> first | exact h.elim | decide
    exact lie h.1 (.inl ⟨ht, h⟩)
  · rcases hE with ⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩
    · exact lie h.1 (.inr (.inl ⟨rfl, ht, h⟩))
    · exact lie h.1 (.inr (.inr (.inl ⟨rfl, ht, h⟩)))
    · exact lie (suzukiModel_admissible h) (.inr (.inr (.inr ⟨rfl, rfl, h⟩)))
  · exact .inr (.inr (.inr hS))

end CFSG.Milestones
