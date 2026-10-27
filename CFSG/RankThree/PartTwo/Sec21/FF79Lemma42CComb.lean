module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem typed_sets (R : Set G) (P Q : G → Prop) (S₁ S₂ : Finset G)
    (hcover : ∀ x ∈ R, x ≠ 1 → P x ∨ Q x)
    (hP4 : {x | x ∈ R ∧ x ≠ 1 ∧ P x}.ncard = 4) (hQ4 : {x | x ∈ R ∧ x ≠ 1 ∧ Q x}.ncard = 4)
    (h1 : S₁.card = 4) (h2 : S₂.card = 4)
    (hS₁ : ∀ x ∈ S₁, x ∈ R ∧ x ≠ 1 ∧ P x)
    (hS₂ : ∀ x ∈ S₂, x ∈ R ∧ x ≠ 1 ∧ x ∉ S₁) :
    (∀ x, (x ∈ R ∧ x ≠ 1 ∧ P x) ↔ x ∈ S₁) ∧ (∀ x, (x ∈ R ∧ x ≠ 1 ∧ Q x) ↔ x ∈ S₂) := by
  have e1 : (↑S₁ : Set G) = {x | x ∈ R ∧ x ≠ 1 ∧ P x} :=
    Set.eq_of_subset_of_ncard_le (fun x hx => hS₁ x hx)
      (by rw [hP4, Set.ncard_coe_finset, h1]) (Set.finite_of_ncard_pos (by omega))
  have hP : ∀ x, (x ∈ R ∧ x ≠ 1 ∧ P x) ↔ x ∈ S₁ := fun x => by
    have := Set.ext_iff.mp e1 x
    simp only [Set.mem_setOf_eq, Finset.mem_coe] at this
    exact this.symm
  refine ⟨hP, ?_⟩
  have e2 : (↑S₂ : Set G) = {x | x ∈ R ∧ x ≠ 1 ∧ Q x} := by
    refine Set.eq_of_subset_of_ncard_le (fun x hx => ?_)
      (by rw [hQ4, Set.ncard_coe_finset, h2]) (Set.finite_of_ncard_pos (by omega))
    obtain ⟨hxR, hx1, hxS⟩ := hS₂ x hx
    refine ⟨hxR, hx1, ?_⟩
    rcases hcover x hxR hx1 with hp | hq
    · exact absurd ((hP x).mp ⟨hxR, hx1, hp⟩) hxS
    · exact hq
  intro x
  have := Set.ext_iff.mp e2 x
  simp only [Set.mem_setOf_eq, Finset.mem_coe] at this
  exact this.symm

@[expose] def cs₁ : Finset (ℤ × ℤ × ℤ) := {(0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)}

@[expose] def cs₂ : Finset (ℤ × ℤ × ℤ) := {(0, 1, 1), (0, -1, -1), (0, 2, 1), (0, -2, -1)}

namespace BGen

variable [Finite G] {b b₁ b₂ : G} {B : Subgroup G} (hB : BGen b b₁ b₂ B)
include hB

theorem crd_neg (p : ℤ × ℤ × ℤ) : (crd b b₁ b₂ p)⁻¹ = crd b b₁ b₂ (-p) := by
  have : crd b b₁ b₂ p * crd b b₁ b₂ (-p) = 1 := by
    rw [hB.crd_mul, ← hB.crd_zero]
    congr 1
    simp
    rfl
  exact inv_eq_of_mul_eq_one_right this

theorem injOn_cs :
    Set.InjOn (crd b b₁ b₂) (↑(cs₁ ∪ cs₂) : Set (ℤ × ℤ × ℤ)) := by
  intro p hp q hq h
  have := hB.crd_eq h
  simp only [cs₁, cs₂, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
  rcases hq with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
  first | rfl | (exfalso; simp only at this; omega)

end BGen

end CFSG.RankThree.PartTwo.Sec21.FF79
