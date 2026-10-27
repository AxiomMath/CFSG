module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CComb

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}

theorem types_main (h4 : FF79Sec4 b J B b₁ b₂) (R : Subgroup G) (hR1 : b₁ ∈ R) (hR2 : b₂ ∈ R)
    (P Q : G → Prop) (hcover : ∀ x ∈ R, x ≠ 1 → P x ∨ Q x)
    (hP4 : {x | x ∈ R ∧ x ≠ 1 ∧ P x}.ncard = 4) (hQ4 : {x | x ∈ R ∧ x ≠ 1 ∧ Q x}.ncard = 4)
    (hPinv : ∀ x, P x⁻¹ ↔ P x) (hP1 : P b₁) (hP2 : P b₂) :
    (∀ x ∈ R, x ≠ 1 → P x → x = b₁ ∨ x = b₁⁻¹ ∨ x = b₂ ∨ x = b₂⁻¹) ∧
    (∀ x ∈ R, x ≠ 1 → Q x →
      x = b₁ * b₂ ∨ x = (b₁ * b₂)⁻¹ ∨ x = b₁ ^ 2 * b₂ ∨ x = (b₁ ^ 2 * b₂)⁻¹) ∧
    Q (b₁ * b₂) := by
  classical
  have hB := bgen_of_sec4 h4
  set E := crd b b₁ b₂ with hE
  have hER : ∀ j k : ℤ, E (0, j, k) ∈ R := fun j k => by
    simp only [hE, crd, zpow_zero, one_mul]
    exact R.mul_mem (R.zpow_mem hR1 j) (R.zpow_mem hR2 k)
  have v1 : E (0, 1, 0) = b₁ := by simp [hE, crd]
  have v1' : E (0, -1, 0) = b₁⁻¹ := by simp [hE, crd]
  have v2 : E (0, 0, 1) = b₂ := by simp [hE, crd]
  have v2' : E (0, 0, -1) = b₂⁻¹ := by simp [hE, crd]
  have w1 : E (0, 1, 1) = b₁ * b₂ := by simp [hE, crd]
  have w2 : E (0, 2, 1) = b₁ ^ 2 * b₂ := by simp [hE, crd]
  have w1' : E (0, -1, -1) = (b₁ * b₂)⁻¹ := by
    rw [← w1, hB.crd_neg]; rfl
  have w2' : E (0, -2, -1) = (b₁ ^ 2 * b₂)⁻¹ := by
    rw [← w2, hB.crd_neg]; rfl
  have hne : ∀ p ∈ cs₁ ∪ cs₂, E p ≠ 1 := by
    intro p hp h
    have := hB.crd_eq (h.trans hB.crd_zero.symm)
    simp only [cs₁, cs₂, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
      (simp only at this; omega)
  have hPS₁ : ∀ p ∈ cs₁, P (E p) := by
    intro p hp
    simp only [cs₁, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [v1]; exact hP1
    · rw [v1']; exact (hPinv _).mpr hP1
    · rw [v2]; exact hP2
    · rw [v2']; exact (hPinv _).mpr hP2
  have c1 : (cs₁.image E).card = 4 := by
    rw [Finset.card_image_of_injOn (hB.injOn_cs.mono (by simp))]; decide
  have c2 : (cs₂.image E).card = 4 := by
    rw [Finset.card_image_of_injOn (hB.injOn_cs.mono (by simp))]; decide
  obtain ⟨hPset, hQset⟩ := typed_sets (R : Set G) P Q (cs₁.image E) (cs₂.image E) hcover hP4 hQ4
    c1 c2
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨?_, hne p (Finset.mem_union_left _ hp), hPS₁ p hp⟩
      simp only [cs₁, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact hER _ _)
    (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨?_, hne q (Finset.mem_union_right _ hq), ?_⟩
      · simp only [cs₂, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> exact hER _ _
      · intro hx1
        obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hx1
        have := hB.crd_eq hpq
        simp only [cs₁, cs₂, Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl <;> (simp only at this; omega))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hx1 hxP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ((hPset x).mp ⟨hx, hx1, hxP⟩)
    simp only [cs₁, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl v1
    · exact Or.inr (Or.inl v1')
    · exact Or.inr (Or.inr (Or.inl v2))
    · exact Or.inr (Or.inr (Or.inr v2'))
  · intro x hx hx1 hxQ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ((hQset x).mp ⟨hx, hx1, hxQ⟩)
    simp only [cs₂, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl w1
    · exact Or.inr (Or.inl w1')
    · exact Or.inr (Or.inr (Or.inl w2))
    · exact Or.inr (Or.inr (Or.inr w2'))
  · have hmem : b₁ * b₂ ∈ cs₂.image E :=
      Finset.mem_image.mpr ⟨(0, 1, 1), by simp [cs₂], w1⟩
    exact ((hQset _).mpr hmem).2.2

end CFSG.RankThree.PartTwo.Sec21.FF79
