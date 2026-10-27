module

public import CFSG.Sporadic.Co2Smith.ClassCount

public section

namespace CFSG.Sporadic.Co2Smith

variable {M : Type*} [Group M] [Finite M]

open Classical in
theorem classes_of_card {zM : M} {k : ℕ} (r : Fin k → M) (m : Fin k → ℕ)
    (hcard : Nat.card {y : M // y * y = 1} = 2 + ∑ i, m i)
    (hzz : zM * zM = 1) (hz1 : zM ≠ 1) (hzc : ∀ g : M, g * zM = zM * g)
    (hr : ∀ i, r i * r i = 1 ∧ r i ≠ 1 ∧ r i ≠ zM)
    (hm : ∀ i, m i ≤ (conjSet (r i)).ncard)
    (hdisj : ∀ i j, i ≠ j → ∀ h : M, h * r i * h⁻¹ ≠ r j) :
    (∀ y : M, y * y = 1 → y = 1 ∨ y = zM ∨ ∃ i, ∃ h : M, h * y * h⁻¹ = r i) ∧
      ∀ i, (conjSet (r i)).ncard = m i := by
  have := Fintype.ofFinite M
  set I : Finset M := Finset.univ.filter fun y => y * y = 1 ∧ y ≠ 1 ∧ y ≠ zM
  set S : Fin k → Finset M := fun i => Finset.univ.filter fun y => ∃ h : M, y = h * r i * h⁻¹
  have hS : ∀ i, (conjSet (r i)).ncard = (S i).card := fun i => by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp [S, conjSet]
  have hsub : ∀ i, S i ⊆ I := by
    intro i y hy
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨h1, h2, h3⟩ := hr i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun e => h2 ?_, fun e => h3 ?_⟩
    · rw [show h * r i * h⁻¹ * (h * r i * h⁻¹) = h * (r i * r i) * h⁻¹ by group, h1]
      group
    · calc r i = h⁻¹ * (h * r i * h⁻¹) * h := by group
        _ = 1 := by rw [e]; group
    · calc r i = h⁻¹ * (h * r i * h⁻¹) * h := by group
        _ = h⁻¹ * zM * h := by rw [e]
        _ = zM := by rw [mul_assoc, ← hzc h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdj : ∀ i ∈ (Finset.univ : Finset (Fin k)), ∀ j ∈ (Finset.univ : Finset (Fin k)),
      i ≠ j → Disjoint (S i) (S j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro y hyi hyj
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hyi).2
    obtain ⟨h', e⟩ := (Finset.mem_filter.mp hyj).2
    apply hdisj i j hij (h'⁻¹ * h)
    calc h'⁻¹ * h * r i * (h'⁻¹ * h)⁻¹ = h'⁻¹ * (h * r i * h⁻¹) * h' := by group
      _ = h'⁻¹ * (h' * r j * h'⁻¹) * h' := by rw [e]
      _ = r j := by group
  have hI : Nat.card {y : M // y * y = 1} = I.card + 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hset : (Finset.univ.filter fun y : M => y * y = 1) = I ∪ {1, zM} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, I,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hy
        by_cases h1 : y = 1
        · exact Or.inr (Or.inl h1)
        · by_cases h2 : y = zM
          · exact Or.inr (Or.inr h2)
          · exact Or.inl ⟨hy, h1, h2⟩
      · rintro (⟨hy, -, -⟩ | rfl | rfl)
        · exact hy
        · exact one_mul 1
        · exact hzz
    have hdisj' : Disjoint I {1, zM} := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨-, -, h1, h2⟩ := Finset.mem_filter.mp hy
      rcases Finset.mem_insert.mp hy' with rfl | hy'
      · exact h1 rfl
      · exact h2 (Finset.mem_singleton.mp hy')
    rw [hset, Finset.card_union_of_disjoint hdisj', Finset.card_pair hz1.symm]
  have hU : (Finset.univ.biUnion S).card = ∑ i, (S i).card := Finset.card_biUnion hdj
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin k)), m i ≤ (S i).card :=
    fun i _ => (hS i) ▸ hm i
  have hsubU : Finset.univ.biUnion S ⊆ I := Finset.biUnion_subset.mpr fun i _ => hsub i
  have hcardU := Finset.card_le_card hsubU
  have hsum := Finset.sum_le_sum hle
  have heq : Finset.univ.biUnion S = I := Finset.eq_of_subset_of_card_le hsubU (by omega)
  have hsum' : ∑ i, m i = ∑ i, (S i).card := by omega
  have heach := (Finset.sum_eq_sum_iff_of_le hle).mp hsum'
  refine ⟨fun y hy => ?_, fun i => (hS i).trans (heach i (Finset.mem_univ _)).symm⟩
  by_cases h1 : y = 1
  · exact Or.inl h1
  by_cases h2 : y = zM
  · exact Or.inr (Or.inl h2)
  have hyI : y ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, h1, h2⟩
  rw [← heq, Finset.mem_biUnion] at hyI
  obtain ⟨i, -, hi⟩ := hyI
  obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hi).2
  exact Or.inr (Or.inr ⟨i, h⁻¹, by group⟩)

end CFSG.Sporadic.Co2Smith
