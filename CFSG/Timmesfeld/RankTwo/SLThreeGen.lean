module

public import CFSG.Timmesfeld.RankTwo.SimplyLaced

public section

namespace CFSG.Timmesfeld

open Matrix
open scoped commutatorElement

private lemma tv_zero_two {F : Type*} [Field F] (c : F) :
    tv (n := 3) 0 2 c = ⁅tv (n := 3) 0 1 c, tv (n := 3) 1 2 (1 : F)⁆ := by
  rw [tv_of_ne (show (0 : Fin 3) ≠ 1 by decide) c,
    tv_of_ne (show (1 : Fin 3) ≠ 2 by decide) (1 : F),
    tv_of_ne (show (0 : Fin 3) ≠ 2 by decide) c,
    Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) c (1 : F),
    mul_one]

private lemma tv_two_zero {F : Type*} [Field F] (c : F) :
    tv (n := 3) 2 0 c = ⁅tv (n := 3) 2 1 c, tv (n := 3) 1 0 (1 : F)⁆ := by
  rw [tv_of_ne (show (2 : Fin 3) ≠ 1 by decide) c,
    tv_of_ne (show (1 : Fin 3) ≠ 0 by decide) (1 : F),
    tv_of_ne (show (2 : Fin 3) ≠ 0 by decide) c,
    Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) c (1 : F),
    mul_one]

private lemma commutator_mem_closure {F : Type*} [Field F]
    {S : Set (Matrix.SpecialLinearGroup (Fin 3) F)} {a b : Matrix.SpecialLinearGroup (Fin 3) F}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) :
    ⁅a, b⁆ ∈ Subgroup.closure S := by
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
    (Subgroup.inv_mem _ hb)

theorem closure_tv_three {F : Type*} [Field F] :
    Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪
      {g | ∃ c : F, g = tv 1 0 c} ∪ {g | ∃ c : F, g = tv 1 2 c} ∪
      {g | ∃ c : F, g = tv 2 1 c} :
        Set (Matrix.SpecialLinearGroup (Fin 3) F)) = ⊤ := by
  set S : Set (Matrix.SpecialLinearGroup (Fin 3) F) :=
    {g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c} ∪
      {g | ∃ c : F, g = tv 1 2 c} ∪ {g | ∃ c : F, g = tv 2 1 c} with hS
  have h01 : ∀ c : F, tv 0 1 c ∈ Subgroup.closure S := fun c =>
    Subgroup.subset_closure (by rw [hS]; exact Or.inl (Or.inl (Or.inl ⟨c, rfl⟩)))
  have h10 : ∀ c : F, tv 1 0 c ∈ Subgroup.closure S := fun c =>
    Subgroup.subset_closure (by rw [hS]; exact Or.inl (Or.inl (Or.inr ⟨c, rfl⟩)))
  have h12 : ∀ c : F, tv 1 2 c ∈ Subgroup.closure S := fun c =>
    Subgroup.subset_closure (by rw [hS]; exact Or.inl (Or.inr ⟨c, rfl⟩))
  have h21 : ∀ c : F, tv 2 1 c ∈ Subgroup.closure S := fun c =>
    Subgroup.subset_closure (by rw [hS]; exact Or.inr ⟨c, rfl⟩)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  rw [← tv_of_ne hij c]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · change tv 0 2 c ∈ Subgroup.closure S
    rw [tv_zero_two c]
    exact commutator_mem_closure (h01 c) (h12 1)
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · change tv 2 0 c ∈ Subgroup.closure S
    rw [tv_two_zero c]
    exact commutator_mem_closure (h21 c) (h10 1)
  · exact h21 c
  · exact absurd rfl hij

end CFSG.Timmesfeld
