module

public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Monster.Existence

variable {G : Type} [Group G] {a : G}

theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact SemiconjBy.orderOf_eq c ((mul_inv_eq_iff_eq_mul.1 hc))

theorem isConj_mul_comm (x y : G) : IsConj (x * y) (y * x) :=
  isConj_iff.2 ⟨x⁻¹, by group⟩

section Involution

variable (ha : orderOf a = 2)
include ha

theorem mul_self_eq_one_of_isConj {x : G} (hx : IsConj a x) : x * x = 1 := by
  rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, ← orderOf_eq_of_isConj hx, ha]

theorem inv_eq_of_isConj {x : G} (hx : IsConj a x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isConj ha hx)

theorem ne_one_of_isConj {x : G} (hx : IsConj a x) : x ≠ 1 := by
  rintro rfl
  have := orderOf_eq_of_isConj hx
  rw [orderOf_one, ha] at this
  omega

theorem ne_of_isConj_mul {x y : G} (hx : IsConj a x) (hxy : IsConj a (x * y)) : x ≠ y := by
  rintro rfl
  rw [mul_self_eq_one_of_isConj ha hx] at hxy
  exact ne_one_of_isConj ha hxy rfl

@[expose] def ThirdVertex (a α β γ : G) : Prop :=
  IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)

variable {α β : G} (hα : IsConj a α) (hβ : IsConj a β) (hαβ : IsConj a (α * β))
include hα hβ hαβ

theorem isTriangle_iff_thirdVertex {γ : G} :
    IsTriangle a {α, β, γ} ↔ ThirdVertex a α β γ := by
  have hne : α ≠ β := ne_of_isConj_mul ha hα hαβ
  have hβα : IsConj a (β * α) := hαβ.trans (isConj_mul_comm α β)
  constructor
  · rintro ⟨hcard, hconj, hpair⟩
    have hγ : IsConj a γ := hconj γ (by simp)
    have hαγ : α ≠ γ := by
      rintro rfl
      have h2 : ({α, β, α} : Set G) = {β, α} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [h2] at hcard
      have := Set.ncard_insert_le β ({α} : Set G)
      rw [Set.ncard_singleton] at this
      omega
    have hβγ : β ≠ γ := by
      rintro rfl
      have h2 : ({α, β, β} : Set G) = {α, β} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [h2] at hcard
      have := Set.ncard_insert_le α ({β} : Set G)
      rw [Set.ncard_singleton] at this
      omega
    exact ⟨hγ, hpair α (by simp) γ (by simp) hαγ, hpair β (by simp) γ (by simp) hβγ⟩
  · rintro ⟨hγ, hαγ, hβγ⟩
    have h1 : α ≠ γ := ne_of_isConj_mul ha hα hαγ
    have h2 : β ≠ γ := ne_of_isConj_mul ha hβ hβγ
    have hγα : IsConj a (γ * α) := hαγ.trans (isConj_mul_comm α γ)
    have hγβ : IsConj a (γ * β) := hβγ.trans (isConj_mul_comm β γ)
    refine ⟨Set.ncard_eq_three.2 ⟨α, β, γ, hne, h1, h2, rfl⟩, ?_, ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hα, hβ, hγ]
    · intro x hx y hy hxy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first | exact absurd rfl hxy | assumption

theorem isShortTriangle_iff {γ : G} (hT : IsTriangle a {α, β, γ}) :
    IsShortTriangle a {α, β, γ} ↔ γ = α * β := by
  have hne : α ≠ β := ne_of_isConj_mul ha hα hαβ
  constructor
  · rintro ⟨-, hS⟩
    have hm := hS α (by simp) β (by simp) hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact absurd (mul_eq_left.1 h) (ne_one_of_isConj ha hβ)
    · exact absurd (mul_eq_right.1 h) (ne_one_of_isConj ha hα)
    · exact h.symm
  · rintro rfl
    refine ⟨hT, ?_⟩
    have h1 := mul_self_eq_one_of_isConj ha hα
    have h2 := mul_self_eq_one_of_isConj ha hβ
    have h3 := mul_self_eq_one_of_isConj ha hαβ
    have hi1 := inv_eq_of_isConj ha hα
    have hi2 := inv_eq_of_isConj ha hβ
    have hi3 := inv_eq_of_isConj ha hαβ
    have hcomm : β * α = α * β := by
      rw [← hi3, mul_inv_rev, hi1, hi2]
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inr (Or.inr rfl)
    · refine Or.inr (Or.inl ?_)
      rw [← mul_assoc, h1, one_mul]
    · refine Or.inr (Or.inr ?_)
      exact hcomm
    · exact absurd rfl hxy
    · refine Or.inl ?_
      rw [← mul_assoc, hcomm, mul_assoc, h2, mul_one]
    · refine Or.inr (Or.inl ?_)
      rw [mul_assoc, hcomm, ← mul_assoc, h1, one_mul]
    · refine Or.inl ?_
      rw [mul_assoc, h2, mul_one]
    · exact absurd rfl hxy

theorem isLongTriangle_iff {γ : G} :
    IsLongTriangle a {α, β, γ} ↔ ThirdVertex a α β γ ∧ γ ≠ α * β := by
  constructor
  · rintro ⟨hT, hS⟩
    refine ⟨(isTriangle_iff_thirdVertex ha hα hβ hαβ).1 hT, fun h => hS ?_⟩
    exact (isShortTriangle_iff ha hα hβ hαβ hT).2 h
  · rintro ⟨hV, hne⟩
    have hT := (isTriangle_iff_thirdVertex ha hα hβ hαβ).2 hV
    exact ⟨hT, fun hS => hne ((isShortTriangle_iff ha hα hβ hαβ hT).1 hS)⟩

theorem longTriangles_eq_image :
    {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s} =
      (fun γ => ({α, β, γ} : Set G)) '' {γ | ThirdVertex a α β γ ∧ γ ≠ α * β} := by
  have hne : α ≠ β := ne_of_isConj_mul ha hα hαβ
  ext s
  constructor
  · rintro ⟨hL, hαs, hβs⟩
    have hcard : s.ncard = 3 := hL.1.1
    have hfin : s.Finite := Set.finite_of_ncard_ne_zero (by omega)
    have hlt : ({α, β} : Set G).ncard < s.ncard := by
      have := Set.ncard_insert_le α ({β} : Set G)
      rw [Set.ncard_singleton] at this
      omega
    obtain ⟨γ, hγs, hγ⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hγ
    have hsub : ({α, β, γ} : Set G) ⊆ s := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({α, β, γ} : Set G).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨α, β, γ, hne, fun h => hγ.1 h.symm, fun h => hγ.2 h.symm, rfl⟩
    have heq : ({α, β, γ} : Set G) = s :=
      Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
    subst heq
    exact ⟨γ, (isLongTriangle_iff ha hα hβ hαβ).1 hL, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(isLongTriangle_iff ha hα hβ hαβ).2 hγ, by simp, by simp⟩

theorem ncard_longTriangles :
    {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard =
      {γ | ThirdVertex a α β γ ∧ γ ≠ α * β}.ncard := by
  rw [longTriangles_eq_image ha hα hβ hαβ]
  refine Set.InjOn.ncard_image fun γ hγ γ' hγ' h => ?_
  have h1 : γ ∈ ({α, β, γ'} : Set G) := by
    rw [← h]; simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h1 | h1 | h1
  · exact absurd h1.symm (ne_of_isConj_mul ha hα hγ.1.2.1)
  · exact absurd h1.symm (ne_of_isConj_mul ha hβ hγ.1.2.2)
  · exact h1

theorem thirdVertex_mul : ThirdVertex a α β (α * β) := by
  refine ⟨hαβ, ?_, ?_⟩
  · rw [← mul_assoc, mul_self_eq_one_of_isConj ha hα, one_mul]
    exact hβ
  · have : β * (α * β) = β * α * β⁻¹ := by rw [inv_eq_of_isConj ha hβ, mul_assoc]
    rw [this]
    exact hα.trans (isConj_iff.2 ⟨β, rfl⟩)

theorem thirdVertex_set_eq :
    {γ | ThirdVertex a α β γ} = insert (α * β) {γ | ThirdVertex a α β γ ∧ γ ≠ α * β} := by
  ext γ
  show ThirdVertex a α β γ ↔ γ = α * β ∨ (ThirdVertex a α β γ ∧ γ ≠ α * β)
  constructor
  · intro h
    by_cases hγ : γ = α * β
    · exact Or.inl hγ
    · exact Or.inr ⟨h, hγ⟩
  · rintro (rfl | ⟨h, -⟩)
    · exact thirdVertex_mul ha hα hβ hαβ
    · exact h

theorem ncard_thirdVertex (hfin : {γ | ThirdVertex a α β γ ∧ γ ≠ α * β}.Finite) :
    {γ | ThirdVertex a α β γ}.ncard =
      {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard + 1 := by
  rw [ncard_longTriangles ha hα hβ hαβ, thirdVertex_set_eq ha hα hβ hαβ,
    Set.ncard_insert_of_notMem (by simp) hfin]

end Involution

end CFSG.Monster.Existence.Compat
