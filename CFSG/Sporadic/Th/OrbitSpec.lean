module

public import Mathlib
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Th

open Native

section Orbit

variable {G Y : Type*} [Group G] [MulAction G Y]

theorem smul_set_eq_of_subset_of_finite {g : G} {S : Set Y} (hS : S.Finite)
    (h : ∀ y ∈ S, g • y ∈ S) : (fun y => g • y) '' S = S := by
  have hsub : (fun y => g • y) '' S ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  apply Set.eq_of_subset_of_ncard_le hsub _ hS
  rw [Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem inv_smul_mem_of_subset_of_finite {g : G} {S : Set Y} (hS : S.Finite)
    (h : ∀ y ∈ S, g • y ∈ S) : ∀ y ∈ S, g⁻¹ • y ∈ S := by
  intro y hy
  have := smul_set_eq_of_subset_of_finite hS h
  rw [← this] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simpa using hz

theorem smul_mem_of_closure {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    {S : Set Y} (hS : S.Finite) (ha : ∀ y ∈ S, a • y ∈ S) (hb : ∀ y ∈ S, b • y ∈ S)
    (g : G) : ∀ y ∈ S, g • y ∈ S := by
  have hg : g ∈ Subgroup.closure ({a, b} : Set G) := by rw [hgen]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => intro y hy; simpa using hy
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_smul]
    exact hx _ (hz y hy)
  | inv x _ hx => exact inv_smul_mem_of_subset_of_finite hS hx

theorem orbit_eq_image {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) {n : ℕ}
    (hn : 0 < n) (P : ℕ → Y) {α β : ℕ → ℕ} (hα : ∀ i < n, α i < n ∧ a • P i = P (α i))
    (hβ : ∀ i < n, β i < n ∧ b • P i = P (β i)) (par lab : ℕ → ℕ)
    (htree : ∀ i < n, 0 < i → par i < i ∧
      ((lab i = 1 ∧ α (par i) = i) ∨ (lab i = 2 ∧ β (par i) = i))) :
    MulAction.orbit G (P 0) = P '' Set.Iio n := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have hS : (P '' Set.Iio n).Finite := (Set.finite_Iio n).image P
    refine smul_mem_of_closure hgen hS ?_ ?_ g (P 0) ⟨0, hn, rfl⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨α i, (hα i hi).1, (hα i hi).2.symm⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨β i, (hβ i hi).1, (hβ i hi).2.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact MulAction.mem_orbit_self _
      · obtain ⟨hpar, hcase⟩ := htree i hi hpos
        have hp := ih (par i) hpar (lt_trans hpar hi)
        rcases hcase with ⟨_, he⟩ | ⟨_, he⟩
        · rw [← he, ← (hα (par i) (lt_trans hpar hi)).2]
          exact MulAction.mem_orbit_of_mem_orbit a hp
        · rw [← he, ← (hβ (par i) (lt_trans hpar hi)).2]
          exact MulAction.mem_orbit_of_mem_orbit b hp

@[expose] noncomputable def orbitEquiv {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    {n : ℕ}
    (hn : 0 < n) (P : ℕ → Y) (hinj : ∀ i < n, ∀ j < n, P i = P j → i = j)
    {α β : ℕ → ℕ} (hα : ∀ i < n, α i < n ∧ a • P i = P (α i))
    (hβ : ∀ i < n, β i < n ∧ b • P i = P (β i)) (par lab : ℕ → ℕ)
    (htree : ∀ i < n, 0 < i → par i < i ∧
      ((lab i = 1 ∧ α (par i) = i) ∨ (lab i = 2 ∧ β (par i) = i))) :
    Fin n ≃ MulAction.orbit G (P 0) :=
  Equiv.ofBijective
    (fun i => ⟨P i, by
      rw [orbit_eq_image hgen hn P hα hβ par lab htree]
      exact ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (hinj i i.isLt j j.isLt (congrArg Subtype.val h)), by
      rintro ⟨y, hy⟩
      rw [orbit_eq_image hgen hn P hα hβ par lab htree] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact ⟨⟨i, hi⟩, rfl⟩⟩

end Orbit

end CFSG.Sporadic.Th
