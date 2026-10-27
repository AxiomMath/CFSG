module

public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.NoE9Z4MinGrp

variable {G : Type*} [Group G]

theorem exists_involution_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ g ∈ Z, g = 1 ∨ g = z := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  refine ⟨y, y.2, fun h => hy (Subtype.ext h), fun g hg => ?_⟩
  by_cases h1 : g = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨g, hg⟩ fun h => h1 (congrArg Subtype.val h)))

theorem exists_basis_of_card_four {V Z : Subgroup G} {z : G} (hZV : Z ≤ V) (hV4 : Nat.card V = 4)
    (hZ : Nat.card Z = 2) (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∃ v ∈ V, v ∉ Z ∧ ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z := by
  classical
  have hex : ∃ v ∈ V, v ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ Z := fun v hv => hcon v hv
    have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨v, hvV, hvZ⟩ := hex
  refine ⟨v, hvV, hvZ, fun x hx => ?_⟩
  have hzV : z ∈ V := hZV hz
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Z.one_mem)
  have hvz : v ≠ z := fun h => hvZ (h ▸ hz)
  have hz1' : z⁻¹ ∈ Z := Z.inv_mem hz
  have h1 : v * z ≠ 1 := fun h => hvZ (by
    have : v = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]; exact hz1')
  have h2 : v * z ≠ z := fun h => hv1 (by
    have h' : v * z = 1 * z := by rw [h, one_mul]
    exact mul_right_cancel h')
  have h3 : v * z ≠ v := fun h => hz1 (by
    have h' : v * z = v * 1 := by rw [h, mul_one]
    exact mul_left_cancel h')
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype V := Fintype.ofFinite V
  let S : Finset V := {⟨1, V.one_mem⟩, ⟨z, hzV⟩, ⟨v, hvV⟩, ⟨v * z, V.mul_mem hvV hzV⟩}
  have hS : S.card = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hV4]
    have e1 : (⟨1, V.one_mem⟩ : V) ≠ ⟨z, hzV⟩ := fun h => hz1 (congrArg Subtype.val h).symm
    have e2 : (⟨1, V.one_mem⟩ : V) ≠ ⟨v, hvV⟩ := fun h => hv1 (congrArg Subtype.val h).symm
    have e3 : (⟨1, V.one_mem⟩ : V) ≠ ⟨v * z, V.mul_mem hvV hzV⟩ := fun h =>
      h1 (congrArg Subtype.val h).symm
    have e4 : (⟨z, hzV⟩ : V) ≠ ⟨v, hvV⟩ := fun h => hvz (congrArg Subtype.val h).symm
    have e5 : (⟨z, hzV⟩ : V) ≠ ⟨v * z, V.mul_mem hvV hzV⟩ := fun h =>
      h2 (congrArg Subtype.val h).symm
    have e6 : (⟨v, hvV⟩ : V) ≠ ⟨v * z, V.mul_mem hvV hzV⟩ := fun h =>
      h3 (congrArg Subtype.val h).symm
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using e6
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨e4, e5⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨e1, e2, e3⟩
  have hall : S = Finset.univ := Finset.eq_univ_of_card S hS
  have hmem : (⟨x, hx⟩ : V) ∈ S := by rw [hall]; exact Finset.mem_univ _
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem central_of_gen {V : Subgroup G} {z v : G}
    (hV : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z) {c : G}
    (hcz : c * z = z * c) (hcv : c * v = v * c) : ∀ x ∈ V, c * x = x * c := by
  intro x hx
  rcases hV x hx with rfl | rfl | rfl | rfl
  · simp
  · exact hcz
  · exact hcv
  · calc c * (v * z) = (c * v) * z := by rw [mul_assoc]
      _ = v * c * z := by rw [hcv]
      _ = v * (c * z) := by rw [mul_assoc]
      _ = v * (z * c) := by rw [hcz]
      _ = v * z * c := by rw [mul_assoc]

theorem y_moves_of_order_three {V Z : Subgroup G} {z v y : G} (hz2 : z * z = 1) (hzZ : z ∈ Z)
    (hvV : v ∈ V) (hvZ : v ∉ Z)
    (hV : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z)
    (hyN : ∀ x ∈ V, y * x * y⁻¹ ∈ V)
    (hnc : ¬ ∀ x ∈ V, y * x = x * y) (h3 : ∀ x ∈ V, y ^ 3 * x = x * y ^ 3) :
    y * z * y⁻¹ ≠ z := by
  intro hyz
  have hcz : y * z = z * y := by
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hyz]
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Z.one_mem)
  have hvz : v ≠ z := fun h => hvZ (h ▸ hzZ)
  rcases hV _ (hyN v hvV) with h | h | h | h
  · exact hv1 (by
      calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group)
  · exact hvz (by
      calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
        _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [h, hyz]
        _ = z := by group)
  · refine hnc (central_of_gen hV hcz ?_)
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [h]
  · refine hnc ?_
    have e : y * y * v * y⁻¹ * y⁻¹ = v := by
      calc y * y * v * y⁻¹ * y⁻¹ = y * (y * v * y⁻¹) * y⁻¹ := by group
        _ = y * (v * z) * y⁻¹ := by rw [h]
        _ = (y * v * y⁻¹) * (y * z * y⁻¹) := by group
        _ = v * z * z := by rw [h, hyz]
        _ = v := by rw [mul_assoc, hz2, mul_one]
    have hy2v : (y * y) * v = v * (y * y) := by
      calc y * y * v = (y * y * v * y⁻¹ * y⁻¹) * y * y := by group
        _ = v * y * y := by rw [e]
        _ = v * (y * y) := by rw [mul_assoc]
    have hy2z : (y * y) * z = z * (y * y) := by
      calc y * y * z = y * (y * z) := by rw [mul_assoc]
        _ = y * (z * y) := by rw [hcz]
        _ = (y * z) * y := by rw [mul_assoc]
        _ = (z * y) * y := by rw [hcz]
        _ = z * (y * y) := by rw [mul_assoc]
    have hyy := central_of_gen hV hy2z hy2v
    intro x hx
    have e1 : y * x * (y * y) = x * y * (y * y) := by
      calc y * x * (y * y) = y * (x * (y * y)) := by rw [mul_assoc]
        _ = y * (y * y * x) := by rw [hyy x hx]
        _ = y ^ 3 * x := by rw [pow_three]; simp only [mul_assoc]
        _ = x * y ^ 3 := h3 x hx
        _ = x * y * (y * y) := by rw [pow_three]; simp only [mul_assoc]
    exact mul_right_cancel e1

end CFSG.Quasithin.NoE9Z4MinGrp
