module

public import CFSG.Sporadic.Recognition.PresentedWords

public section

namespace CFSG.Sporadic.Recognition.PresentedWords

@[expose] def expSum {n : ℕ} (i : Fin n) (w : List (Fin n × Bool)) : ℤ :=
  (w.map fun l => if l.1 = i then (if l.2 then (1 : ℤ) else -1) else 0).sum

theorem expSum_cons {n : ℕ} (i : Fin n) (l : Fin n × Bool) (w : List (Fin n × Bool)) :
    expSum i (l :: w) =
      (if l.1 = i then (if l.2 then (1 : ℤ) else -1) else 0) + expSum i w := by
  simp [expSum]

@[simp] theorem expSum_nil {n : ℕ} (i : Fin n) : expSum i [] = 0 := rfl

theorem wprod_eq_prod_zpow_expSum {A : Type*} [CommGroup A] {n : ℕ} (y : Fin n → A)
    (w : List (Fin n × Bool)) : wprod y w = ∏ i, y i ^ expSum i w := by
  induction w with
  | nil => simp [wprod]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [wprod_cons, ih]
    simp only [expSum_cons]
    have hsplit : (∏ j, y j ^ ((if i = j then (if b then (1 : ℤ) else -1) else 0) +
        expSum j w)) =
        (∏ j, y j ^ (if i = j then (if b then (1 : ℤ) else -1) else 0)) *
          ∏ j, y j ^ expSum j w := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => zpow_add _ _ _
    rw [hsplit]
    have hsingle : (∏ j, y j ^ (if i = j then (if b then (1 : ℤ) else -1) else 0)) =
        (if b then y i else (y i)⁻¹) := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji
        have hij : i ≠ j := fun h => hji h.symm
        rw [if_neg hij, zpow_zero]
      · intro hi
        simp at hi
    rw [hsingle]

theorem wprod_mul_zpow_of_commute {X : Type*} [Group X] {n : ℕ} (y : Fin n → X) (c : X)
    (hc : ∀ i, Commute c (y i)) (k : Fin n → ℤ) (w : List (Fin n × Bool)) :
    wprod (fun i => y i * c ^ k i) w = wprod y w * c ^ (∑ i, k i * expSum i w) := by
  have hcW : ∀ w : List (Fin n × Bool), Commute c (wprod y w) := by
    intro w
    induction w with
    | nil => simp [wprod]
    | cons l w ih =>
      rw [wprod_cons]
      have hcz : Commute c (if l.2 then y l.1 else (y l.1)⁻¹) := by
        cases l.2 with
        | false => simpa using (hc l.1).inv_right
        | true => simpa using hc l.1
      exact hcz.mul_right ih
  induction w with
  | nil => simp [wprod]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hW : Commute c (wprod y w) := hcW w
    have hzi : Commute c (y i) := hc i
    have hexp : (∑ j, k j * expSum j ((i, b) :: w)) =
        (if b then (1 : ℤ) else -1) * k i + ∑ j, k j * expSum j w := by
      have h1 : ∀ j, k j * expSum j ((i, b) :: w) =
          k j * (if i = j then (if b then (1 : ℤ) else -1) else 0) + k j * expSum j w := by
        intro j
        rw [expSum_cons, mul_add]
      rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib]
      have h2 : (∑ j, k j * (if i = j then (if b then (1 : ℤ) else -1) else 0)) =
          k i * (if b then (1 : ℤ) else -1) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          have hij : i ≠ j := fun h => hji h.symm
          rw [if_neg hij, mul_zero]
        · intro hi
          simp at hi
      rw [h2, mul_comm]
    rw [wprod_cons, ih, wprod_cons, hexp]
    cases b
    · have hzi' : Commute (c ^ (-k i)) (y i)⁻¹ := (Commute.zpow_left hzi (-k i)).inv_right
      have hcW' : Commute (c ^ (-k i)) (wprod y w) := Commute.zpow_left hW (-k i)
      have hinv : (y i * c ^ k i)⁻¹ = c ^ (-k i) * (y i)⁻¹ := by
        rw [mul_inv_rev, zpow_neg]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hinv]
      calc c ^ (-k i) * (y i)⁻¹ * (wprod y w * c ^ (∑ j, k j * expSum j w))
          = (c ^ (-k i) * (y i)⁻¹) * (wprod y w * c ^ (∑ j, k j * expSum j w)) := by
            group
        _ = ((y i)⁻¹ * c ^ (-k i)) * (wprod y w * c ^ (∑ j, k j * expSum j w)) := by
            rw [hzi'.eq]
        _ = (y i)⁻¹ * (c ^ (-k i) * wprod y w) * c ^ (∑ j, k j * expSum j w) := by
            group
        _ = (y i)⁻¹ * (wprod y w * c ^ (-k i)) * c ^ (∑ j, k j * expSum j w) := by
            rw [hcW'.eq]
        _ = (y i)⁻¹ * wprod y w * (c ^ (-k i) * c ^ (∑ j, k j * expSum j w)) := by
            group
        _ = (y i)⁻¹ * wprod y w * c ^ (-k i + ∑ j, k j * expSum j w) := by
            rw [← zpow_add]
        _ = (y i)⁻¹ * wprod y w * c ^ (-1 * k i + ∑ j, k j * expSum j w) := by
            rw [neg_one_mul]
    · have hcW' : Commute (c ^ k i) (wprod y w) := Commute.zpow_left hW (k i)
      simp only [↓reduceIte]
      calc (y i * c ^ k i) * (wprod y w * c ^ (∑ j, k j * expSum j w))
          = y i * (c ^ k i * wprod y w) * c ^ (∑ j, k j * expSum j w) := by
            group
        _ = y i * (wprod y w * c ^ k i) * c ^ (∑ j, k j * expSum j w) := by
            rw [hcW'.eq]
        _ = y i * wprod y w * (c ^ k i * c ^ (∑ j, k j * expSum j w)) := by
            group
        _ = y i * wprod y w * c ^ (k i + ∑ j, k j * expSum j w) := by
            rw [← zpow_add]
        _ = y i * wprod y w * c ^ (1 * k i + ∑ j, k j * expSum j w) := by
            rw [one_mul]

end CFSG.Sporadic.Recognition.PresentedWords

end
