module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesExtra

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Elementary

variable {Γ : Type} [Group Γ]

theorem comm_of_gens (s : Set Γ) (hc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  have h1 : ∀ g ∈ s, ∀ y ∈ Subgroup.closure s, Commute g y := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem h hh => exact hc g hg h hh
    | one => exact Commute.one_right g
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  intro x hx y hy
  have : Commute x y := by
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact h1 g hg y hy
    | one => exact Commute.one_left y
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  exact this.eq

theorem sq_of_gens (s : Set Γ) (hc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g)
    (hsq : ∀ g ∈ s, g * g = 1) : ∀ x ∈ Subgroup.closure s, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact hsq g hg
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := comm_of_gens s hc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

end Elementary

section Central

variable {V : Type} [Group V] (s : Set V) {z : V}

theorem comm_swap_aux (hzz : z * z = 1) {x y : V} (h : x * y = y * x ∨ x * y = z * (y * x)) :
    y * x = x * y ∨ y * x = z * (x * y) := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    rw [h, ← mul_assoc z z, hzz, one_mul]

theorem comm_mul_aux (hzc : ∀ y, y * z = z * y) (hzz : z * z = 1) {a b y : V}
    (ha : a * y = y * a ∨ a * y = z * (y * a)) (hb : b * y = y * b ∨ b * y = z * (y * b)) :
    a * b * y = y * (a * b) ∨ a * b * y = z * (y * (a * b)) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · left
    calc a * b * y = a * (b * y) := mul_assoc _ _ _
      _ = a * (y * b) := by rw [hb]
      _ = a * y * b := (mul_assoc _ _ _).symm
      _ = y * a * b := by rw [ha]
      _ = y * (a * b) := mul_assoc _ _ _
  · right
    calc a * b * y = a * (b * y) := mul_assoc _ _ _
      _ = a * (z * (y * b)) := by rw [hb]
      _ = (a * z) * (y * b) := (mul_assoc _ _ _).symm
      _ = (z * a) * (y * b) := by rw [hzc a]
      _ = z * (a * (y * b)) := mul_assoc _ _ _
      _ = z * (a * y * b) := by rw [← mul_assoc a y b]
      _ = z * (y * a * b) := by rw [ha]
      _ = z * (y * (a * b)) := by rw [mul_assoc y a b]
  · right
    calc a * b * y = a * (b * y) := mul_assoc _ _ _
      _ = a * (y * b) := by rw [hb]
      _ = a * y * b := (mul_assoc _ _ _).symm
      _ = z * (y * a) * b := by rw [ha]
      _ = z * (y * a * b) := mul_assoc _ _ _
      _ = z * (y * (a * b)) := by rw [mul_assoc y a b]
  · left
    calc a * b * y = a * (b * y) := mul_assoc _ _ _
      _ = a * (z * (y * b)) := by rw [hb]
      _ = (a * z) * (y * b) := (mul_assoc _ _ _).symm
      _ = (z * a) * (y * b) := by rw [hzc a]
      _ = z * (a * (y * b)) := mul_assoc _ _ _
      _ = z * (a * y * b) := by rw [← mul_assoc a y b]
      _ = z * (z * (y * a) * b) := by rw [ha]
      _ = z * (z * (y * a * b)) := by rw [mul_assoc z (y * a) b]
      _ = (z * z) * (y * a * b) := (mul_assoc _ _ _).symm
      _ = y * a * b := by rw [hzz, one_mul]
      _ = y * (a * b) := mul_assoc _ _ _

theorem comm_inv_aux (hzc : ∀ y, y * z = z * y) (hzz : z * z = 1) {a y : V}
    (h : a * y = y * a ∨ a * y = z * (y * a)) :
    a⁻¹ * y = y * a⁻¹ ∨ a⁻¹ * y = z * (y * a⁻¹) := by
  rcases h with h | h
  · exact Or.inl (Commute.inv_left (show Commute a y from h)).eq
  · right
    have hya : y * a = z * (a * y) := by rw [h, ← mul_assoc z z, hzz, one_mul]
    calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
      _ = a⁻¹ * (z * (a * y)) * a⁻¹ := by rw [hya]
      _ = (a⁻¹ * z) * (a * y) * a⁻¹ := by group
      _ = (z * a⁻¹) * (a * y) * a⁻¹ := by rw [hzc a⁻¹]
      _ = z * (a⁻¹ * (a * y) * a⁻¹) := by group
      _ = z * (y * a⁻¹) := by group

theorem comm_central_of_gens (hs : Subgroup.closure s = ⊤) (hzc : ∀ y, y * z = z * y)
    (hzz : z * z = 1) (hgc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g ∨ g * h = z * (h * g)) :
    ∀ x y : V, x * y = y * x ∨ x * y = z * (y * x) := by
  have hgy : ∀ g ∈ s, ∀ y : V, g * y = y * g ∨ g * y = z * (y * g) := by
    intro g hg y
    have hy : y ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top y
    induction hy using Subgroup.closure_induction with
    | mem h hh => exact hgc g hg h hh
    | one => left; simp
    | mul a b _ _ ha hb =>
      exact comm_swap_aux hzz
        (comm_mul_aux hzc hzz (comm_swap_aux hzz ha) (comm_swap_aux hzz hb))
    | inv a _ ha => exact comm_swap_aux hzz (comm_inv_aux hzc hzz (comm_swap_aux hzz ha))
  intro x y
  have hx : x ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact hgy g hg y
  | one => left; simp
  | mul a b _ _ ha hb => exact comm_mul_aux hzc hzz ha hb
  | inv a _ ha => exact comm_inv_aux hzc hzz ha

theorem sq_central_of_gens (hs : Subgroup.closure s = ⊤) (hzc : ∀ y, y * z = z * y)
    (hzz : z * z = 1) (hgc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g ∨ g * h = z * (h * g))
    (hgsq : ∀ g ∈ s, g * g = 1 ∨ g * g = z) : ∀ x : V, x * x = 1 ∨ x * x = z := by
  have hQ := comm_central_of_gens s hs hzc hzz hgc
  intro x
  have hx : x ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact hgsq g hg
  | one => left; simp
  | mul a b _ _ ha hb =>
    have key : a * b * (a * b) = a * a * (b * b) ∨ a * b * (a * b) = z * (a * a * (b * b)) := by
      rcases hQ b a with hba | hba
      · left
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hba]
          _ = a * a * (b * b) := by group
      · right
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (z * (a * b)) * b := by rw [hba]
          _ = (a * z) * (a * b) * b := by group
          _ = (z * a) * (a * b) * b := by rw [hzc a]
          _ = z * (a * a * (b * b)) := by group
    have hz1 : z * z = 1 := hzz
    rcases key with key | key <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [key, ha, hb, hz1]
  | inv a _ ha =>
    rw [← mul_inv_rev]
    rcases ha with ha | ha
    · left; rw [ha, inv_one]
    · right; rw [ha]; exact inv_eq_of_mul_eq_one_right hzz

theorem isExtraspecial2_of_gens [Finite V] (hs : Subgroup.closure s = ⊤) (hz1 : z ≠ 1)
    (hzc : ∀ y, y * z = z * y) (hzz : z * z = 1)
    (hgc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g ∨ g * h = z * (h * g))
    (hgsq : ∀ g ∈ s, g * g = 1 ∨ g * g = z)
    (hcen : ∀ x : V, (∀ g ∈ s, x * g = g * x) → x = 1 ∨ x = z) {m : ℕ}
    (hcard : Nat.card V = 2 ^ (1 + 2 * m)) (hm : 1 ≤ m) : IsExtraspecial2 m V :=
  A312ExtShapes.isExtraspecial2_of_central_involution z hz1 hzc
    (sq_central_of_gens s hs hzc hzz hgc hgsq) (comm_central_of_gens s hs hzc hzz hgc)
    (fun x hx => hcen x fun g _ => hx g) hcard hm

end Central

end CFSG.Quasithin.A312M24
