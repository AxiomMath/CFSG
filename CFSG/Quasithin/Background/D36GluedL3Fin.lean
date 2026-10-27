module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.L3Fin

open CFSG.Quasithin.L3 Matrix.SpecialLinearGroup

abbrev ent (g : Γ) (i j : Fin 3) : ZMod 2 := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j

set_option maxRecDepth 100000 in
theorem P_mul : ∀ a b : Γ, ent a 1 0 = 0 → ent a 2 0 = 0 → ent b 1 0 = 0 → ent b 2 0 = 0 →
    ent (a * b) 1 0 = 0 ∧ ent (a * b) 2 0 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem P_inv : ∀ a : Γ, ent a 1 0 = 0 → ent a 2 0 = 0 →
    ent a⁻¹ 1 0 = 0 ∧ ent a⁻¹ 2 0 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem Q_mul : ∀ a b : Γ, ent a 2 0 = 0 → ent a 2 1 = 0 → ent b 2 0 = 0 → ent b 2 1 = 0 →
    ent (a * b) 2 0 = 0 ∧ ent (a * b) 2 1 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem Q_inv : ∀ a : Γ, ent a 2 0 = 0 → ent a 2 1 = 0 →
    ent a⁻¹ 2 0 = 0 ∧ ent a⁻¹ 2 1 = 0 := by decide +kernel

@[expose] def subP : Subgroup Γ where
  carrier := {g | ent g 1 0 = 0 ∧ ent g 2 0 = 0}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => P_mul a b ha.1 ha.2 hb.1 hb.2
  inv_mem' := fun {a} ha => P_inv a ha.1 ha.2

@[expose] def subQ : Subgroup Γ where
  carrier := {g | ent g 2 0 = 0 ∧ ent g 2 1 = 0}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => Q_mul a b ha.1 ha.2 hb.1 hb.2
  inv_mem' := fun {a} ha => Q_inv a ha.1 ha.2

instance : DecidablePred (· ∈ subP) := fun g =>
  inferInstanceAs (Decidable (ent g 1 0 = 0 ∧ ent g 2 0 = 0))

instance : DecidablePred (· ∈ subQ) := fun g =>
  inferInstanceAs (Decidable (ent g 2 0 = 0 ∧ ent g 2 1 = 0))

set_option maxRecDepth 100000 in
theorem card_subP : Nat.card subP = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_subQ : Nat.card subQ = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

instance : DecidablePred (· ∈ subP ⊓ subQ) := fun g =>
  inferInstanceAs (Decidable (g ∈ subP ∧ g ∈ subQ))

set_option maxRecDepth 100000 in
theorem card_subS : Nat.card ↥(subP ⊓ subQ) = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

@[expose] def w12 : Γ := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

@[expose] def w21 : Γ := ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩

@[expose] def w0 : Γ := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩

@[expose] def y12 : Γ := transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

@[expose] def y23 : Γ := transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 2)

@[expose] def y31 : Γ := transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)

theorem closure_gens' : Subgroup.closure ({y12, y23, y31} : Set Γ) = ⊤ := by
  set H := Subgroup.closure ({y12, y23, y31} : Set Γ) with hH
  have h12 : y12 ∈ H := Subgroup.subset_closure (by simp)
  have h23 : y23 ∈ H := Subgroup.subset_closure (by simp)
  have h31 : y31 ∈ H := Subgroup.subset_closure (by simp)
  have h02 : transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact comm_mem h12 h23
  have h10 : transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (1 : Fin 3) ≠ 2 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact comm_mem h23 h31
  have h21 : transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (2 : Fin 3) ≠ 0 by decide)
      (show (0 : Fin 3) ≠ 1 by decide) (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact comm_mem h31 h12
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2), transvection hij c ∈ H := by
    intro i j hij c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [transvection_coeff_zero]; exact H.one_mem
    · fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | assumption
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin 3) (K := ZMod 2)]
  rw [Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hall t.i t.j t.hij t.c

@[expose] def x21 : Γ := transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)

@[expose] def x32 : Γ := transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

theorem y12_mem : y12 ∈ subP ⊓ subQ := by unfold y12; decide

theorem y23_mem : y23 ∈ subP ⊓ subQ := by unfold y23; decide

set_option maxRecDepth 100000 in
theorem bruhat : ∀ g : Γ, g ∈ subP ∨ g ∈ subQ ∨
    ∃ b ∈ Finset.univ.filter (· ∈ subP ⊓ subQ), ∃ b' ∈ Finset.univ.filter (· ∈ subP ⊓ subQ),
      (g = b * w12 * b' ∨ g = b * w21 * b' ∨ g = b * w0 * b') := by decide +kernel

set_option maxRecDepth 100000 in
theorem y31_eq_w12 : y31 = w12 * y23 * w12⁻¹ := by decide +kernel

set_option maxRecDepth 100000 in
theorem y31_eq_w21 : y31 = w21 * y12 * w21⁻¹ := by decide +kernel

set_option maxRecDepth 100000 in
theorem y31_eq_w0 : y31 = w0 * (y12 * y23 * y12 * y23) * w0⁻¹ := by decide +kernel

theorem eq_top_of_y31 (H : Subgroup Γ) (h12 : y12 ∈ H) (h23 : y23 ∈ H) (h31 : y31 ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff, ← closure_gens', Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem eq_top_of_mem_double (H : Subgroup Γ) (hS : subP ⊓ subQ ≤ H) {g b b' : Γ} (hg : g ∈ H)
    (hb : b ∈ subP ⊓ subQ) (hb' : b' ∈ subP ⊓ subQ)
    (hw : g = b * w12 * b' ∨ g = b * w21 * b' ∨ g = b * w0 * b') : H = ⊤ := by
  have h12 : y12 ∈ H := hS y12_mem
  have h23 : y23 ∈ H := hS y23_mem
  have hb1 : b⁻¹ ∈ H := H.inv_mem (hS hb)
  have hb2 : b'⁻¹ ∈ H := H.inv_mem (hS hb')
  rcases hw with hw | hw | hw
  · have hwH : w12 ∈ H := by
      have : w12 = b⁻¹ * g * b'⁻¹ := by rw [hw]; group
      rw [this]; exact H.mul_mem (H.mul_mem hb1 hg) hb2
    refine eq_top_of_y31 H h12 h23 ?_
    rw [y31_eq_w12]
    exact H.mul_mem (H.mul_mem hwH h23) (H.inv_mem hwH)
  · have hwH : w21 ∈ H := by
      have : w21 = b⁻¹ * g * b'⁻¹ := by rw [hw]; group
      rw [this]; exact H.mul_mem (H.mul_mem hb1 hg) hb2
    refine eq_top_of_y31 H h12 h23 ?_
    rw [y31_eq_w21]
    exact H.mul_mem (H.mul_mem hwH h12) (H.inv_mem hwH)
  · have hwH : w0 ∈ H := by
      have : w0 = b⁻¹ * g * b'⁻¹ := by rw [hw]; group
      rw [this]; exact H.mul_mem (H.mul_mem hb1 hg) hb2
    refine eq_top_of_y31 H h12 h23 ?_
    rw [y31_eq_w0]
    exact H.mul_mem (H.mul_mem hwH (H.mul_mem (H.mul_mem (H.mul_mem h12 h23) h12) h23))
      (H.inv_mem hwH)

theorem le_subP_or_le_subQ (H : Subgroup Γ) (hS : subP ⊓ subQ ≤ H) (hH : H ≠ ⊤) :
    H ≤ subP ∨ H ≤ subQ := by
  have hsub : ∀ g ∈ H, g ∈ subP ∨ g ∈ subQ := by
    intro g hg
    rcases bruhat g with hP | hQ | ⟨b, hb, b', hb', hw⟩
    · exact Or.inl hP
    · exact Or.inr hQ
    · exact absurd (eq_top_of_mem_double H hS hg (Finset.mem_filter.mp hb).2
        (Finset.mem_filter.mp hb').2 hw) hH
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnP, hnQ⟩ := hcon
  rw [SetLike.not_le_iff_exists] at hnP hnQ
  obtain ⟨a, haH, haP⟩ := hnP
  obtain ⟨b, hbH, hbQ⟩ := hnQ
  have haQ : a ∈ subQ := (hsub a haH).resolve_left haP
  have hbP : b ∈ subP := (hsub b hbH).resolve_right hbQ
  rcases hsub (a * b) (H.mul_mem haH hbH) with h | h
  · exact haP (by simpa using subP.mul_mem h (subP.inv_mem hbP))
  · exact hbQ (by simpa using subQ.mul_mem (subQ.inv_mem haQ) h)

set_option maxRecDepth 100000 in
theorem exists_mul_of_not_mem_subP : ∀ g : Γ, g ∈ subP ∨
    ∃ a ∈ Finset.univ.filter (· ∈ subP), x21⁻¹ * (a⁻¹ * g) ∈ subP := by
  unfold x21
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_mul_of_not_mem_subQ : ∀ g : Γ, g ∈ subQ ∨
    ∃ a ∈ Finset.univ.filter (· ∈ subQ), x32⁻¹ * (a⁻¹ * g) ∈ subQ := by
  unfold x32
  decide +kernel

@[expose] def sw12 : Γ := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def sw23 : Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def hsP : Fin 3 → Γ := ![1, x21, sw12]

@[expose] def hsQ : Fin 3 → Γ := ![1, x32, sw23]

theorem hsP_zero : hsP 0 = 1 := rfl

theorem hsQ_zero : hsQ 0 = 1 := rfl

theorem P_two_trans : ∀ g : Γ, g ∈ subP ∨ ∃ a ∈ subP, (hsP 1)⁻¹ * (a⁻¹ * g) ∈ subP := by
  intro g
  rcases exists_mul_of_not_mem_subP g with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, (Finset.mem_filter.mp ha).2, h⟩

theorem Q_two_trans : ∀ g : Γ, g ∈ subQ ∨ ∃ a ∈ subQ, (hsQ 1)⁻¹ * (a⁻¹ * g) ∈ subQ := by
  intro g
  rcases exists_mul_of_not_mem_subQ g with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, (Finset.mem_filter.mp ha).2, h⟩

set_option maxRecDepth 100000 in
theorem P_distinct : ∀ i j : Fin 3, (hsP i)⁻¹ * hsP j ∈ subP → i = j := by
  unfold hsP x21 sw12; decide +kernel

set_option maxRecDepth 100000 in
theorem Q_distinct : ∀ i j : Fin 3, (hsQ i)⁻¹ * hsQ j ∈ subQ → i = j := by
  unfold hsQ x32 sw23; decide +kernel

set_option maxRecDepth 100000 in
theorem P_closed : ∀ q : Γ, q ∈ subQ → ∀ i : Fin 3,
    ∃ j : Fin 3, (hsP j)⁻¹ * (q * hsP i) ∈ subP := by
  unfold hsP x21 sw12; decide +kernel

set_option maxRecDepth 100000 in
theorem Q_closed : ∀ q : Γ, q ∈ subP → ∀ i : Fin 3,
    ∃ j : Fin 3, (hsQ j)⁻¹ * (q * hsQ i) ∈ subQ := by
  unfold hsQ x32 sw23; decide +kernel

set_option maxRecDepth 100000 in
theorem P_not_conj : ∀ g : Γ, ∃ a : Γ, a ∈ subP ∧ g * a * g⁻¹ ∉ subQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Q_not_conj : ∀ g : Γ, ∃ a : Γ, a ∈ subQ ∧ g * a * g⁻¹ ∉ subP := by
  decide +kernel

theorem nonabelian : ∃ a b : Γ, a * b ≠ b * a := ⟨y12, y23, by unfold y12 y23; decide +kernel⟩

end CFSG.Quasithin.L3Fin
