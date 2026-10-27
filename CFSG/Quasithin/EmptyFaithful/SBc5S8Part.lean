module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor

public section

open scoped Pointwise

namespace CFSG.Quasithin.SBc5S8

theorem perm_apply_inv_self (σ : Equiv.Perm (Fin 8)) (i : Fin 8) : σ (σ⁻¹ i) = i :=
  σ.apply_symm_apply i

@[expose] def PS (σ : Equiv.Perm (Fin 8)) : Prop :=
  (∀ i : Fin 8, (σ i).val < 4 ↔ i.val < 4) ∨ (∀ i : Fin 8, (σ i).val < 4 ↔ ¬ i.val < 4)

instance : DecidablePred PS := fun σ => by unfold PS; infer_instance

@[expose] def partStab : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | PS σ}
  one_mem' := Or.inl fun _ => Iff.rfl
  mul_mem' := by
    rintro σ τ (hσ | hσ) (hτ | hτ)
    · exact Or.inl fun i => (hσ (τ i)).trans (hτ i)
    · exact Or.inr fun i => (hσ (τ i)).trans (hτ i)
    · exact Or.inr fun i => (hσ (τ i)).trans (not_congr (hτ i))
    · exact Or.inl fun i => (hσ (τ i)).trans ((not_congr (hτ i)).trans not_not)
  inv_mem' := by
    rintro σ (hσ | hσ)
    · refine Or.inl fun i => ?_
      have := hσ (σ⁻¹ i)
      rwa [perm_apply_inv_self, iff_comm] at this
    · refine Or.inr fun i => ?_
      have := hσ (σ⁻¹ i)
      rw [perm_apply_inv_self] at this
      rw [this, not_not]

theorem mem_partStab {σ : Equiv.Perm (Fin 8)} : σ ∈ partStab ↔ PS σ := Iff.rfl

@[expose] def c1 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * Equiv.swap 1 3

@[expose] def c3 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 4 6

@[expose] def c4 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 4 7

@[expose] def s01 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def swapQ : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7

theorem sign_swap_mul_swap {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.Perm.sign (Equiv.swap a b * Equiv.swap c d) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
  decide

theorem sign_c1 : Equiv.Perm.sign c1 = 1 := sign_swap_mul_swap (by decide) (by decide)

theorem sign_c3 : Equiv.Perm.sign c3 = 1 := sign_swap_mul_swap (by decide) (by decide)

theorem sign_c4 : Equiv.Perm.sign c4 = 1 := sign_swap_mul_swap (by decide) (by decide)

theorem sign_s01 : Equiv.Perm.sign s01 = 1 := sign_swap_mul_swap (by decide) (by decide)

theorem sign_swapQ : Equiv.Perm.sign swapQ = 1 := by
  unfold swapQ
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 8) ≠ 4 by decide), Equiv.Perm.sign_swap (show (1 : Fin 8) ≠ 5 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 8) ≠ 6 by decide), Equiv.Perm.sign_swap (show (3 : Fin 8) ≠ 7 by decide)]
  decide

theorem PS_facts : PS c1 ∧ PS c3 ∧ PS c4 ∧ PS s01 ∧ PS swapQ := by decide +kernel

theorem swapQ_lt : ∀ y : Fin 8, (swapQ y).val < 4 ↔ ¬ y.val < 4 := by decide +kernel

theorem forall_fin8 {P : Fin 8 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ x, P x := by
  intro x
  fin_cases x <;> assumption

theorem block_classification {B : Set (Fin 8)} (h0 : (0 : Fin 8) ∈ B)
    (hc1 : ∀ x, c1 x ∈ B ↔ x ∈ B) (hc3 : ∀ x, c3 x ∈ B ↔ x ∈ B) (hc4 : ∀ x, c4 x ∈ B ↔ x ∈ B)
    (hs : (4 : Fin 8) ∈ B → ∀ x, s01 x ∈ B ↔ x ∈ B) :
    (∀ i, i ∈ B ↔ i = 0) ∨ (∀ i, i ∈ B ↔ i.val < 4) ∨ (∀ i, i ∈ B) := by
  have e1 := hc1 1
  have e2 := hc1 3
  have f1 := hc3 4
  have f2 := hc3 6
  have f3 := hc4 4
  rw [show c1 1 = 3 from by decide +kernel] at e1
  rw [show c1 3 = 2 from by decide +kernel] at e2
  rw [show c3 4 = 6 from by decide +kernel] at f1
  rw [show c3 6 = 5 from by decide +kernel] at f2
  rw [show c4 4 = 7 from by decide +kernel] at f3
  by_cases h4 : (4 : Fin 8) ∈ B
  · have h1 : (1 : Fin 8) ∈ B := by
      have := hs h4 0
      rw [show s01 0 = 1 from by decide +kernel] at this
      exact this.2 h0
    have h3 : (3 : Fin 8) ∈ B := e1.2 h1
    have h2 : (2 : Fin 8) ∈ B := e2.2 h3
    have h6 : (6 : Fin 8) ∈ B := f1.2 h4
    have h5 : (5 : Fin 8) ∈ B := f2.2 h6
    have h7 : (7 : Fin 8) ∈ B := f3.2 h4
    exact Or.inr (Or.inr (forall_fin8 h0 h1 h2 h3 h4 h5 h6 h7))
  · have h6 : (6 : Fin 8) ∉ B := fun h => h4 (f1.1 h)
    have h5 : (5 : Fin 8) ∉ B := fun h => h6 (f2.1 h)
    have h7 : (7 : Fin 8) ∉ B := fun h => h4 (f3.1 h)
    by_cases h1 : (1 : Fin 8) ∈ B
    · have h3 : (3 : Fin 8) ∈ B := e1.2 h1
      have h2 : (2 : Fin 8) ∈ B := e2.2 h3
      refine Or.inr (Or.inl (forall_fin8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_))
      · exact ⟨fun _ => by decide, fun _ => h0⟩
      · exact ⟨fun _ => by decide, fun _ => h1⟩
      · exact ⟨fun _ => by decide, fun _ => h2⟩
      · exact ⟨fun _ => by decide, fun _ => h3⟩
      · exact ⟨fun h => absurd h h4, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h5, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h6, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h7, fun h => absurd h (by decide)⟩
    · have h3 : (3 : Fin 8) ∉ B := fun h => h1 (e1.1 h)
      have h2 : (2 : Fin 8) ∉ B := fun h => h3 (e2.1 h)
      refine Or.inl (forall_fin8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · exact ⟨fun _ => rfl, fun _ => h0⟩
      · exact ⟨fun h => absurd h h1, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h2, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h3, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h4, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h5, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h6, fun h => absurd h (by decide)⟩
      · exact ⟨fun h => absurd h h7, fun h => absurd h (by decide)⟩

theorem isPreprimitive_of_not_le_partStab {Q : Subgroup (Equiv.Perm (Fin 8))}
    (h1 : c1 ∈ Q) (h3 : c3 ∈ Q) (h4 : c4 ∈ Q) (hs01 : s01 ∈ Q) (hs : swapQ ∈ Q)
    (hQ : ¬ Q ≤ partStab) : MulAction.IsPreprimitive Q (Fin 8) := by
  refine MulAction.IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints (a := (0 : Fin 8)) ?_ ?_
  · intro h
    have h1 := (MulAction.mem_fixedPoints.1 h) ⟨_, hs01⟩
    have h2 : s01 0 = 0 := h1
    revert h2
    decide +kernel
  · intro B h0B hB
    have hinv : ∀ g ∈ Q, ∀ a ∈ B, g a ∈ B → ∀ x, (g x ∈ B ↔ x ∈ B) := by
      intro g hg a ha hga x
      have h1 : (⟨g, hg⟩ : Q) • B = B := hB.smul_eq_of_mem (g := ⟨g, hg⟩) ha hga
      have h2 : (⟨g, hg⟩ : Q) • x ∈ (⟨g, hg⟩ : Q) • B ↔ x ∈ B := Set.smul_mem_smul_set_iff
      rw [h1] at h2
      exact h2
    have hfix : ∀ g ∈ Q, g 0 = 0 → ∀ x, (g x ∈ B ↔ x ∈ B) := fun g hg h0 =>
      hinv g hg 0 h0B (by rw [h0]; exact h0B)
    have hcls := block_classification h0B (hfix c1 h1 (by decide +kernel)) (hfix c3 h3 (by decide +kernel))
      (hfix c4 h4 (by decide +kernel)) (fun h4B => hinv s01 hs01 4 h4B (by
        rw [show s01 4 = 4 from by decide +kernel]
        exact h4B))
    rcases hcls with h | h | h
    · left
      intro x hx y hy
      rw [(h x).1 hx, (h y).1 hy]
    · exfalso
      apply hQ
      intro q hq
      by_cases hex : ∃ a ∈ B, q a ∈ B
      · obtain ⟨a, ha, hqa⟩ := hex
        refine Or.inl fun i => ?_
        rw [← h, ← h]
        exact hinv q hq a ha hqa i
      · push Not at hex
        refine Or.inr fun i => ?_
        have hq0 : q 0 ∉ B := hex 0 h0B
        have hs0 : swapQ (q 0) ∈ B := by
          rw [h]
          exact (swapQ_lt _).2 (fun h' => hq0 ((h _).2 h'))
        have h3 := hinv (swapQ * q) (Q.mul_mem hs hq) 0 h0B hs0 i
        rw [Equiv.Perm.mul_apply, h, h, swapQ_lt] at h3
        tauto
    · right
      ext x
      simpa using h x

theorem partStab_alt_max {Q : Subgroup (Equiv.Perm (Fin 8))}
    (hK : alternatingGroup (Fin 8) ⊓ partStab ≤ Q) (hQ : Q ≤ alternatingGroup (Fin 8)) :
    Q = alternatingGroup (Fin 8) ⊓ partStab ∨ Q = alternatingGroup (Fin 8) := by
  by_cases h : Q ≤ partStab
  · exact Or.inl (le_antisymm (le_inf hQ h) hK)
  · right
    obtain ⟨p1, p3, p4, p01, ps⟩ := PS_facts
    have hprim := isPreprimitive_of_not_le_partStab (Q := Q)
      (hK ⟨Equiv.Perm.mem_alternatingGroup.2 sign_c1, p1⟩)
      (hK ⟨Equiv.Perm.mem_alternatingGroup.2 sign_c3, p3⟩)
      (hK ⟨Equiv.Perm.mem_alternatingGroup.2 sign_c4, p4⟩)
      (hK ⟨Equiv.Perm.mem_alternatingGroup.2 sign_s01, p01⟩)
      (hK ⟨Equiv.Perm.mem_alternatingGroup.2 sign_swapQ, ps⟩) h
    have h3 : c1.IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    exact le_antisymm hQ (Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3
      (hK ⟨Equiv.Perm.mem_alternatingGroup.2 sign_c1, p1⟩))

theorem three_cycle_not_PS : ¬ PS (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 0 4) := by decide +kernel

theorem partStab_alt_ne : alternatingGroup (Fin 8) ⊓ partStab ≠ alternatingGroup (Fin 8) := by
  intro h
  have : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 0 4) ∈ alternatingGroup (Fin 8) ⊓ partStab := by
    rw [h]
    exact Equiv.Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide))
  exact three_cycle_not_PS this.2

end CFSG.Quasithin.SBc5S8
