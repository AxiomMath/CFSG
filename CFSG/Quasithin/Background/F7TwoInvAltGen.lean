module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.Quasithin.F7Two

open Equiv Equiv.Perm MulAction
open scoped Pointwise

variable {α : Type*} [DecidableEq α]

@[expose] def triCycle (a b d : α) : Perm α := swap a b * swap b d

section triCycle

variable {a b d x : α}

theorem triCycle_apply_left (hab : a ≠ b) (had : a ≠ d) : triCycle a b d a = b := by
  simp [triCycle, swap_apply_of_ne_of_ne hab had]

theorem triCycle_apply_mid (hbd : b ≠ d) (had : a ≠ d) : triCycle a b d b = d := by
  simp [triCycle, swap_apply_of_ne_of_ne had.symm hbd.symm]

theorem triCycle_apply_right : triCycle a b d d = a := by
  simp [triCycle]

theorem triCycle_apply_of_ne (ha : x ≠ a) (hb : x ≠ b) (hd : x ≠ d) : triCycle a b d x = x := by
  simp [triCycle, swap_apply_of_ne_of_ne hb hd, swap_apply_of_ne_of_ne ha hb]

theorem triCycle_isThreeCycle [Fintype α] (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    (triCycle a b d).IsThreeCycle := by
  rw [triCycle, swap_comm a b]
  exact isThreeCycle_swap_mul_swap_same hab.symm hbd had

theorem triCycle_mem_alternatingGroup [Fintype α] (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    triCycle a b d ∈ alternatingGroup α :=
  (triCycle_isThreeCycle hab hbd had).mem_alternatingGroup

theorem triCycle_closed {S : Set α} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (hS : ∀ y ∈ S, triCycle a b d y ∈ S) : (a ∈ S ∨ b ∈ S ∨ d ∈ S) → a ∈ S ∧ b ∈ S ∧ d ∈ S := by
  have h1 : a ∈ S → b ∈ S := fun h => triCycle_apply_left hab had ▸ hS a h
  have h2 : b ∈ S → d ∈ S := fun h => triCycle_apply_mid hbd had ▸ hS b h
  have h3 : d ∈ S → a ∈ S := fun h => triCycle_apply_right (a := a) (b := b) ▸ hS d h
  rintro (ha | hb | hd)
  · exact ⟨ha, h1 ha, h2 (h1 ha)⟩
  · exact ⟨h3 (h2 hb), hb, h2 hb⟩
  · exact ⟨h3 hd, h1 (h3 hd), hd⟩

end triCycle

section blocks

variable {H : Subgroup (Perm α)} {B : Set α} {a b d : α}

omit [DecidableEq α] in
theorem isBlock_invariant (hB : IsBlock H B) {c : Perm α} (hc : c ∈ H) {w : α} (hw : w ∈ B)
    (hcw : c w ∈ B) : ∀ y ∈ B, c y ∈ B := by
  have h : (⟨c, hc⟩ : H) • B = (1 : H) • B :=
    hB.smul_eq_smul_of_nonempty ⟨c w, ⟨w, hw, rfl⟩, by rwa [one_smul]⟩
  rw [one_smul] at h
  intro y hy
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem triCycle_closed_of_isBlock (hB : IsBlock H B) (hnt : ¬ B.Subsingleton) (hab : a ≠ b)
    (hbd : b ≠ d) (had : a ≠ d) (hc : triCycle a b d ∈ H) :
    (a ∈ B ∨ b ∈ B ∨ d ∈ B) → a ∈ B ∧ b ∈ B ∧ d ∈ B := by
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ B, ∃ v ∈ B, u ≠ v := by
    simpa [Set.Subsingleton] using hnt
  obtain ⟨w, hw, hcw⟩ : ∃ w ∈ B, triCycle a b d w ∈ B := by
    by_contra! hno
    have hsub : ∀ w ∈ B, w = a ∨ w = b ∨ w = d := by
      intro w hw
      by_contra! hw'
      exact hno w hw (by rwa [triCycle_apply_of_ne hw'.1 hw'.2.1 hw'.2.2])
    have hab' : ¬ (a ∈ B ∧ b ∈ B) := fun h =>
      hno a h.1 (by rw [triCycle_apply_left hab had]; exact h.2)
    have hbd' : ¬ (b ∈ B ∧ d ∈ B) := fun h =>
      hno b h.1 (by rw [triCycle_apply_mid hbd had]; exact h.2)
    have hda' : ¬ (d ∈ B ∧ a ∈ B) := fun h =>
      hno d h.1 (by rw [triCycle_apply_right]; exact h.2)
    have := hsub u hu
    have := hsub v hv
    grind
  exact triCycle_closed hab hbd had (isBlock_invariant hB hc hw hcw)

variable [Fintype α]

theorem alternatingGroup_le_of_connected [Nontrivial α] {P : α → α → α → Prop}
    (hP : ∀ a b d, P a b d → a ≠ b ∧ b ≠ d ∧ a ≠ d ∧ triCycle a b d ∈ H)
    (hconn : ∀ B : Set α, B.Nonempty →
      (∀ a b d, P a b d → (a ∈ B ∨ b ∈ B ∨ d ∈ B) → a ∈ B ∧ b ∈ B ∧ d ∈ B) →
      B = Set.univ) :
    alternatingGroup α ≤ H := by
  obtain ⟨a₀, b₀, d₀, h₀⟩ : ∃ a b d, P a b d := by
    by_contra! hno
    obtain ⟨x, y, hxy⟩ := exists_pair_ne α
    have h := hconn {x} (Set.singleton_nonempty x) (fun a b d h => (hno a b d h).elim)
    exact hxy (by simpa using (Set.eq_univ_iff_forall.1 h y).symm)
  have htr : IsPretransitive H α := by
    rw [isPretransitive_iff_base a₀]
    intro y
    have h := hconn (orbit H a₀) ⟨a₀, mem_orbit_self a₀⟩ (fun a b d hP' => ?_)
    · exact (Set.eq_univ_iff_forall.1 h y)
    · obtain ⟨hab, hbd, had, hc⟩ := hP a b d hP'
      refine triCycle_closed hab hbd had (fun y hy => ?_)
      rw [← IsFixedBlock.orbit a₀ ⟨triCycle a b d, hc⟩]
      exact ⟨y, hy, rfl⟩
  have hpr : IsPreprimitive H α :=
    { toIsPretransitive := htr
      isTrivialBlock_of_isBlock := fun {B} hB => by
        by_cases hnt : B.Subsingleton
        · exact Or.inl hnt
        · refine Or.inr (hconn B ?_ fun a b d hP' => ?_)
          · obtain ⟨u, hu, -⟩ : ∃ u ∈ B, ∃ v ∈ B, u ≠ v := by
              simpa [Set.Subsingleton] using hnt
            exact ⟨u, hu⟩
          · obtain ⟨hab, hbd, had, hc⟩ := hP a b d hP'
            exact triCycle_closed_of_isBlock hB hnt hab hbd had hc }
  obtain ⟨hab, hbd, had, hc⟩ := hP a₀ b₀ d₀ h₀
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hpr
    (triCycle_isThreeCycle hab hbd had) hc

end blocks

end CFSG.Quasithin.F7Two
