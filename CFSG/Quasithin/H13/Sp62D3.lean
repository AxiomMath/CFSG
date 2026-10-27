module

public import CFSG.Quasithin.H13.Sp62S6Over
public import CFSG.Quasithin.H13.A6Producer134
public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.H13.A6Statements

public section

namespace CFSG.Quasithin.H13.A6

open Equiv

section Abstract

variable {G : Type} [Group G]

theorem maxOvergroups_eq {T X A₁ A₂ E₁ E₂ : Subgroup G}
    (hcls : ∀ Y : Subgroup G, T ≤ Y → Y ≤ X → Y = T ∨ Y = A₁ ∨ Y = A₂ ∨ Y = X)
    (hT₁ : T ≤ A₁) (hT₂ : T ≤ A₂) (h₁X : A₁ ≤ X) (h₂X : A₂ ≤ X)
    (h₁₂ : ¬ A₁ ≤ A₂) (h₂₁ : ¬ A₂ ≤ A₁) (h₁ : A₁ ≠ X) (h₂ : A₂ ≠ X)
    (hE₁ : T ≤ E₁) (hE₁X : E₁ ≤ X) (hE₁T : E₁ ≠ T) (hE₁X' : E₁ ≠ X)
    (hE₂ : T ≤ E₂) (hE₂X : E₂ ≤ X) (hE₂T : E₂ ≠ T) (hE₂X' : E₂ ≠ X) (hE : E₁ ≠ E₂) :
    ∀ Y : Subgroup G, (T ≤ Y ∧ IsMaxSubgroupIn Y X) ↔ (Y = E₁ ∨ Y = E₂) := by
  have hmax₁ : IsMaxSubgroupIn A₁ X := by
    refine ⟨lt_of_le_of_ne h₁X h₁, fun W hW hWX => ?_⟩
    rcases hcls W (hT₁.trans hW) hWX with rfl | rfl | rfl | rfl
    · exact absurd (hW.trans hT₂) h₁₂
    · exact Or.inl rfl
    · exact absurd hW h₁₂
    · exact Or.inr rfl
  have hmax₂ : IsMaxSubgroupIn A₂ X := by
    refine ⟨lt_of_le_of_ne h₂X h₂, fun W hW hWX => ?_⟩
    rcases hcls W (hT₂.trans hW) hWX with rfl | rfl | rfl | rfl
    · exact absurd (hW.trans hT₁) h₂₁
    · exact absurd hW h₂₁
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hEi : ∀ E : Subgroup G, T ≤ E → E ≤ X → E ≠ T → E ≠ X → E = A₁ ∨ E = A₂ := by
    intro E hE hEX hET hEX'
    rcases hcls E hE hEX with h | h | h | h
    · exact absurd h hET
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hEX'
  have hset : ∀ Y : Subgroup G, (Y = A₁ ∨ Y = A₂) ↔ (Y = E₁ ∨ Y = E₂) := by
    intro Y
    rcases hEi E₁ hE₁ hE₁X hE₁T hE₁X' with e₁ | e₁ <;>
      rcases hEi E₂ hE₂ hE₂X hE₂T hE₂X' with e₂ | e₂
    · exact absurd (e₁.trans e₂.symm) hE
    · subst e₁; subst e₂; exact Iff.rfl
    · subst e₁; subst e₂; exact Or.comm
    · exact absurd (e₁.trans e₂.symm) hE
  intro Y
  rw [← hset]
  constructor
  · rintro ⟨hTY, hlt, hmax⟩
    rcases hcls Y hTY hlt.le with rfl | rfl | rfl | rfl
    · exfalso
      rcases hmax A₁ hT₁ h₁X with h | h
      · exact h₁₂ (h.le.trans hT₂)
      · exact h₁ h
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hlt.ne
  · rintro (rfl | rfl)
    · exact ⟨hT₁, hmax₁⟩
    · exact ⟨hT₂, hmax₂⟩

end Abstract

theorem card_P1sub : Nat.card P1sub = 48 := by
  have : Fintype.card {σ : Perm (Fin 6) // InP1 σ} = 48 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_P2sub : Nat.card P2sub = 48 := by
  have : Fintype.card {σ : Perm (Fin 6) // InP2 σ} = 48 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem D6sub_le : D6sub ≤ P1sub ⊓ P2sub := fun σ hσ =>
  ⟨⟨hσ.1, hσ.2.1⟩, InD6.blocks σ hσ⟩

theorem P1_not_le_P2 : ¬ P1sub ≤ P2sub ∧ ¬ P2sub ≤ P1sub := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : InP2 (swap 0 2 : Perm (Fin 6)) := h (show InP1 (swap 0 2) by decide)
    exact absurd this (by decide)
  · have : InP1 (swap 0 4 * swap 1 5 : Perm (Fin 6)) :=
      h (show InP2 (swap 0 4 * swap 1 5) by decide)
    exact absurd this (by decide)

theorem overgroups_D6 (Y : Subgroup (Perm (Fin 6))) (hY : D6sub ≤ Y) :
    Y = D6sub ∨ Y = P1sub ∨ Y = P2sub ∨ Y = ⊤ := by
  rcases overgroup_S6 Y (fun σ hσ => hY hσ) with h | h | h
  · rcases eq_or_eq_of_index_three hY (show Y ≤ P1sub from h)
      (by rw [card_P1sub, card_D6sub]) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases eq_or_eq_of_index_three hY (show Y ≤ P2sub from h)
      (by rw [card_P2sub, card_D6sub]) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr h))

@[expose] def QA6sub : Subgroup (Perm (Fin 6)) := D6sub ⊓ alternatingGroup (Fin 6)

theorem card_QA6sub : Nat.card QA6sub = 8 := by
  have : Fintype.card {σ : Perm (Fin 6) // InD6 σ ∧ Equiv.Perm.sign σ = 1} = 8 := by
    decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_P1A6 : Nat.card ↥(P1sub ⊓ alternatingGroup (Fin 6)) = 24 := by
  have : Fintype.card {σ : Perm (Fin 6) // InP1 σ ∧ Equiv.Perm.sign σ = 1} = 24 := by
    decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_P2A6 : Nat.card ↥(P2sub ⊓ alternatingGroup (Fin 6)) = 24 := by
  have : Fintype.card {σ : Perm (Fin 6) // InP2 σ ∧ Equiv.Perm.sign σ = 1} = 24 := by
    decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem gens_mem_QA6sub : ga ∈ QA6sub ∧ gb ∈ QA6sub ∧ gc ∈ QA6sub :=
  ⟨Subgroup.mem_inf.2 ⟨show InD6 ga by decide, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    Subgroup.mem_inf.2 ⟨show InD6 gb by decide, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    Subgroup.mem_inf.2 ⟨show InD6 gc by decide, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩⟩

theorem overgroups_QA6 (Y : Subgroup (Perm (Fin 6))) (hY : QA6sub ≤ Y)
    (hYA : Y ≤ alternatingGroup (Fin 6)) :
    Y = QA6sub ∨ Y = P1sub ⊓ alternatingGroup (Fin 6) ∨ Y = P2sub ⊓ alternatingGroup (Fin 6) ∨
      Y = alternatingGroup (Fin 6) := by
  obtain ⟨ha, hb, hc⟩ := gens_mem_QA6sub
  rcases overgroup_A6 Y hYA (hY ha) (hY hb) (hY hc) with h | h | h
  · rcases eq_or_eq_of_index_three hY (show Y ≤ P1sub ⊓ alternatingGroup (Fin 6) from
      le_inf (fun y hy => h y hy) hYA) (by rw [card_P1A6, card_QA6sub]) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases eq_or_eq_of_index_three hY (show Y ≤ P2sub ⊓ alternatingGroup (Fin 6) from
      le_inf (fun y hy => h y hy) hYA) (by rw [card_P2A6, card_QA6sub]) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin.H13.A6
