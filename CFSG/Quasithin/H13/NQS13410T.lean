module

public import CFSG.Quasithin.H13.A6S13227
public import CFSG.Quasithin.H13.U3L139M
public import CFSG.Quasithin.H13.NQS13410TPack

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Permutation.FinPack CFSG.Quasithin.H13.NQS134Pack

@[expose] def a6Dlist : List (Perm (Fin 6)) :=
  [1, swap 2 3 * swap 4 5, swap 0 1 * swap 4 5, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
    swap 0 2 * swap 1 3 * swap 2 3 * swap 4 5, swap 0 3 * swap 1 2 * swap 2 3 * swap 4 5,
    swap 0 3 * swap 1 2]

@[expose] def a6P2list : List (Perm (Fin 6)) :=
  [1, swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4, swap 0 1 * swap 4 5,
    swap 0 1 * swap 2 3, swap 0 1 * swap 2 4 * swap 3 5 * swap 4 5,
    swap 0 1 * swap 2 5 * swap 3 4 * swap 4 5, swap 0 2 * swap 1 3,
    swap 0 2 * swap 1 3 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 2 4 * swap 3 5,
    swap 0 2 * swap 1 3 * swap 2 5 * swap 3 4, swap 0 3 * swap 1 2 * swap 2 3 * swap 4 5,
    swap 0 3 * swap 1 2, swap 0 3 * swap 1 2 * swap 2 4 * swap 3 5,
    swap 0 3 * swap 1 2 * swap 2 5 * swap 3 4, swap 0 4 * swap 1 5 * swap 2 4 * swap 3 5,
    swap 0 4 * swap 1 5 * swap 2 5 * swap 3 4, swap 0 4 * swap 1 5,
    swap 0 4 * swap 1 5 * swap 2 3 * swap 4 5, swap 0 5 * swap 1 4 * swap 2 5 * swap 3 4,
    swap 0 5 * swap 1 4 * swap 2 4 * swap 3 5, swap 0 5 * swap 1 4,
    swap 0 5 * swap 1 4 * swap 2 3 * swap 4 5]

theorem a6D_mul : ∀ a ∈ a6Dlist, ∀ b ∈ a6Dlist, a * b ∈ a6Dlist := by decide +kernel

theorem a6D_inv : ∀ a ∈ a6Dlist, a⁻¹ ∈ a6Dlist := by decide +kernel

theorem a6P2_mul : ∀ a ∈ a6P2list, ∀ b ∈ a6P2list, a * b ∈ a6P2list := by decide +kernel

theorem a6P2_inv : ∀ a ∈ a6P2list, a⁻¹ ∈ a6P2list := by decide +kernel

theorem a6D_nodup : a6Dlist.Nodup := by decide +kernel

theorem a6P2_nodup : a6P2list.Nodup := by decide +kernel

@[expose] def a6D : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ a6Dlist}
  mul_mem' := fun {a b} ha hb => a6D_mul a ha b hb
  one_mem' := by decide
  inv_mem' := fun {a} ha => a6D_inv a ha

@[expose] def a6P2 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ a6P2list}
  mul_mem' := fun {a b} ha hb => a6P2_mul a ha b hb
  one_mem' := by decide
  inv_mem' := fun {a} ha => a6P2_inv a ha

theorem mem_a6D {σ : Perm (Fin 6)} : σ ∈ a6D ↔ σ ∈ a6Dlist := Iff.rfl

theorem mem_a6P2 {σ : Perm (Fin 6)} : σ ∈ a6P2 ↔ σ ∈ a6P2list := Iff.rfl

theorem mem_a6D_iff : ∀ σ : Perm (Fin 6), σ ∈ a6Dlist ↔ InD6 σ ∧ Perm.sign σ = 1 := by
  decide +kernel

theorem a6D_le_stab45 : ∀ σ ∈ a6Dlist, σ ∈ stab45List := by decide +kernel

theorem a6D_le_P2 : ∀ σ ∈ a6Dlist, σ ∈ a6P2list := by decide +kernel

theorem mem_stab45_iff : ∀ σ : Perm (Fin 6), σ ∈ stab45List ↔ Perm.sign σ = 1 ∧ U3.Pres45 σ := by
  decide +kernel

theorem a6_word_0 : ∀ g : Perm (Fin 6), g 0 = 0 → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
    ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ a6P2list →
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) :=
  word_of_check 0 a6Dlist a6P2list evenCodes6 a6DCodes a6P2Codes pc6_mem_even
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a6_word_1 : ∀ g : Perm (Fin 6), g 0 = 1 → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
    ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ a6P2list →
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) :=
  word_of_check 1 a6Dlist a6P2list evenCodes6 a6DCodes a6P2Codes pc6_mem_even
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a6_word_2 : ∀ g : Perm (Fin 6), g 0 = 2 → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
    ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ a6P2list →
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) :=
  word_of_check 2 a6Dlist a6P2list evenCodes6 a6DCodes a6P2Codes pc6_mem_even
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a6_word_3 : ∀ g : Perm (Fin 6), g 0 = 3 → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
    ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ a6P2list →
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) :=
  word_of_check 3 a6Dlist a6P2list evenCodes6 a6DCodes a6P2Codes pc6_mem_even
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a6_word_4 : ∀ g : Perm (Fin 6), g 0 = 4 → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
    ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ a6P2list →
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) :=
  word_of_check 4 a6Dlist a6P2list evenCodes6 a6DCodes a6P2Codes pc6_mem_even
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a6_word_5 : ∀ g : Perm (Fin 6), g 0 = 5 → Perm.sign g = 1 → ¬ (g 4 = 4 ∧ g 5 = 5) →
    ¬ (g 4 = 5 ∧ g 5 = 4) → g ∉ a6P2list →
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) :=
  word_of_check 5 a6Dlist a6P2list evenCodes6 a6DCodes a6P2Codes pc6_mem_even
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a6_word (g : Perm (Fin 6)) (hg1 : Perm.sign g = 1) (hg45 : ¬ U3.Pres45 g)
    (hg2 : g ∉ a6P2list) :
    ∃ b ∈ a6Dlist, ∃ b' ∈ a6Dlist,
      (g * b * g⁻¹ * b' * (g * b * g⁻¹) ∈ a6P2list ∧
        g * b * g⁻¹ * b' * (g * b * g⁻¹) ∉ a6Dlist) ∨
      (g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∈ a6P2list ∧
        g⁻¹ * b * g * b' * (g⁻¹ * b * g) ∉ a6Dlist) := by
  have h1 : ¬ (g 4 = 4 ∧ g 5 = 5) := fun h => hg45 (Or.inl h)
  have h2 : ¬ (g 4 = 5 ∧ g 5 = 4) := fun h => hg45 (Or.inr h)
  obtain ⟨i, hi⟩ : ∃ i, g 0 = i := ⟨_, rfl⟩
  fin_cases i
  · exact a6_word_0 g hi hg1 h1 h2 hg2
  · exact a6_word_1 g hi hg1 h1 h2 hg2
  · exact a6_word_2 g hi hg1 h1 h2 hg2
  · exact a6_word_3 g hi hg1 h1 h2 hg2
  · exact a6_word_4 g hi hg1 h1 h2 hg2
  · exact a6_word_5 g hi hg1 h1 h2 hg2

theorem card_a6D : Nat.card ↥a6D = 8 := by
  classical
  rw [← (show a6Dlist.length = 8 from rfl), ← List.toFinset_card_of_nodup a6D_nodup,
    ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [List.mem_toFinset]; rfl)

theorem card_a6P2 : Nat.card ↥a6P2 = 24 := by
  classical
  rw [← (show a6P2list.length = 24 from rfl), ← List.toFinset_card_of_nodup a6P2_nodup,
    ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [List.mem_toFinset]; rfl)

theorem a6P2_le_of {Y : Subgroup (Perm (Fin 6))} (hYA : Y ≤ alternatingGroup (Fin 6))
    (hD : a6D ≤ Y) (hY : ¬ Y ≤ stab45) : a6P2 ≤ Y := by
  have hw : ∃ w ∈ Y, w ∈ a6P2 ∧ w ∉ a6D := by
    obtain ⟨g, hgY, hgP⟩ := IsConcreteLE.not_le_iff_exists.1 hY
    have hg1 : Perm.sign g = 1 := Perm.mem_alternatingGroup.1 (hYA hgY)
    by_cases hg2 : g ∈ a6P2list
    · exact ⟨g, hgY, hg2, fun h => hgP (a6D_le_stab45 g h)⟩
    · have hg45 : ¬ U3.Pres45 g := fun h =>
        hgP ((mem_stab45_iff g).2 ⟨hg1, h⟩)
      obtain ⟨b, hb, b', hb', h | h⟩ := a6_word g hg1 hg45 hg2
      · have hx : g * b * g⁻¹ ∈ Y := mul_mem (mul_mem hgY (hD hb)) (inv_mem hgY)
        exact ⟨_, mul_mem (mul_mem hx (hD hb')) hx, h.1, h.2⟩
      · have hx : g⁻¹ * b * g ∈ Y := mul_mem (mul_mem (inv_mem hgY) (hD hb)) hgY
        exact ⟨_, mul_mem (mul_mem hx (hD hb')) hx, h.1, h.2⟩
  obtain ⟨w, hwY, hwP, hwD⟩ := hw
  have hDP : a6D ≤ a6P2 := fun g hg => a6D_le_P2 g hg
  have hDY2 : a6D ≤ Y ⊓ a6P2 := le_inf hD hDP
  have h1 := relIndex_mul_relIndex a6D (Y ⊓ a6P2) a6P2 hDY2 inf_le_right
  have h3 : a6D.relIndex a6P2 = 3 := by
    have h4 := relIndex_mul_card a6D a6P2
    rw [inf_eq_left.2 hDP, card_a6D, card_a6P2] at h4
    omega
  rw [h3] at h1
  rcases (Nat.prime_mul_iff.mp (h1 ▸ (by norm_num : Nat.Prime 3))) with ⟨-, hb⟩ | ⟨-, ha⟩
  · exact (relIndex_eq_one.mp hb).trans inf_le_left
  · exact absurd (relIndex_eq_one.mp ha (mem_inf.2 ⟨hwY, hwP⟩)) hwD

theorem act4f_e0123_of_inD6 : ∀ σ : Perm (Fin 6), InD6 σ → act4f σ e0123 = e0123 := by
  decide +kernel

theorem permAct_e45_of_inD6 : ∀ σ : Perm (Fin 6), InD6 σ → G6.permAct 6 σ e45 = e45 := by
  decide +kernel

theorem pres45_of_act4f_fix : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → U3.Pres45 σ := by
  decide +kernel

theorem pres45_of_permAct_fix : ∀ σ : Perm (Fin 6), G6.permAct 6 σ e45 = e45 → U3.Pres45 σ := by
  decide +kernel

theorem act4f_fix_of_pres45 : ∀ σ : Perm (Fin 6), U3.Pres45 σ → ∀ x : P6, InW4 x →
    (∀ τ ∈ a6Dlist, act4f τ x = x) → act4f σ x = x := by
  decide +kernel

theorem permAct_fix_of_pres45 : ∀ σ : Perm (Fin 6), U3.Pres45 σ → ∀ x : P6,
    (∀ τ ∈ a6Dlist, G6.permAct 6 τ x = x) → G6.permAct 6 σ x = x := by
  decide +kernel

end CFSG.Quasithin.H13.NQS134
