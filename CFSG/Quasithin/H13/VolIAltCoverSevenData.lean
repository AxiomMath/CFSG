module

public import CFSG.Quasithin.H13.VolIAltCover
import CFSG.Quasithin.H13.VolIAltCoverSevenDataK

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

@[expose] def a7c012 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a7c234 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 2 3 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a7c456 : ↥(alternatingGroup (Fin 7)) :=
  ⟨swap 4 5 * swap 5 6, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a7s : ↥(alternatingGroup (Fin 7)) := a7c456 * a7c234 * (a7c456 * a7c456)

theorem a7c012_pow : a7c012 ^ 3 = 1 := by decide

theorem a7c234_pow : a7c234 ^ 3 = 1 := by decide

theorem a7c456_pow : a7c456 ^ 3 = 1 := by decide

theorem alt7_words : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 5 = 5 →
    (σ : Perm (Fin 7)) 6 = 6 → IsWord6 a7c012 a7c234 σ :=
  A7WordsK.words (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def a7reps5 : List ↥(alternatingGroup (Fin 7)) :=
  [1, a7c012, a7c012 * a7c012, a7c234, a7c234 * a7c234]

theorem a7reps5_fix : ∀ h ∈ a7reps5, (h : Perm (Fin 7)) 5 = 5 ∧ (h : Perm (Fin 7)) 6 = 6 := by
  intro h hh
  simp only [a7reps5, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem alt7_cosets5 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 6 = 6 →
    (σ : Perm (Fin 7)) 5 = 5 ∨ ∃ h ∈ a7reps5,
      (((h * a7s)⁻¹ * σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 5 = 5 := by
  intro σ h6
  have hv : ∀ v : Fin 7, v ≠ 6 → v = 5 ∨ ∃ h ∈ a7reps5,
      ((h * a7s : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 5 = v := by
    decide +kernel
  have h5 : (σ : Perm (Fin 7)) 5 ≠ 6 := by
    intro h
    have h56 := (σ : Perm (Fin 7)).injective (h.trans h6.symm)
    exact absurd h56 (by decide)
  rcases hv _ h5 with h | ⟨h, hh, he⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, hh, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, Perm.inv_eq_iff_eq, he]

theorem a7s_six : (a7s : Perm (Fin 7)) 6 = 6 := by decide

theorem evenOn_seven_012_card : (evenOn (0 : Fin 7) 1 2).card = 4 := by decide

theorem evenOn_seven_234_card : (evenOn (2 : Fin 7) 3 4).card = 4 := by decide

theorem evenOn_seven_456_card : (evenOn (4 : Fin 7) 5 6).card = 4 := by decide

theorem comm_mem_evenOn_seven_012 : ∀ m : PermMod 7,
    permAct 7 (a7c012 : Perm (Fin 7)) m * m⁻¹ ∈ evenOn 0 1 2 := by
  decide +kernel

theorem comm_mem_evenOn_seven_234 : ∀ m : PermMod 7,
    permAct 7 (a7c234 : Perm (Fin 7)) m * m⁻¹ ∈ evenOn 2 3 4 := by
  decide +kernel

theorem comm_mem_evenOn_seven_456 : ∀ m : PermMod 7,
    permAct 7 (a7c456 : Perm (Fin 7)) m * m⁻¹ ∈ evenOn 4 5 6 := by
  decide +kernel

theorem allOnes_seven_not_mem : allOnes 7 ∉ coreMod 7 := by
  rw [mem_coreMod]
  decide

theorem card_coreMod_seven : Nat.card (coreMod 7) = 64 := by
  have h : (coreMod 7 : Set (PermMod 7)) =
      ↑(Finset.univ.filter fun x : PermMod 7 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

end CFSG.Quasithin.H13.VolI
