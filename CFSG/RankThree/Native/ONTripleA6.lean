module

public import Certificates.Certificate8136
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.Native.ONTriple

open Equiv Equiv.Perm

theorem card_closure_sK :
    Nat.card (Subgroup.closure {g | g ∈ [sK1, sK2]}) = 360 :=
  Certificates.certificate8136.1

theorem sK_sign :
    Equiv.Perm.sign sK1 = 1 ∧ Equiv.Perm.sign sK2 = 1 :=
  Certificates.certificate8136.2.1

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem closure_sK_eq_alt :
    Subgroup.closure {g | g ∈ [sK1, sK2]} = alternatingGroup (Fin 6) := by
  have hle : Subgroup.closure {g | g ∈ [sK1, sK2]} ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    rcases hg with rfl | rfl
    · exact Equiv.Perm.mem_alternatingGroup.2 sK_sign.1
    · exact Equiv.Perm.mem_alternatingGroup.2 sK_sign.2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_alt_six, card_closure_sK]

theorem d1_check
    (j : ℕ) (hj : j < 2) : ∀ t : Perm (Fin 6), Equiv.Perm.sign t = 1 →
    t ^ 4 = 1 → t ≠ 1 →
      (∃ m < 3, ∃ i < 3, t = sV j m i) ∨ (cand1 (sY j) t).any (fun u => u ^ 4 != 1) :=
  Certificates.certificate8136.2.2.1 j hj

theorem d2_check
    (j : ℕ) (hj : j < 2) (m : ℕ) (hm : m < 3) : ∀ s : Perm (Fin 6),
    Equiv.Perm.sign s = 1 → s ^ 4 = 1 → s ≠ 1 → (∀ i < 3, s ≠ sV j m i) →
      (cand2 (sY j) s [1, sV j m 0, sV j m 1, sV j m 2]).any (fun u => u ^ 4 != 1) :=
  Certificates.certificate8136.2.2.2 j hj m hm

theorem dV_check (j : ℕ) (hj : j < 2) (m : ℕ) (hm : m < 3) : ∀ i < 3, ∀ i' < 3,
    sV j m i' = sV j m i ∨ sV j m i' = cj (sY j) (sV j m i) ∨
      sV j m i' = cj (sY j) (cj (sY j) (sV j m i)) := by
  interval_cases j <;> interval_cases m <;> decide

end CFSG.RankThree.Native.ONTriple
