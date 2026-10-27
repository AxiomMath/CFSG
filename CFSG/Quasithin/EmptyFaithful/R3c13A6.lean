module

public import CFSG.Quasithin.EmptyFaithful.R3c13Gen
public import CFSG.Quasithin.EmptyFaithful.S143A6Nat

public section

namespace CFSG.Quasithin.R3c13

open Equiv Equiv.Perm

section A6

@[expose] def a6x0 : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def a6p : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 4 5, swap 2 3 * swap 4 5, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

set_option maxRecDepth 100000 in
theorem a6_comm_x0 : ∀ y : Perm (Fin 6), sign y = 1 → y * y = 1 → y ≠ 1 → y ≠ a6x0 →
    y * a6x0 = a6x0 * y →
      y = swap 0 1 * swap 4 5 ∨ y = swap 2 3 * swap 4 5 ∨ y = swap 0 2 * swap 1 3 ∨
        y = swap 0 3 * swap 1 2 := by
  unfold a6x0
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6_cent : ∀ u ∈ a6p, ∀ g : Perm (Fin 6), g * a6x0 = a6x0 * g → g * u = u * g →
    sign g = 1 → g = 1 ∨ g = a6x0 ∨ g = u ∨ g = a6x0 * u := by
  unfold a6x0 a6p
  decide +kernel

theorem a6x0_mem : a6x0 ∈ alternatingGroup (Fin 6) := by
  rw [mem_alternatingGroup]
  unfold a6x0
  decide

@[expose] def a6c1 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a6c2 : alternatingGroup (Fin 6) :=
  ⟨swap 2 3 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a6c3 : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a6c4 : alternatingGroup (Fin 6) :=
  ⟨swap 0 3 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

theorem kleinSelfCent_alt6 : KleinSelfCent (alternatingGroup (Fin 6)) := by
  refine kleinSelfCent_of_conj (⟨a6x0, a6x0_mem⟩ : alternatingGroup (Fin 6)) ?_
    [a6c1, a6c2, a6c3, a6c4] ?_ ?_ ?_
  · intro h
    have := congrArg Subtype.val h
    revert this
    unfold a6x0
    decide
  · intro a ha1 ha2
    obtain ⟨ρ, hρA, hρ⟩ := S143.alt6_invol_conj (a : Perm (Fin 6)) a6x0 a.2 a6x0_mem
      (fun h => ha1 (Subtype.ext h)) (by unfold a6x0; decide) (congrArg Subtype.val ha2)
      (by unfold a6x0; decide)
    refine ⟨⟨ρ, hρA⟩, Subtype.ext ?_⟩
    show ρ * (a : Perm (Fin 6)) = a6x0 * ρ
    rw [← hρ]
    group
  · intro y hy2 hy1 hya hyc
    have h := a6_comm_x0 (y : Perm (Fin 6)) (mem_alternatingGroup.mp y.2)
      (congrArg Subtype.val hy2) (fun h => hy1 (Subtype.ext h)) (fun h => hya (Subtype.ext h))
      (congrArg Subtype.val hyc)
    rcases h with h | h | h | h
    · have : y = a6c1 := Subtype.ext h
      simp [this]
    · have : y = a6c2 := Subtype.ext h
      simp [this]
    · have : y = a6c3 := Subtype.ext h
      simp [this]
    · have : y = a6c4 := Subtype.ext h
      simp [this]
  · intro u hu g hg0 hgu
    have hu' : (u : Perm (Fin 6)) ∈ a6p := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> simp [a6p, a6c1, a6c2, a6c3, a6c4]
    have h := a6_cent (u : Perm (Fin 6)) hu' (g : Perm (Fin 6)) (congrArg Subtype.val hg0)
      (congrArg Subtype.val hgu) (mem_alternatingGroup.mp g.2)
    rcases h with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

end A6

theorem sylowKleinSelfCent_of_alt6 {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 6)) :
    SylowKleinSelfCent X :=
  (kleinSelfCent_alt6.map φ.symm).sylow

end CFSG.Quasithin.R3c13
