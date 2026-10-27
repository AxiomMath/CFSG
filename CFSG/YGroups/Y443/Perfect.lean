module

public import CFSG.YGroups.Y443.Basic
public import CFSG.YGroups.Y443.OddInvolutionDiagram
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443ArmLength
  MonsterY443Derived)

namespace Y443

theorem armLength_pos : ∀ j : Fin 3, 0 < monsterY443ArmLength j := by decide

theorem armLength_ge_three : ∀ j : Fin 3, 3 ≤ monsterY443ArmLength j := by decide

@[expose] def terminal (j : Fin 3) : MonsterY443Gen :=
  some ⟨j, ⟨monsterY443ArmLength j - 1, Nat.sub_lt (armLength_pos j) Nat.one_pos⟩⟩

theorem terminal_commute_none (k : Fin 3) :
    Commute (PresentedGroup.of (terminal k) : MonsterY443) (PresentedGroup.of none) := by
  refine gen_commute_of_nonadj (by simp [terminal]) ?_
  intro h
  have h' : monsterY443ArmLength k - 1 = 0 := h
  have := armLength_ge_three k
  omega

theorem terminal_commute_node {k i : Fin 3} (hki : k ≠ i) (j : Fin (monsterY443ArmLength i)) :
    Commute (PresentedGroup.of (terminal k) : MonsterY443) (PresentedGroup.of (some ⟨i, j⟩)) := by
  refine gen_commute_of_nonadj ?_ ?_
  · intro h
    have h' : (⟨k, _⟩ : Σ i : Fin 3, Fin (monsterY443ArmLength i)) = ⟨i, j⟩ := Option.some.inj h
    exact hki (congrArg Sigma.fst h')
  · rintro ⟨h, -⟩
    exact hki h

theorem succ_ne (i : Fin 3) : i + 1 ≠ i := by
  revert i
  decide

theorem exists_commute_adj {s t : MonsterY443Gen} (h : MonsterY443Adj s t) :
    ∃ k : MonsterY443Gen, Commute (PresentedGroup.of k : MonsterY443) (PresentedGroup.of s) ∧
      Commute (PresentedGroup.of k : MonsterY443) (PresentedGroup.of t) := by
  rcases s with _ | ⟨i, j⟩ <;> rcases t with _ | ⟨i', j'⟩
  · exact absurd h id
  · exact ⟨terminal (i' + 1), terminal_commute_none _, terminal_commute_node (succ_ne i') j'⟩
  · exact ⟨terminal (i + 1), terminal_commute_node (succ_ne i) j, terminal_commute_none _⟩
  · obtain ⟨hi, -⟩ := h
    subst hi
    exact ⟨terminal (i + 1), terminal_commute_node (succ_ne i) j,
      terminal_commute_node (succ_ne i) j'⟩

end Y443

theorem y443_commutator_commutator :
    ⁅commutator MonsterY443, commutator MonsterY443⁆ = commutator MonsterY443 :=
  OddInvolutionDiagram.commutator_commutator_eq Y443.graph PresentedGroup.of Y443.graph_connected
    (PresentedGroup.closure_range_of _) Y443.gen_mul_self
    (fun _ _ h => ⟨3, by decide, Y443.gen_pair_adj h⟩) (fun _ _ h => Y443.exists_commute_adj h)

theorem y443_derived_commutator_eq :
    ⁅MonsterY443Derived, MonsterY443Derived⁆ = MonsterY443Derived :=
  y443_commutator_commutator

theorem y443_derived_isPerfect : Group.IsPerfect MonsterY443Derived :=
  Subgroup.isPerfect_iff.2 y443_derived_commutator_eq

theorem y443_derived_commutator_eq_top : commutator MonsterY443Derived = ⊤ :=
  Group.isPerfect_def.1 y443_derived_isPerfect

theorem y443_derived_hom_trivial {A : Type*} [CommGroup A] (f : MonsterY443Derived →* A) :
    f = 1 := by
  have h := Abelianization.commutator_subset_ker f
  rw [y443_derived_commutator_eq_top] at h
  ext x
  exact MonoidHom.mem_ker.1 (h (Subgroup.mem_top x))

end CFSG.YGroups
