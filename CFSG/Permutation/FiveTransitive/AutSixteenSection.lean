module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG

namespace FiveTransitive.AutSixteenSection

private theorem eq_top_of_index_le_four
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (B : Subgroup G) (hB : B.index ≤ 4) : B = ⊤ := by
  classical
  let f := MulAction.toPermHom G (G ⧸ B)
  let : Group.IsSolvable (Equiv.Perm (G ⧸ B)) :=
    Equiv.Perm.isSolvable hB
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    rcases subsingleton_or_nontrivial f.range with h | h
    · exact h
    · exact False.elim (Group.IsPerfect.not_isSolvable f.range inferInstance)
  have hf (g : G) : f g = 1 := by
    exact congrArg Subtype.val (@Subsingleton.elim f.range hsub ⟨f g, g, rfl⟩ 1)
  apply top_unique
  intro g _
  have heq : (g : G ⧸ B) = ((1 : G) : G ⧸ B) := by
    have h := congrArg (fun p : Equiv.Perm (G ⧸ B) => p ((1 : G) : G ⧸ B)) (hf g)
    simpa [f, MulAction.toPermHom_apply, MulAction.Quotient.smul_mk] using h
  have hmem := QuotientGroup.eq.mp heq.symm
  simpa using hmem

private theorem not_perfect_seven : ¬ Group.IsPerfect (Equiv.Perm (Fin 7)) := by
  intro hp
  let := hp
  have h := Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm (Fin 7) →* ℤˣ)
    (Group.IsPerfect.mem_commutator (g := Equiv.swap (0 : Fin 7) 1))
  have hsign : Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1) = 1 := h
  norm_num [Equiv.Perm.sign_swap] at hsign

theorem no_surjection
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hG : Nat.card G = 20160) (B : Subgroup G)
    (f : B →* Equiv.Perm (Fin 7)) : ¬ Function.Surjective f := by
  intro hf
  have hdvd := Subgroup.card_dvd_of_surjective hf
  have hcard : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  rw [hcard] at hdvd
  have hBcard : 5040 ≤ Nat.card B := Nat.le_of_dvd Nat.card_pos hdvd
  have hmul := B.card_mul_index
  rw [hG] at hmul
  have hindex : B.index ≤ 4 := by nlinarith
  have htop := eq_top_of_index_le_four B hindex
  let : Group.IsPerfect B := by rw [htop]; exact Group.IsPerfect.top_iff.mpr inferInstance
  exact not_perfect_seven (Group.IsPerfect.ofSurjective hf)

end FiveTransitive.AutSixteenSection

end CFSG
