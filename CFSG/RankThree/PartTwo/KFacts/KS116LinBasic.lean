module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

section Perfect

theorem eq_one_of_perfect_of_comm {Γ M : Type*} [Group Γ] [CommMonoid M] (f : Γ →* M)
    {K : Subgroup Γ} (hK : ⁅K, K⁆ = K) {k : Γ} (hk : k ∈ K) : f k = 1 := by
  have hle : K ≤ f.toHomUnits.ker := by
    rw [← hK, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [mul_comm (f.toHomUnits x) (f.toHomUnits y)]
    simp [mul_assoc]
  have h1 : f.toHomUnits k = 1 := hle hk
  have h2 := congrArg Units.val h1
  simpa using h2

def permHomOfAct {M S : Type*} [Group M] (act : M → S → S) (h1 : ∀ s, act 1 s = s)
    (hmul : ∀ m m' s, act (m * m') s = act m (act m' s)) : M →* Equiv.Perm S where
  toFun m :=
    { toFun := act m
      invFun := act m⁻¹
      left_inv := fun s => by rw [← hmul, inv_mul_cancel, h1]
      right_inv := fun s => by rw [← hmul, mul_inv_cancel, h1] }
  map_one' := by
    ext s
    exact h1 s
  map_mul' m m' := by
    ext s
    exact hmul m m' s

theorem perfect_act_trivial {M S : Type*} [Group M] [Finite S] (hS : Nat.card S ≤ 4)
    (act : M → S → S) (h1 : ∀ s, act 1 s = s)
    (hmul : ∀ m m' s, act (m * m') s = act m (act m' s))
    {K : Subgroup M} (hK : ⁅K, K⁆ = K) {k : M} (hk : k ∈ K) (s : S) : act k s = s := by
  haveI : Group.IsSolvable (Equiv.Perm S) := Equiv.Perm.isSolvable hS
  set f := permHomOfAct act h1 hmul with hf
  have hKm : ⁅K.map f, K.map f⁆ = K.map f := by
    rw [← Subgroup.map_commutator, hK]
  have hbot : K.map f = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hKm
  have : f k = 1 := (Subgroup.map_eq_bot_iff _).mp hbot hk
  exact congrArg (fun e : Equiv.Perm S => e s) this

end Perfect

end CFSG.RankThree.PartTwo.KFacts.NDC

end
