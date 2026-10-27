module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model
public import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.HallHigman Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.CatB

theorem pSolv3_of_solvable {X : Type} [Group X] (hX : Group.IsSolvable X) : IsPSolvable 3 X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = 3 ∨ Nat.Coprime 3 (Nat.card (↥H ⧸ T))
  by_cases h : Nat.card (↥H ⧸ T) = 3
  · exact Or.inl h
  · exact Or.inr ((Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm h))

noncomputable abbrev sig : Perm (Fin 8) := a8c * a8d

theorem cycleType_sig : sig.cycleType = {3, 3} := by
  have h1 : a8c.cycleType = {3} := by
    have : a8c = swap 1 0 * swap 1 2 := by
      show swap 0 1 * swap 1 2 = _
      rw [swap_comm]
    rw [this]
    exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType
  have h2 : a8d.cycleType = {3} := by
    have : a8d = swap 4 3 * swap 4 5 := by
      show swap 3 4 * swap 4 5 = _
      rw [swap_comm]
    rw [this]
    exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType
  have hd : Disjoint a8c a8d := by
    intro x
    revert x
    decide
  rw [show sig = a8c * a8d from rfl, hd.cycleType_mul, h1, h2]
  rfl

theorem card_cent_sig : Nat.card (Subgroup.centralizer ({sig} : Set (Perm (Fin 8)))) = 36 := by
  rw [nat_card_centralizer, cycleType_sig]
  decide

theorem solvable_cent_sig : Group.IsSolvable (Subgroup.centralizer ({sig} : Set (Perm (Fin 8)))) :=
  TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3) Nat.prime_two
    Nat.prime_three (a := 2) (b := 2) (by rw [card_cent_sig]; norm_num)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
