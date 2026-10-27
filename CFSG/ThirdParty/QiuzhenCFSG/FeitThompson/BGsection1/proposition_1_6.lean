module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_5

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

theorem CFSG.proposition_1_6_a {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    fixedPointSubgroup A G ⊔ commutatorAction (A := A) (G := G) = ⊤ := by
  simpa using
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := G) (A := A) hsolv hcoprime

theorem CFSG.proposition_1_6_b {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    commutatorAction₂ (A := A) (G := G) = commutatorAction (A := A) (G := G) := by
  simpa using
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := G) (A := A) hsolv hcoprime

theorem CFSG.proposition_1_6_c {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    commutatorAction₂ (A := A) (G := G) = ⊥ → ActsTrivially (A := A) (G := G) := by
  exact
    actsTrivially_of_commutatorAction₂_eq_bot_of_solvable_coprime
      (G := G) (A := A) hsolv hcoprime

theorem CFSG.proposition_1_6_d {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    IsMulCommutative G → IsCompl (fixedPointSubgroup A G) (commutatorAction (A := A) (G := G)) := by
  simpa using
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := G) (A := A) hsolv hcoprime

theorem CFSG.proposition_1_6_e {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    IsMulCommutative G →
      (∀ g : G, Nat.Prime (orderOf g) → g ∈ fixedPointSubgroup A G) → ActsTrivially (A := A) (G := G) := by
  exact
    actsTrivially_of_isMulCommutative_and_prime_order_mem_fixedPointSubgroup
      (G := G) (A := A) hsolv hcoprime


end
