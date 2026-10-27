module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Mathlib.GroupTheory.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG

@[expose] def GL12Data (S : Type) [Group S] : Prop :=
  ∃ (n : ℕ) (X : Type) (_ : Group X) (_ : Finite X)
    (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) (K : Subgroup X) (_ : K.Normal),
    n ≤ 12 ∧ Group.IsPerfect X ∧ ρ ≠ 1 ∧ ρ.ker ≤ K ∧ Odd (Nat.card K) ∧
      Nonempty (X ⧸ K ≃* S) ∧
      ∀ t : X, orderOf t = 2 →
        Nat.card {v : Fin n → ZMod 3 //
          Matrix.mulVec ((ρ t : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
            Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ 4

end CFSG.RankThree.PartTwo.Sec13.K135SF
