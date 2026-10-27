module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup

theorem alt_six_centralizer_cube : ∀ τ : Equiv.Perm (Fin 6), τ ^ 3 = 1 → τ ≠ 1 →
    Equiv.Perm.sign τ = 1 → ∀ κ : Equiv.Perm (Fin 6), Equiv.Perm.sign κ = 1 → κ * τ = τ * κ →
    κ ^ 3 = 1 := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup
