module

public import CFSG.RankThree.GF2n.Parrott.SpinTChecks

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinRigid

@[expose] def lV : List Nat := [0, 2]

@[expose] def lRho : List Nat := [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1]

@[expose] def lXa : List Nat := lT ++ lU ++ lV

@[expose] def bT : B8 := evalB b3 (toW lT)

@[expose] def bX : B8 := evalB b3 (toW lXa)

@[expose] def bRho : B8 := evalB b3 (toW lRho)

@[expose] def wZero : List Nat := (List.range 256).filter fun m => bapply bRho m == m

@[expose] def fixX : List Nat := (List.range 256).filter fun m => bapply bX m == m

theorem fixX_iso : ∀ m ∈ fixX, ∀ n ∈ fixX, bq m n = 0 := by decide +kernel

theorem fixT_of_fixX : ∀ m ∈ wZero, m ∈ fixX → qTab.getD m 0 = 0 → bapply bT m = m := by
  decide +kernel

theorem pair_check : ∀ m₁ ∈ wZero, ∀ mk ∈ wZero, ∀ m ∈ wZero, m ∈ fixX → qTab.getD m 0 = 0 →
    (mk ^^^ bapply bX mk) = (m₁ ^^^ bapply bT m₁) → bq mk m = 0 := by
  decide +kernel

end CFSG.RankThree.GF2n.Parrott.SpinRigid
