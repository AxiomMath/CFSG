module

public import CFSG.RankThree.GF2n.Parrott.SpinTChecks

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinRigid

@[expose] def bUT : B8 := bmul (evalB b3 (toW lU)) (evalB b3 (toW lT))

@[expose] def tUT : List Nat := tcomp (evalT t3 (toW lU)) (evalT t3 (toW lT))

@[expose] def lHbadS : List Nat := [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] def lHbadA : List Nat := [1, 1, 1, 0, 1, 0, 2, 1]

@[expose] def bHbadS : B8 := evalB b3 (toW lHbadS)

@[expose] def bHbadA : B8 := evalB b3 (toW lHbadA)

@[expose] def hbadW : List Nat :=
  [0, 4, 26, 30, 64, 68, 90, 94, 128, 132, 154, 158, 192, 196, 218, 222]

@[expose] def hbadF (m : Nat) : Nat := bq m (bapply bHbadS (bapply bUT m ^^^ m))

@[expose] def hbadTrans : List (List Nat) :=
  [[], [1, 0, 1, 1, 1, 0, 1, 0, 1, 2], [1, 1, 0, 1, 0, 1, 2, 1, 0, 1], [1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2], [2], [2, 1, 0, 2, 1, 1, 0, 1, 2, 1],
    [1, 0, 2, 1, 1, 0, 1, 2, 1], [1, 1, 1, 0, 1, 0, 2, 1, 2], [1, 0, 2, 1, 1, 0, 1, 2, 1, 2],
    [1, 1, 1, 0, 1, 0, 2, 1], [2, 1, 0, 2, 1, 1, 0, 1, 2, 1, 2]]

@[expose] def hbadBasis : List Nat := [4, 26, 64, 128]

@[expose] def hbadRestr (A : B8) : List Nat := hbadBasis.map fun m => bapply A m

theorem hbadW_spec : ∀ m < 256, (m ∈ hbadW ↔ bapply bUT m = m) := by
  decide +kernel

theorem hbadW_length : hbadW.length = 16 := by
  decide +kernel

theorem hbadW_nodup : hbadW.Nodup := by
  decide +kernel

theorem hbadW_lt : ∀ m ∈ hbadW, m < 256 := by
  decide +kernel

theorem hbadW_im : ∀ m ∈ hbadW, ∃ n < 256, bapply bUT n ^^^ n = m := by
  decide +kernel

theorem hbadW_q : ∀ m ∈ hbadW, qTab.getD m 0 = 0 := by
  decide +kernel

theorem hbadS_sum : ∀ m ∈ hbadW, bapply bHbadS (bapply bHbadS m) ^^^ bapply bHbadS m ^^^ m = 0 := by
  decide +kernel

theorem hbadA_check : ∀ m < 256, hbadF m = 1 →
    bapply bUT (m ^^^ bapply bHbadA m) ^^^ (m ^^^ bapply bHbadA m) ≠ 0 ∧
      hbadF (m ^^^ bapply bHbadA m) = 0 := by
  decide +kernel

theorem hbadTrans_length : hbadTrans.length = 12 := by
  decide +kernel

theorem hbadTrans_comm : ∀ w ∈ hbadTrans,
    tcomp (evalT t3 (toW w)) tUT = tcomp tUT (evalT t3 (toW w)) := by
  decide +kernel

theorem hbadTrans_distinct : (hbadTrans.map fun w => hbadRestr (evalB b3 (toW w))).Nodup := by
  decide +kernel

theorem hbadBasis_sub : ∀ m ∈ hbadBasis, m ∈ hbadW := by
  decide +kernel

theorem hbadS_comm : tcomp (evalT t3 (toW lHbadS)) tUT = tcomp tUT (evalT t3 (toW lHbadS)) := by
  decide +kernel

theorem hbadA_comm : tcomp (evalT t3 (toW lHbadA)) tUT = tcomp tUT (evalT t3 (toW lHbadA)) := by
  decide +kernel

theorem hbadS_cube : tpow (evalT t3 (toW lHbadS)) 3 = tone := by
  decide +kernel

theorem hbadS_ne : evalT t3 (toW lHbadS) ≠ tone := by
  decide +kernel

end CFSG.RankThree.GF2n.Parrott.SpinRigid
