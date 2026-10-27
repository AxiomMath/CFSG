module

public import Certificates.Data.GMS78RuQCheck

public section

namespace CFSG.GMS78RuS

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

@[expose] def dCodeTab : List Lin8 :=
  [(1, 2, 4), (1, 3, 4), (1, 3, 7), (1, 2, 7), (1, 2, 5), (1, 3, 5), (1, 3, 6), (1, 2, 6)]

@[expose] def dCode (d : Fin 8) : Lin8 := dCodeTab.getD d.val linId

@[expose] def dMul (d e : Fin 8) : Fin 8 :=
  ⟨2 * ((if d.val % 2 = 0 then d.val / 2 + e.val / 2 else d.val / 2 + 4 - e.val / 2) % 4) +
    (d.val + e.val) % 2, by omega⟩

@[expose] def dOvf (d e : Fin 8) : Bool :=
  if d.val % 2 = 0 then decide (4 ≤ d.val / 2 + e.val / 2) else decide (d.val / 2 < e.val / 2)

@[expose] def fin8Of (j : Nat) : Fin 8 := ⟨j % 8, Nat.mod_lt _ (by decide)⟩

@[expose] def sBasis : List Nat := [16, 48, 117, 222, 210, 243, 188, 20]

@[expose] def sMaskN (c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sMaskN c n ^^^ (if c.testBit n then sBasis.getD n 0 else 0)

@[expose] def sMask (c : Nat) : Nat := sMaskN c 8

@[expose] def cOf (m : Nat) : Nat := maskApply [51, 255, 129, 153, 1, 3, 180, 90] m

@[expose] def gamN (c c' : Nat) : Nat → Fin 8
  | 0 => 0
  | n + 1 =>
    gamN c c' n ^^^ (if c.testBit n then bC (sBasis.getD n 0) (sMaskN c' n) else 0)

@[expose] def gam (c c' : Nat) : Fin 8 := gamN c c' 8

@[expose] def dPartN (d : Fin 8) (c : Nat) : Nat → Nat × Fin 8
  | 0 => (0, 0)
  | n + 1 =>
    if c.testBit n then
      ((dPartN d c n).1 ^^^ 2 ^ (dMul d (fin8Of n)).val,
        (dPartN d c n).2 ^^^ gam (dPartN d c n).1 (2 ^ (dMul d (fin8Of n)).val))
    else dPartN d c n

@[expose] def dPart (d : Fin 8) (c : Nat) : Nat × Fin 8 := dPartN d c 8

@[expose] def sMul (ε : Bool) (p q : Nat × Fin 8 × Fin 8) : Nat × Fin 8 × Fin 8 :=
  (p.1 ^^^ (dPart p.2.2 q.1).1,
    p.2.1 ^^^ linApply (dCode p.2.2) q.2.1 ^^^ (dPart p.2.2 q.1).2 ^^^
      gam p.1 (dPart p.2.2 q.1).1 ^^^ (if ε && dOvf p.2.2 q.2.2 then 1 else 0),
    dMul p.2.2 q.2.2)

end CFSG.GMS78RuS
