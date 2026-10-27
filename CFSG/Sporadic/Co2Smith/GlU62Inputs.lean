module

public import CFSG.Sporadic.Co2Smith.GlDataRootInputs
public import CFSG.Sporadic.Co2Smith.GlU62Data
public import CFSG.Sporadic.Co2Smith.GlU62Data2

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def u62QNFR (c : Nat × Nat × Nat × Nat × Nat) : Array Nat :=
  mulRows 22 (mulRows 22 (mulRows 22 (mulRows 22 (if c.1 == 1 then glZ else idRows 22)
    (glRootRows 0 c.2.1)) (glRootRows 1 c.2.2.1)) (glRootRows 2 c.2.2.2.1))
    (glRootRows 3 c.2.2.2.2)

@[expose] def u62QOK : Bool :=
  (List.range 8).all fun j => glRows.getD (j + 1) #[] == u62QNFR (u62QNF.getD j (0, 0, 0, 0, 0))

@[expose] def u62CommOK : Bool :=
  validM (mulRows 22 glZ glX61) && validM (mulRows 22 glX61 glZ) && !commRows glZ glX61

@[expose] def u62L1Ids : List (Nat × Nat) :=
  [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (5, 2),
    (10, 1), (10, 2), (11, 1), (11, 2), (12, 1), (13, 1), (14, 1), (16, 1), (17, 1)]

@[expose] def u62L1OK : Bool :=
  glChainOK u62L1Words u62L1Base u62L1W 26542080 &&
    u62L1Words.all (fun w => glMaps (glR w) 80 80 && commRows (glR w) glZ) &&
    u62L1Words.length == 22 && u62L1Words.getD 21 [] == glD0hWord &&
    (List.range 21).all fun i => glR (u62L1Words.getD i []) ==
      glRootRows (u62L1Ids.getD i (0, 0)).1 (u62L1Ids.getD i (0, 0)).2

@[expose] def u62InvOK (ws : List (List Nat)) : Bool :=
  ws.all fun w => mulRows 22 (glR w) (glR w) == idRows 22 && glMaps (glR w) 80 80

@[expose] def u62WR (G : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldl (fun a j => mulRows 22 a (G.getD j (idRows 22))) (idRows 22)

@[expose, noinline] def u62G1R : Array (Array Nat) := u62G1Words.toArray.map glR

@[expose, noinline] def u62OrbR : Array (Array Nat) :=
  u62Orb.map fun w => mulRows 22 (mulRows 22 (u62WR u62G1R w) glZ) (u62WR u62G1R w.reverse)

@[expose] def u62DistOK (n : Nat) (O : Array (Array Nat)) : Bool :=
  O.size == n && O.all validM &&
    (List.range n).all fun i => (List.range i).all fun k => O.getD i #[] != O.getD k #[]

@[expose] def u62OrbOK : Bool := u62InvOK u62G1Words && u62DistOK 693 u62OrbR

@[expose, noinline] def u62C1R : Array (Array Nat) := u62C1Words.toArray.map glR

@[expose, noinline] def u62C1E : Array (Array Nat) := u62C1.map (u62WR u62C1R)

@[expose] def u62C1Frame : List Nat := [0, 3, 1, 4, 2, 5]

@[expose] def u62C1OK : Bool :=
  u62InvOK u62C1Words && u62C1Words.all (fun w => w.all (glC0Let.contains ·)) &&
    u62DistOK 1296 u62C1E && u62C1Words.length == 8 && u62C1Words.getD 6 [] == glD0hWord &&
    u62C1Words.getD 7 [] == glD1hWord &&
    (List.range 6).all fun j => glR (u62C1Words.getD j []) == glLongRows (u62C1Frame.getD j 0)

@[expose] def u62OK : Bool := u62QOK && u62CommOK && u62L1OK && u62OrbOK && u62C1OK

end CFSG.Sporadic.Co2Smith.Native
