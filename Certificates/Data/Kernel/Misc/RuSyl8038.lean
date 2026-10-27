module

public import Certificates.Data.Kernel.PkPow

public section

namespace CFSG.KC.RuSyl8038

open CFSG.KC.Enum CFSG.KC.PkPow CFSG.KS

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 4060) (nat_lit 12) (mask (nat_lit 12)) p q

@[expose] noncomputable def nz7 (p : Nat) : Bool :=
  bIf(Nat.beq (Nat.mod (nfix (nat_lit 4060) (nat_lit 12) p) (nat_lit 7)) (nat_lit 0), false, true)

@[expose] noncomputable def row (A Z Z2 : Nat) : Bool :=
  bAnd(nz7 A, bAnd(nz7 (pc A Z), nz7 (pc A Z2)))

@[expose] noncomputable def wchk (W I : Nat) : Bool :=
  strictB (ppw (nat_lit 4060) (nat_lit 12) W (nat_lit 7)) (fun W7 =>
    bAnd(Nat.beq W7 I, Nat.beq (nfix (nat_lit 4060) (nat_lit 12) W) (nat_lit 0)))

@[expose] noncomputable def core8038 (U H HI W : Nat) : Bool :=
  strictB (ppw (nat_lit 4060) (nat_lit 12) U (nat_lit 4)) (fun X =>
  strictB (pc H X) (fun HX =>
  strictB (pc HX HI) (fun Y =>
  strictB (pc X X) (fun X2 =>
  strictB (pc Y Y) (fun Y2 =>
  strictB (pc X Y) (fun XY =>
  strictB (pc XY X2) (fun XYX =>
  strictB (pc XYX Y2) (fun Z =>
  strictB (pc Z Z) (fun Z2 =>
  strictB (pidn (nat_lit 4060) (nat_lit 12)) (fun I =>
  bAnd(Nat.beq (pc X X2) I,
  bAnd(Nat.beq (pc Y Y2) I,
  bAnd(Nat.beq (pc Z X) (pc X Z),
  bAnd(Nat.beq (pc Z Y) (pc Y Z),
  bAnd(nz7 Z, bAnd(nz7 Z2,
  bAnd(row X Z Z2, bAnd(row X2 Z Z2, bAnd(row Y Z Z2, bAnd(row Y2 Z Z2,
  bAnd(row XY Z Z2,
  bAnd(strictB (pc X Y2) (fun A => row A Z Z2),
  bAnd(strictB (pc X2 Y) (fun A => row A Z Z2),
  bAnd(strictB (pc X2 Y2) (fun A => row A Z Z2),
  wchk W I))))))))))))))))))))))))

@[expose] def uW : List Int := [-2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1]

@[expose] def hW : List Int :=
  [2, 1, 2, 2, 1, 2, 2, -1, 2, 1, -2, -2, -1, -2, 1, -2, -2, 1, 2, 2, -1, -2]

@[expose] def hWI : List Int :=
  [2, 1, -2, -2, -1, 2, 2, -1, 2, 1, 2, 2, -1, -2, 1, -2, -2, -1, -2, -2, -1, -2]

@[expose] def wW : List Int := [1, 2, 2, 1, 2, 2]

end CFSG.KC.RuSyl8038

end
