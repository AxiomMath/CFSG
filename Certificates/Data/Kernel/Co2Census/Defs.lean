module

public import Certificates.Data.Kernel.Co2InvS
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Co2Census

open CFSG.KC.Co2InvS

@[expose] def fld20 (r j : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.mul 20 j)) 1048575

@[expose] def rtOf (IX : Nat → Nat) (i : Nat) : Nat := fld20 (IX i) 0

@[expose] noncomputable def treeK (step : Nat → Nat → Nat) (ngen N : Nat) (P IX : Nat → Nat)
    (i : Nat) : Bool :=
  letB (IX i) fun r => letB (fld20 r 0) fun rt =>
    Nat.blt rt N && Nat.beq (fld20 (IX rt) 0) rt &&
      (Nat.beq rt i || (letB (fld20 r 1) fun pa => letB (fld20 r 2) fun la =>
        Nat.blt pa i && Nat.beq (fld20 (IX pa) 0) rt && Nat.blt la ngen &&
          Nat.beq (P i) (step la (P pa)))) &&
      letB (fld20 r 3) fun so => Nat.blt so N &&
        (!Nat.blt (i + 1) N || Nat.blt (P so) (P (fld20 (IX (i + 1)) 3)))

@[expose] noncomputable def closK (step : Nat → Nat → Nat) (ngen N : Nat) (P IX : Nat → Nat)
    (i : Nat) : Bool :=
  letB (IX i) fun r => (List.range ngen).all fun l => letB (fld20 r (4 + l)) fun t =>
    Nat.blt t N && Nat.beq (fld20 (IX t) 0) (fld20 r 0) && Nat.beq (step l (P i)) (P t)

@[expose] noncomputable def posK (test : Nat → Bool) (X P POS : Nat → Nat) (N j : Nat) : Bool :=
  !test (X j) || (Nat.blt (POS j) N && Nat.beq (P (POS j)) (X j))

@[expose] noncomputable def conjStep (G GI : Nat → Nat) (l x : Nat) : Nat := mulV (mulV (G l) x) (GI l)

@[expose] noncomputable def rmStep (G : Nat → Nat) (l x : Nat) : Nat := mulV x (G l)

@[expose] noncomputable def rootCount (IX : Nat → Nat) (N hi k : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow N hi fun i => nIf(Nat.beq (rtOf IX i) k, 1, 0)

end CFSG.KC.Co2Census

end
