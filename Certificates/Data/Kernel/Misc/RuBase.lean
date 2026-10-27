module

public import Certificates.Data.Kernel.Misc.RuInv

public section

namespace CFSG.KC.Misc.RuBase

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv

@[expose] noncomputable def packL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun s _ ih => Nat.lor s (Nat.shiftLeft ih 48720)) L

@[expose] noncomputable def getS (SS j : Nat) : Nat :=
  fld(SS, Nat.mul (nat_lit 48720) j, mask (nat_lit 48720))

@[expose] noncomputable def ptK (H HI : Nat → Nat) (b : Nat) (ss : List (List Int))
    (fs : List (Nat × List Int)) : Bool :=
  strictB (packL (ss.map (wordP H HI))) (fun SS =>
    bAnd(allN ss.length (fun j => Nat.beq (apP (getS SS j) b) b),
    bAnd(allN (nat_lit 4060) (fun i =>
        bIf(fs.any (fun f => Nat.beq f.1 i), true,
          bIf(allN ss.length (fun j => Nat.beq (apP (getS SS j) i) i), false, true))),
      fs.all (fun f => strictB (wordP H HI f.2) (fun T =>
        bAnd(Nat.beq (apP T b) f.1, Nat.beq (apP T f.1) b))))))

end CFSG.KC.Misc.RuBase

end
