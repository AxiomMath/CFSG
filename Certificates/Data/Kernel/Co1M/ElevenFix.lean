module

public import Certificates.Data.Kernel.Co1B

public section

namespace CFSG.KD.Co1ElevenFix

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2

@[expose] def decL (n : Nat) : Int :=
  bif Nat.beq (n % 2) 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int)

@[expose] noncomputable def powB (Y : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => mulK acc Y) n

@[expose] noncomputable def fixB (Y v : Nat) : Bool :=
  Nat.blt v (2 ^ 24) && Nat.beq (vmF 24 (trK 24 Y) v) v

@[expose] noncomputable def movesB (Y v : Nat) : Bool := !Nat.beq (vmF 24 (trK 24 Y) v) v

@[expose] def nodupB : List Nat → Bool
  | [] => true
  | a :: t => t.all (fun b => !Nat.beq a b) && nodupB t

@[expose] noncomputable def elevenFixOK (mem : Nat → Bool) (base : List Nat) (derivs : List (List Nat))
    (RS RIS W NF : List Nat) (U iy ie p q k n : Nat) : Bool :=
  dagOK base (derivs.map (List.map decL)) RS RIS &&
    Nat.beq (powB (getL oneK RS iy) p) oneK && Nat.beq (powB (getL oneK RS ie) q) oneK &&
    movesB (getL oneK RS ie) 1 &&
    Nat.beq (mulK (getL oneK RS ie) (getL oneK RS iy)) (mulK (getL oneK RS iy) (getL oneK RS ie)) &&
    Nat.beq W.length k &&
    pivK 24 (W.map fun v => vmF 24 (trK 24 (getL oneK RS iy)) v ^^^ v) 0 &&
    Nat.beq NF.length n && nodupB NF &&
    NF.all (fun v => fixB (getL oneK RS iy) v && !mem v) &&
    fixB (getL oneK RS iy) U && mem U

end CFSG.KD.Co1ElevenFix

end
