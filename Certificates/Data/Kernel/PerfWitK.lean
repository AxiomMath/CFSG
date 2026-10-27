module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.GH74.Generic.S45.PerfWitCheck
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.KC.PerfWitK

open CFSG.KC.Enum CFSG.KS CFSG.GH74.Generic.S45

@[expose] noncomputable def letK (G GI : Nat → Nat) : Int → Nat
  | .ofNat k => G (k - 1)
  | .negSucc k => GI k

@[expose] noncomputable def wK (n w : Nat) (G GI : Nat → Nat) (wd : List Int) : Nat :=
  wd.foldr (fun l acc => pcomp n w (mask w) (letK G GI l) acc) (pidn n w)

@[expose] noncomputable def powK (n w X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ q => pcomp n w (mask w) X q) e

@[expose] noncomputable def ordK (n w X m : Nat) : Bool :=
  Nat.beq (powK n w X m) (pidn n w) &&
    (CFSG.Sporadic.Schreier.Native.divParts m).all fun e => !Nat.beq (powK n w X e) (pidn n w)

@[expose] def commW (p : List Int × List Int) : List Int :=
  p.1 ++ p.2 ++ invWord p.1 ++ invWord p.2

@[expose] noncomputable def perfK (n w k : Nat) (G GI : Nat → Nat) (W : PerfWit) : Bool :=
  Nat.beq W.comms.length k &&
    (List.range k).all (fun i => lettersOK k (W.comms[i]!).1 && lettersOK k (W.comms[i]!).2 &&
      Nat.beq (G i) (wK n w G GI (commW W.comms[i]!))) &&
    lettersOK k W.four && ordK n w (wK n w G GI W.four) 4

end CFSG.KC.PerfWitK

end
