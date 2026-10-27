module

public import Certificates.Data.Kernel.Odd87CCK
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.J2ModelData
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.KC.J2ModelK

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CFSG.KC.Misc.ArrEnum CFSG.KC.Odd87CCK
open CFSG.Quasithin.Kleidman.ThreeLocal.J2Model

variable (n w : Nat)

@[expose] noncomputable def genK (A B : Nat) (z : ℤ) : Nat :=
  if z = 1 then A else if z = -1 then pinv n w A else if z = 2 then B else pinv n w B

@[expose] noncomputable def uK (A B k : Nat) : Nat := pword n w (genK n w A B) (uWord2 k)

@[expose] noncomputable def letK (A B : Nat) (z : ℤ) : Nat :=
  if 0 < z then uK n w A B (z - 1).toNat else pinv n w (uK n w A B (-z - 1).toNat)

@[expose] def lettersOK (wd : List ℤ) : Bool := wd.all fun z => z != 0 && decide (z.natAbs ≤ 7)

@[expose] noncomputable def movesK (T : Nat) : Bool := (List.range n).any fun i => papK w T i != i

@[expose] noncomputable def differK (T U : Nat) : Bool :=
  (List.range n).any fun i => papK w T i != papK w U i

@[expose] noncomputable def modelK (A B : Nat) : Bool :=
  let W := fun wd => pword n w (letK n w A B) wd
  let I := pidn n w
  let tf := W (encodeWord fWord)
  let tt := W (encodeWord tauWord)
  let tt' := W (encodeWord tau2Word)
  permB n w A && permB n w B &&
    lettersOK (encodeWord fWord) && lettersOK (encodeWord tauWord) &&
    lettersOK (encodeWord tau2Word) && lettersOK wa7 && lettersOK wb7 &&
    j2Rels.all (fun r => lettersOK (encodeWord r)) &&
    j2Rels.all (fun r => Nat.beq (W (encodeWord r)) I) &&
    Nat.beq (W wa7) A && Nat.beq (W wb7) B &&
    Nat.beq (pc n w tt tt) I && Nat.beq (pc n w tt' tt') I &&
    Nat.beq (pc n w tt tt') (pc n w tt' tt) && movesK n w tt && movesK n w tt' &&
    differK n w tt tt' && Nat.beq (ppw n w tf 5) I && movesK n w tf &&
    Nat.beq (pc n w tf tt) (pc n w tt tf) && Nat.beq (pc n w tf tt') (pc n w tt' tf)

end CFSG.KC.J2ModelK
