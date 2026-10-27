module

public import Certificates.Data.Kernel.ONanB2K
public import Certificates.Data.ONanB2Mirror

public section

namespace CFSG.OddStandard.ONanRec.MirK

open CFSG.OddStandard.ONanRec.CM
open CFSG.OddStandard.ONanRec.B2K (eqB allNeB)

@[expose] def ptsM : List (Nat × Nat) := [(0, 0), (0, 2), (0, 4), (1, 0), (1, 2)]

@[expose] noncomputable def mSmallK : Bool :=
  eqB (yW ++ yW) aW && eqB (yW ++ s1W ++ invWord yW ++ invWord s1W) r1W &&
    eqB (yW ++ s2W ++ invWord yW ++ invWord s2W) r2W && eqB (yW ++ zW) (zW ++ yW) &&
    eqB (yW ++ dW) (dW ++ yW) && eqB (wpow x5W 5) [] && !eqB x5W [] &&
    eqB (invWord gW ++ zW ++ gW) (wpow zW 3) && eqB (invWord gW ++ dW ++ gW) (zW ++ dW) &&
    cmRelCodes.all fun w => eqB (w.flatMap substG2) []

@[expose] noncomputable def mCentK (cw : List (List Nat)) : Bool :=
  cw.length == 64 && cw.all (fun c => c.all fun x => Nat.blt x 12) && allNeB cw &&
    cw.all fun c => eqB (c ++ yW) (yW ++ c) && eqB (c ++ zW) (zW ++ c)

@[expose] noncomputable def mT0K (t0 : List Nat) : Bool :=
  t0.all (fun x => Nat.blt x 12) && eqB (t0 ++ yW ++ invWord t0) (invWord yW) &&
    eqB (t0 ++ zW) (zW ++ t0)

@[expose] def mEvalW (uW t : List Nat) (w : List Nat) : List Nat :=
  w.flatMap fun k => if k = 1 then r1W else if k = 2 then r2W else if k = 3 then uW else t

@[expose] noncomputable def mOrd68K (W : List Nat) : Bool :=
  (eqB (wpow W 6) [] && !eqB (wpow W 2) [] && !eqB (wpow W 3) []) ||
    (eqB (wpow W 8) [] && !eqB (wpow W 4) [])

@[expose] noncomputable def mLeafK (uW : List Nat) (l : Nat) (t : List Nat) (h : Nat) : Bool :=
  if h = 0 then !eqB (t ++ t) []
  else if h < 5 then l == 0 && eqB (t ++ wpow uW (h - 1)) cW
  else if h < 9 then l == 0 && eqB (t ++ wpow uW (h - 5)) (dW ++ cW ++ dW)
  else Nat.blt (h - 9) 8 && mOrd68K (mEvalW uW t (badWords.getD (h - 9) []))

@[expose] noncomputable def mChainK (uW : List Nat) (l : Nat) (t0 : List Nat) :
    List (List Nat) → List Nat → Bool
  | [], _ => true
  | c :: cs, h :: hs => mLeafK uW l (t0 ++ c) h && mChainK uW l t0 cs hs
  | _ :: _, [] => false

end CFSG.OddStandard.ONanRec.MirK
