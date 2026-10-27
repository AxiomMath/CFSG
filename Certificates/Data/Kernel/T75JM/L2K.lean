module

public import Certificates.Data.Kernel.T75JM.PCheckK
public import CFSG.CGT.T75JM.L2FInputs

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM

@[expose] noncomputable def eqP (P Q : Nat) : Bool :=
  (List.range 22).all fun x => Nat.beq (fdN 5 P x) (fdN 5 Q x)

@[expose] noncomputable def eqWd (L : Int → Nat) (w w' : List (Fin 6 × Bool)) : Bool :=
  eqP (pw L w) (pw L w')

@[expose] noncomputable def inT (L : Int → Nat) (w : List (Fin 6 × Bool)) : Bool :=
  (List.range 16).any fun k => eqWd L w (tw k)

@[expose] noncomputable def inB (L : Int → Nat) (w : List (Fin 6 × Bool)) : Bool :=
  eqWd L w [] || (eqWd L w (bGen 0) || (eqWd L w (bGen 1) || (eqWd L w (bGen 0 ++ bGen 1) || false)))

@[expose] noncomputable def normBK (L : Int → Nat) (x xi : List (Fin 6 × Bool)) : Bool :=
  inB L (x ++ bGen 0 ++ xi) && inB L (x ++ bGen 1 ++ xi) && inB L (xi ++ bGen 0 ++ x) &&
    inB L (xi ++ bGen 1 ++ x)

@[expose] noncomputable def tK (L : Int → Nat) : Bool :=
  withL L fun L =>
    (List.range 16).all (fun k => (List.range 16).all fun l => eqWd L (tw k ++ tw l) (tw (k ^^^ l))) &&
      (List.range 16).all fun k => (List.range 16).all fun l => !(eqWd L (tw k) (tw l)) || k == l

@[expose] noncomputable def bK (L : Int → Nat) : Bool :=
  withL L fun L =>
    eqWd L (bGen 0 ++ bGen 0) [] && eqWd L (bGen 1 ++ bGen 1) [] &&
      eqWd L (bGen 0 ++ bGen 1) (bGen 1 ++ bGen 0) && !(eqWd L (bGen 0) []) &&
      !(eqWd L (bGen 1) []) && !(eqWd L (bGen 0) (bGen 1)) && !(eqWd L (bGen 0 ++ bGen 1) []) &&
      !(eqWd L (bGen 0 ++ bGen 1) (bGen 0)) && !(eqWd L (bGen 0 ++ bGen 1) (bGen 1)) &&
      !(inT L (bGen 0))

@[expose] noncomputable def aRelK (L : Int → Nat) : Bool :=
  withL L fun L => rels6.all fun r => eqWd L (substWord r) []

@[expose] noncomputable def aTK (L : Int → Nat) : Bool :=
  withL L fun L => (List.range 16).all fun k => inT L (substWord (tw k))

@[expose] noncomputable def dMemK (L : Int → Nat) : Bool :=
  withL L fun L =>
    normBK L (dGen 0) (invWord (dGen 0)) && normBK L (dGen 1) (invWord (dGen 1)) &&
      normBK L (dTheta 0) (invWord (dTheta 0)) && normBK L (dTheta 1) (invWord (dTheta 1))

@[expose] noncomputable def dRelK (L : Int → Nat) : Bool :=
  withL L fun L =>
    eqWd L (dEvalW [0, 0, 0, 0]) [] && eqWd L (dEvalW [1, 1, 1, 1]) [] &&
      eqWd L (dEvalW [0, 1, 0, 1, 0, 1]) []

@[expose] noncomputable def abK (L : Int → Nat) : Bool :=
  withL L fun L =>
    aWords.all (fun w => normBK L (dEvalW w) (invWord (dEvalW w)) && inT L (dEvalW w) &&
        !(eqWd L (dEvalW w) [])) &&
      bWords.all fun w => inB L (dEvalW w) && !(eqWd L (dEvalW w) [])

@[expose] noncomputable def thSqK (L : Int → Nat) : Bool :=
  withL L fun L =>
    (List.finRange 2).all fun i =>
      eqWd L (dEvalW (thWords i)) (dTheta i) && eqWd L (thEvalW (thWords i)) (dGen i)

@[expose] def letters6 : List (Fin 6 × Bool) :=
  (List.finRange 6).flatMap fun i => [(i, true), (i, false)]

@[expose] noncomputable def normalK (L : Int → Nat) : Bool :=
  withL L fun L => letters6.all fun p => (List.range 16).all fun k =>
    inT L ([p] ++ tw k ++ [(p.1, !p.2)])

@[expose] def a6Wl (u : List Nat) : List (Fin 6 × Bool) :=
  u.map fun i => (if i = 0 then 0 else 1, true)

@[expose] noncomputable def alphaK (L : Int → Nat) : Bool :=
  withL L fun L =>
    rels6.all (fun r => eqWd L (substWord r) []) &&
      (List.range 16).all (fun k => hexad.all fun p =>
        Nat.beq (fdN 5 (pw L (substWord (tw k))) p) p) &&
      nodupN (a6Words.map fun u => keyL hexad (pw L (substWord (a6Wl u)))) &&
      nodupN ((List.range 16).map fun k => keyL (List.range 22) (pw L (substWord (tw k))))

@[expose] noncomputable def conjAt (A T P Y : Nat) : Bool :=
  (List.range 22).all fun x =>
    Nat.beq (fdN 5 A (fdN 5 T (fdN 5 P x))) (fdN 5 Y (fdN 5 A (fdN 5 T x)))

@[expose] noncomputable def centerE (L : Int → Nat) (D0 D1 B0 B1 B01 : Nat) : Bool :=
  allAT L fun _ _ A T =>
    !((List.range 22).all fun x => comAt A T D0 x && comAt A T D1 x) ||
      !([B0, B1].all fun P => [idn, B0, B1, B01].any fun Y => conjAt A T P Y) || eqAt A T idn

@[expose] noncomputable def centerK (L : Int → Nat) : Bool :=
  withL L fun L =>
    strictB (pw L (dGen 0)) fun D0 => strictB (pw L (dGen 1)) fun D1 =>
    strictB (pw L (bGen 0)) fun B0 => strictB (pw L (bGen 1)) fun B1 =>
    strictB (pw L (bGen 0 ++ bGen 1)) fun B01 => centerE L D0 D1 B0 B1 B01

end CFSG.KC.N0K

end
