module

public import Certificates.Data.Kernel.T75M23.P7K
public import CFSG.CGT.T75M23.L2FInputs7

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23

@[expose] noncomputable def eqP (P Q : Nat) : Bool :=
  (List.range 23).all fun x => Nat.beq (fdN 5 P x) (fdN 5 Q x)

@[expose] noncomputable def eqWd (L : Int → Nat) (w w' : List (Fin 6 × Bool)) : Bool :=
  eqP (pw L w) (pw L w')

@[expose] noncomputable def inT (L : Int → Nat) (w : List (Fin 6 × Bool)) : Bool :=
  (List.range 16).any fun k => eqWd L w (tw7 k)

@[expose] noncomputable def inB (L : Int → Nat) (w : List (Fin 6 × Bool)) : Bool :=
  eqWd L w [] || (eqWd L w (bGen7 0) || (eqWd L w (bGen7 1) ||
    (eqWd L w (bGen7 0 ++ bGen7 1) || false)))

@[expose] noncomputable def normBK (L : Int → Nat) (x xi : List (Fin 6 × Bool)) : Bool :=
  inB L (x ++ bGen7 0 ++ xi) && inB L (x ++ bGen7 1 ++ xi) && inB L (xi ++ bGen7 0 ++ x) &&
    inB L (xi ++ bGen7 1 ++ x)

@[expose] noncomputable def tK (L : Int → Nat) : Bool :=
  withL L fun L =>
    (List.range 16).all (fun k => (List.range 16).all fun l =>
      eqWd L (tw7 k ++ tw7 l) (tw7 (k ^^^ l))) &&
      (List.range 16).all fun k => (List.range 16).all fun l => !(eqWd L (tw7 k) (tw7 l)) || k == l

@[expose] noncomputable def bK (L : Int → Nat) : Bool :=
  withL L fun L =>
    eqWd L (bGen7 0 ++ bGen7 0) [] && eqWd L (bGen7 1 ++ bGen7 1) [] &&
      eqWd L (bGen7 0 ++ bGen7 1) (bGen7 1 ++ bGen7 0) && !(eqWd L (bGen7 0) []) &&
      !(eqWd L (bGen7 1) []) && !(eqWd L (bGen7 0) (bGen7 1)) &&
      !(eqWd L (bGen7 0 ++ bGen7 1) []) && !(eqWd L (bGen7 0 ++ bGen7 1) (bGen7 0)) &&
      !(eqWd L (bGen7 0 ++ bGen7 1) (bGen7 1)) && !(inT L (bGen7 0))

@[expose] noncomputable def normalK (L : Int → Nat) : Bool :=
  withL L fun L => (List.range 6).all fun k => (List.range 16).all fun l =>
    inT L ([(Fin.ofNat 6 k, true)] ++ tw7 l ++ [(Fin.ofNat 6 k, false)]) &&
      inT L ([(Fin.ofNat 6 k, false)] ++ tw7 l ++ [(Fin.ofNat 6 k, true)])

@[expose] noncomputable def dMemK (L : Int → Nat) : Bool :=
  withL L fun L =>
    (List.finRange 3).all (fun i => normBK L (dGen7 i) (invWord7 (dGen7 i))) &&
      (List.finRange 2).all (fun k => (List.finRange 3).all fun i =>
        normBK L (thetaW7 k i) (invWord7 (thetaW7 k i))) &&
      (List.finRange 2).all fun k => normBK L (d0W7 k) (invWord7 (d0W7 k))

@[expose] noncomputable def dRelK (L : Int → Nat) : Bool :=
  withL L fun L =>
    eqWd L (dEvalW7 [0, 0]) [] && eqWd L (dEvalW7 [1, 1]) [] && eqWd L (dEvalW7 [2, 2, 2]) [] &&
      dRels7.all fun w => eqWd L (dEvalW7 w) []

@[expose] noncomputable def abK (L : Int → Nat) : Bool :=
  withL L fun L =>
    aWords7.all (fun w => normBK L (dEvalW7 w) (invWord7 (dEvalW7 w)) && inT L (dEvalW7 w) &&
        !(eqWd L (dEvalW7 w) [])) &&
      bWords7.all fun w => inB L (dEvalW7 w) && !(eqWd L (dEvalW7 w) [])

@[expose] def thEvalW7 (k : Fin 2) (w : List (Fin 3)) : List (Fin 6 × Bool) :=
  (w.map (thetaW7 k)).flatten

@[expose] noncomputable def thSqK (L : Int → Nat) : Bool :=
  withL L fun L =>
    (List.finRange 2).all fun k => (List.finRange 3).all fun i =>
      eqWd L (dEvalW7 (thWords7 k i)) (thetaW7 k i) &&
        eqWd L (thEvalW7 k (thWords7 k i)) (d0W7 k ++ dGen7 i ++ invWord7 (d0W7 k))

@[expose] noncomputable def conjAt (A T P Y : Nat) : Bool :=
  (List.range 23).all fun x =>
    Nat.beq (fdN 5 A (fdN 5 T (fdN 5 P x))) (fdN 5 Y (fdN 5 A (fdN 5 T x)))

@[expose] noncomputable def centerE (L : Int → Nat) (D0 D1 D2 B0 B1 B01 : Nat) : Bool :=
  allAT L fun _ _ A T =>
    !((List.range 23).all fun x => comAt A T D0 x && comAt A T D1 x && comAt A T D2 x) ||
      !([B0, B1].all fun P => [idn, B0, B1, B01].any fun Y => conjAt A T P Y) || eqAt A T idn

@[expose] noncomputable def centerK (L : Int → Nat) : Bool :=
  withL L fun L =>
    strictB (pw L (dGen7 0)) fun D0 => strictB (pw L (dGen7 1)) fun D1 =>
    strictB (pw L (dGen7 2)) fun D2 =>
    strictB (pw L (bGen7 0)) fun B0 => strictB (pw L (bGen7 1)) fun B1 =>
    strictB (pw L (bGen7 0 ++ bGen7 1)) fun B01 => centerE L D0 D1 D2 B0 B1 B01

end CFSG.KC.N7K

end
