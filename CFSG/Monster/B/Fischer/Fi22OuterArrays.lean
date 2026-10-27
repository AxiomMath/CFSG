module

public import CFSG.Monster.B.Fischer.Fi22OuterData
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower

public section

namespace CFSG.Monster.B.Fischer

@[expose] def fi22Outer3510Bytes : ByteArray := fi22Outer3510Text.toUTF8

@[expose] def fi22Outer693Bytes : ByteArray := fi22Outer693Text.toUTF8

@[expose] def fi22Outer256Bytes : ByteArray := fi22Outer256Text.toUTF8

@[expose] def hexLine (b : ByteArray) (w n L : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => CFSG.Monster.B.Max2.Native.hexAt b (L * (w * n + 1) + w * i.val) w

@[expose] def fi22OuterArr3510 (L : Nat) : Array Nat := hexLine fi22Outer3510Bytes 3 3510 L

@[expose] def fi22OuterArr693 (L : Nat) : Array Nat := hexLine fi22Outer693Bytes 3 693 L

@[expose] def fi22OuterArr256 (L : Nat) : Array Nat := hexLine fi22Outer256Bytes 2 256 L

@[expose] def fi22OuterLine3510 (f k : Nat) : Nat := (fi22OuterLines3510.getD f (0, 0)).1 + k

@[expose] def fi22OuterLine693 (f k : Nat) : Nat := (fi22OuterLines693.getD f (0, 0)).1 + k

@[expose] def fi22OuterStrong3510 (f : Nat) : Array (Array Nat) :=
  Array.ofFn (n := (fi22OuterLines3510.getD f (0, 0)).2) fun j =>
    fi22OuterArr3510 (fi22OuterLine3510 f j.val)

@[expose] def fi22OuterStrong693 (f : Nat) : Array (Array Nat) :=
  Array.ofFn (n := (fi22OuterLines693.getD f (0, 0)).2) fun j =>
    fi22OuterArr693 (fi22OuterLine693 f j.val)

@[expose] def fi22OuterStrong256 : Array (Array Nat) :=
  Array.ofFn (n := 16) fun j => fi22OuterArr256 j.val

@[expose] def fi22WordsArr (k s : Nat) (D : List (List Int)) : Array (List Int) :=
  Array.ofFn (n := s) fun j => if j.val < k then [] else D.getD (j.val - k) []

@[expose] def hex3List (s : String) (m : Nat) : List Nat :=
  let b := s.toUTF8
  (List.range m).map fun k => CFSG.Monster.B.Max2.Native.hexAt b (3 * k) 3

@[expose] def fi22OuterMPointsNat : List Nat := hex3List fi22OuterMPointsHex 693

@[expose] def fi22OuterTPointsNat : List Nat := hex3List fi22OuterTPointsHex 256

@[expose] def fi22OuterWitnessOrbitNat (r : Nat) : List Nat :=
  let start := (fi22OuterWitnessOrbitSizes.take r).sum
  (hex3List fi22OuterWitnessOrbitsHex 693).drop start |>.take
    (fi22OuterWitnessOrbitSizes.getD r 0)

@[expose] def codeAt (s : String) (k : Nat) : Nat := (s.toUTF8.get! k).toNat - 48

end CFSG.Monster.B.Fischer
