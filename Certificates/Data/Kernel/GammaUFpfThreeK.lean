module

public import CFSG.GF2Type.Smith1979.GammaU.FpfThreeInputs

public section

namespace CFSG.KC.GUK

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.SigmaP

@[expose] noncomputable def comboK (L : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih m => Nat.xor (bif Nat.beq (Nat.land m 1) 1 then a else 0) (ih (Nat.shiftRight m 1)))
    L m

@[expose] noncomputable def maskL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.lor (Nat.shiftLeft 1 a) ih) L

@[expose] noncomputable def bitM (M y : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight M y) 1) 1

@[expose] noncomputable def par6 (t : Nat) : Bool :=
  (((((false ^^ t.testBit 0) ^^ t.testBit 1) ^^ t.testBit 2) ^^ t.testBit 3) ^^ t.testBit 4) ^^
    t.testBit 5

@[expose] noncomputable def f0K (m n : Nat) : Bool := par6 ((m &&& (n >>> 6)) ^^^ ((m >>> 6) &&& n))

@[expose] noncomputable def headK (b B6 S : List ℕ) (CS : List (ℕ × ℕ)) (SB SP : List ℕ) : Bool :=
  b.all S.contains && (List.range 63).all (fun m => comboK B6 (m + 1) != 0) &&
    CS.all (fun p => comboK B6 p.2 == p.1) &&
    (List.range 4096).all fun v => SB.any (f0K v) || SP.contains v

@[expose] noncomputable def tripleK (B6 : List ℕ) (SM : ℕ) (CS : List (ℕ × ℕ)) (b u : List ℕ) :
    Bool :=
  !(CS.all (fun p => bitM SM (comboK (six u) p.2)) &&
      (List.range 63).all (fun m => comboK (six u) (m + 1) != comboK B6 (m + 1)) &&
      (b.zip u).all fun p =>
        comboK (six u) (coordOf B6 (comboK (six u) (coordOf B6 p.2))) == p.1) ||
    u == b.map theta0N || u == b.map fun x => theta0N (theta0N x)

@[expose] noncomputable def triplesK (B6 S U : List ℕ) (SM : ℕ) (CS : List (ℕ × ℕ)) (b : List ℕ) :
    Bool :=
  U.all fun u₁ => S.all fun u₂ => S.all fun u₃ => tripleK B6 SM CS b [u₁, u₂, u₃]

end CFSG.KC.GUK

end
