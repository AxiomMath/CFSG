module

public import Certificates.Data.Kernel.T75JM.L2KD

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM

@[expose] noncomputable def el (L : Int → Nat) (c : Nat) : Nat := pc (ak L (c / 16)) (tk L (c % 16))

@[expose] def allZ {β : Type} (d : β) (g : Nat → β → Bool) : List Nat → List β → Bool :=
  List.rec (motive := fun _ => List β → Bool) (fun _ => true)
    (fun c _ ih rs => g c (List.headD rs d) && ih (List.tail rs))

@[expose] noncomputable def comAll (A T P : Nat) : Bool := (List.range 22).all fun x => comAt A T P x

@[expose] noncomputable def inSAt (A T P : Nat) (S : List Nat) : Bool := S.any fun Y => conjAt A T P Y

@[expose] noncomputable def inSAtI (A T P : Nat) (S : List Nat) : Bool :=
  S.any fun Y => conjAt A T Y P

@[expose] noncomputable def inTP (L : Int → Nat) (X : Nat) : Bool :=
  (List.range 16).any fun l => eqP X (tk L l)

@[expose] noncomputable def evP (U0 U1 : Nat) (w : List (Fin 2)) : Nat :=
  w.foldl (fun acc i => pc acc (if i = 0 then U0 else U1)) idn

@[expose] noncomputable def inDS (A T B0 B1 : Nat) (S : List Nat) : Bool :=
  inSAt A T B0 S && inSAt A T B1 S

@[expose] noncomputable def swCond (L : Int → Nat) (S : List Nat) (U0 U1 : Nat) : Bool :=
  eqP (evP U0 U1 [0, 0, 0, 0]) idn && eqP (evP U0 U1 [1, 1, 1, 1]) idn &&
    eqP (evP U0 U1 [0, 1, 0, 1, 0, 1]) idn &&
    aWords.all (fun w => strictB (evP U0 U1 w) fun X => S.any (fun Y => eqP X Y) && !(eqP X idn)) &&
    bWords.all fun w => strictB (evP U0 U1 w) fun X => inTP L X && !(eqP X idn)

@[expose] noncomputable def swWit (L : Int → Nat) (B0 B1 H0 H1 : Nat) (S : List Nat)
    (U0 U1 j : Nat) : Bool :=
  inDS (ak L (j / 16)) (tk L (j % 16)) B0 B1 S &&
    inSAtI (ak L (j / 16)) (tk L (j % 16)) B0 S && inSAtI (ak L (j / 16)) (tk L (j % 16)) B1 S &&
    conjAt (ak L (j / 16)) (tk L (j % 16)) U0 H0 && conjAt (ak L (j / 16)) (tk L (j % 16)) U1 H1

@[expose] noncomputable def swE (L : Int → Nat) (B0 B1 H0 H1 : Nat) (S : List Nat)
    (su0 su1 : List Nat) (sj : List (List Nat)) : Bool :=
  allAT L (fun a k A T => !(inDS A T B0 B1 S) ||
      strictB (pc A T) fun E => strictB (pc E E) fun E2 =>
        (!(inTP L E2 && !(eqP E2 idn)) || su0.contains (16 * a + k)) &&
          (!(S.any (fun Y => eqP E2 Y) && !(eqP E2 idn)) || su1.contains (16 * a + k))) &&
    allZ [] (fun c0 r => strictB (el L c0) fun U0 => allZ 0 (fun c1 j =>
      strictB (el L c1) fun U1 => swWit L B0 B1 H0 H1 S U0 U1 j || !(swCond L S U0 U1)) su1 r)
      su0 sj

@[expose] noncomputable def swK (L : Int → Nat) (su0 su1 : List Nat) (sj : List (List Nat)) :
    Bool :=
  withL L fun L =>
    strictB (pw L (bGen 0)) fun B0 => strictB (pw L (bGen 1)) fun B1 =>
    strictB (pw L (bGen 0 ++ bGen 1)) fun B01 =>
    strictB (pw L (dTheta 0)) fun H0 => strictB (pw L (dTheta 1)) fun H1 =>
      swE L B0 B1 H0 H1 [idn, B0, B1, B01] su0 su1 sj

@[expose] noncomputable def klPre (L : Int → Nat) (B0 A T : Nat) : Bool :=
  invAt A T && comAll A T B0 && strictB (pc A T) fun E =>
    !(inTP L E) && !(inTP L (pc B0 E)) && !(eqP E B0)

@[expose] noncomputable def klBad (A T B0 C BC : Nat) : Bool :=
  (comAll A T B0 || comAll A T C || comAll A T BC) &&
    !(inDS A T B0 C [idn, B0, C, BC] && inSAtI A T B0 [idn, B0, C, BC] &&
      inSAtI A T C [idn, B0, C, BC])

@[expose] noncomputable def klOne (L : Int → Nat) (B0 B1 X0 X1 C BC : Nat) (r : List Nat) : Bool :=
  (Nat.beq (r.headD 3) 0 && klBad (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) B0 C BC) ||
    (Nat.beq (r.headD 3) 1 &&
      inDS (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) B0 B1 [idn, B0, C, BC]) ||
    (Nat.beq (r.headD 3) 2 &&
      inDS (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) X0 X1 [idn, B0, C, BC])

@[expose] noncomputable def klE (L : Int → Nat) (B0 B1 X0 X1 : Nat) (kc : List Nat)
    (kw : List (List Nat)) : Bool :=
  allAT L (fun a k A T => !(klPre L B0 A T) || kc.contains (16 * a + k)) &&
    allZ [] (fun c r => strictB (el L c) fun C => klOne L B0 B1 X0 X1 C (pc B0 C) r) kc kw

@[expose] noncomputable def klK (L : Int → Nat) (kc : List Nat) (kw : List (List Nat)) : Bool :=
  withL L fun L =>
    strictB (pw L (bGen 0)) fun B0 => strictB (pw L (bGen 1)) fun B1 =>
    strictB (pw L (substWord (bGen 0))) fun X0 => strictB (pw L (substWord (bGen 1))) fun X1 =>
      klE L B0 B1 X0 X1 kc kw

end CFSG.KC.N0K

end
