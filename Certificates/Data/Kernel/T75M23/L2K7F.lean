module

public import Certificates.Data.Kernel.T75M23.L2K7D
public import Certificates.Data.Kernel.T75JM.L2KF

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.KC.N0K (allZ)

@[expose] noncomputable def el (L : Int → Nat) (c : Nat) : Nat := pc (ak L (c / 16)) (tk L (c % 16))

@[expose] noncomputable def inSAt (A T P : Nat) (S : List Nat) : Bool := S.any fun Y => conjAt A T P Y

@[expose] noncomputable def inSAtI (A T P : Nat) (S : List Nat) : Bool :=
  S.any fun Y => conjAt A T Y P

@[expose] noncomputable def inDS (A T B0 B1 : Nat) (S : List Nat) : Bool :=
  inSAt A T B0 S && inSAt A T B1 S

@[expose] noncomputable def inTP (L : Int → Nat) (X : Nat) : Bool :=
  (List.range 16).any fun l => eqP X (tk L l)

@[expose] noncomputable def comAll (A T P : Nat) : Bool := (List.range 23).all fun x => comAt A T P x

@[expose] noncomputable def evP3 (U0 U1 U2 : Nat) (w : List (Fin 3)) : Nat :=
  w.foldl (fun acc i => pc acc (if i = 0 then U0 else if i = 1 then U1 else U2)) idn

@[expose] noncomputable def evX (U0 U1 U2 : Nat) (w : List (Fin 3)) (x : Nat) : Nat :=
  w.foldr (fun i acc => fdN 5 (if i = 0 then U0 else if i = 1 then U1 else U2) acc) x

@[expose] noncomputable def relAt (U0 U1 U2 : Nat) (w : List (Fin 3)) : Bool :=
  (List.range 23).all fun x => Nat.beq (evX U0 U1 U2 w x) x

@[expose] def pts23 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

@[expose] noncomputable def evL (Ps : List Nat) (x : Nat) : Nat := Ps.foldr (fun P acc => fdN 5 P acc) x

@[expose] noncomputable def memL (Ps Ys : List Nat) : Bool :=
  Ys.any fun Y => pts23.all fun x => Nat.beq (evL Ps x) (fdN 5 Y x)

@[expose] def relsT7 : List (List (Fin 3)) := dRels7.tail

@[expose] noncomputable def swCond7 (L : Int → Nat) (S : List Nat) (U0 U1 U2 : Nat) : Bool :=
  relsT7.all (fun w => relAt U0 U1 U2 w) &&
    aWords7.all (fun w =>
      strictB (evP3 U0 U1 U2 w) fun X => S.any (fun Y => eqP X Y) && !(eqP X idn)) &&
    bWords7.all fun w => strictB (evP3 U0 U1 U2 w) fun X => inTP L X && !(eqP X idn)

@[expose] noncomputable def conj3 (A T U0 U1 U2 H0 H1 H2 : Nat) : Bool :=
  conjAt A T U0 H0 && conjAt A T U1 H1 && conjAt A T U2 H2

@[expose] noncomputable def swWit7 (A T B0 B1 : Nat) (S : List Nat) (H0 H1 H2 G0 G1 G2 U0 U1 U2 : Nat) :
    Bool :=
  inDS A T B0 B1 S && inSAtI A T B0 S && inSAtI A T B1 S &&
    (conj3 A T U0 U1 U2 H0 H1 H2 || conj3 A T U0 U1 U2 G0 G1 G2)

@[expose] def zipAll {β : Type} (d : β) (g : Nat → β → Bool) : List Nat → List β → Bool :=
  List.rec (motive := fun _ => List β → Bool) (fun _ => true)
    (fun c _ ih rs => List.casesOn (motive := fun _ => Bool) rs (g c d && ih [])
      (fun r rs' => g c r && ih rs'))

@[expose] noncomputable def forceL (f : Nat → Nat) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun c _ ih k => strictB (f c) fun P => ih fun Ps => k (P :: Ps))

@[expose] noncomputable def swPass7 (L : Int → Nat) (B0 B1 : Nat) (S : List Nat) (s2 s3 : List Nat) :
    Bool :=
  allAT L fun a k A T => !(inDS A T B0 B1 S) ||
    strictB (pc A T) fun E => strictB (pc E E) fun E2 =>
      (!(eqP E2 idn) || s2.contains (16 * a + k)) &&
        (!(eqP (pc E2 E) idn) || s3.contains (16 * a + k))

@[expose] noncomputable def swRows7 (L : Int → Nat) (B0 B1 H0 H1 H2 G0 G1 G2 : Nat) (S : List Nat)
    (R2 T2 T3 T16 : List Nat) (sw : List (List (List Nat))) : Bool :=
  zipAll [] (fun U0 r0 => zipAll [] (fun U1 r1 =>
    !(strictB (pc U0 U1) fun P => eqP (pc P (pc P P)) idn) ||
      zipAll 0 (fun U2 j => !(memL [U1, U2, U1, U2] S.tail &&
          memL [U0, U1, U2, U2, U1, U0, U2] T16 && swCond7 L S U0 U1 U2) ||
        swWit7 (ak L (j / 16)) (tk L (j % 16)) B0 B1 S H0 H1 H2 G0 G1 G2 U0 U1 U2) T3 r1)
    T2 r0) R2 sw

@[expose] noncomputable def swPassK (L : Int → Nat) (s2 s3 : List Nat) : Bool :=
  withL L fun L =>
    strictB (pw L (bGen7 0)) fun B0 => strictB (pw L (bGen7 1)) fun B1 =>
    strictB (pw L (bGen7 0 ++ bGen7 1)) fun B01 => swPass7 L B0 B1 [idn, B0, B1, B01] s2 s3

@[expose] noncomputable def swRowsK (L : Int → Nat) (s2 s3 r2 : List Nat)
    (sw : List (List (List Nat))) : Bool :=
  withL L fun L =>
    strictB (pw L (bGen7 0)) fun B0 => strictB (pw L (bGen7 1)) fun B1 =>
    strictB (pw L (bGen7 0 ++ bGen7 1)) fun B01 =>
    strictB (pw L (thetaW7 0 0)) fun H0 => strictB (pw L (thetaW7 0 1)) fun H1 =>
    strictB (pw L (thetaW7 0 2)) fun H2 =>
    strictB (pw L (thetaW7 1 0)) fun G0 => strictB (pw L (thetaW7 1 1)) fun G1 =>
    strictB (pw L (thetaW7 1 2)) fun G2 =>
    forceL (el L) r2 fun R2 => forceL (el L) s2 fun T2 => forceL (el L) s3 fun T3 =>
    forceL (tk L) (List.range 16) fun T16 =>
      swRows7 L B0 B1 H0 H1 H2 G0 G1 G2 [idn, B0, B1, B01] R2 T2 T3 T16 sw

@[expose] noncomputable def klPre7 (L : Int → Nat) (B0 A T : Nat) : Bool :=
  invAt A T && comAll A T B0 && strictB (pc A T) fun E =>
    !(inTP L E) && !(inTP L (pc B0 E)) && !(eqP E B0)

@[expose] noncomputable def klBad7 (A T B0 C BC : Nat) : Bool :=
  (comAll A T B0 || comAll A T C || comAll A T BC) &&
    !(inDS A T B0 C [idn, B0, C, BC] && inSAtI A T B0 [idn, B0, C, BC] &&
      inSAtI A T C [idn, B0, C, BC])

@[expose] noncomputable def klOne7 (L : Int → Nat) (B0 B1 C BC : Nat) (r : List Nat) : Bool :=
  (Nat.beq (r.headD 2) 0 && klBad7 (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) B0 C BC) ||
    (Nat.beq (r.headD 2) 1 &&
      inDS (ak L (r.getD 1 0 / 16)) (tk L (r.getD 1 0 % 16)) B0 B1 [idn, B0, C, BC])

@[expose] noncomputable def klE7 (L : Int → Nat) (B0 B1 : Nat) (kc : List Nat)
    (kw : List (List Nat)) : Bool :=
  allAT L (fun a k A T => !(klPre7 L B0 A T) || kc.contains (16 * a + k)) &&
    allZ [] (fun c r => strictB (el L c) fun C => klOne7 L B0 B1 C (pc B0 C) r) kc kw

@[expose] noncomputable def klK7 (L : Int → Nat) (kc : List Nat) (kw : List (List Nat)) : Bool :=
  withL L fun L =>
    strictB (pw L (bGen7 0)) fun B0 => strictB (pw L (bGen7 1)) fun B1 => klE7 L B0 B1 kc kw

end CFSG.KC.N7K

end
