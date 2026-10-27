module

public import Certificates.Data.Kernel.AS91K468.K46
public import CFSG.Quasithin.H13.AS91Sec4EightInputs
public import CFSG.Quasithin.H13.AS91Sec4SevenInputs

public section

noncomputable section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K
open CFSG.Quasithin.H13.AS91.Two (w1List w1Basis crd6 i7List omList inO1b inIb iWit48 q0c lamOf
  idA stabWords48 stabNcWords48 orbWords48 core1Rows spanRows48 spanInv48)

@[expose] def un7 (X : ℕ) : List ℕ :=
  [X % 128, X / 128 % 128, X / 16384 % 128, X / 2097152 % 128, X / 268435456 % 128,
    X / 34359738368 % 128, X / 4398046511104 % 128]

@[expose] def unpack7 (X : ℕ) : Array ℕ := (un7 X).toArray

@[expose] def pk7 (a0 a1 a2 a3 a4 a5 a6 : ℕ) : ℕ :=
  a0 + 128 * a1 + 16384 * a2 + 2097152 * a3 + 268435456 * a4 + 34359738368 * a5 +
    4398046511104 * a6

@[expose] def app7Q (X n : ℕ) : ℕ :=
  0 ^^^ X % 128 * (n / 1 % 2) ^^^ X / 128 % 128 * (n / 2 % 2) ^^^
    X / 16384 % 128 * (n / 4 % 2) ^^^ X / 2097152 % 128 * (n / 8 % 2) ^^^
    X / 268435456 % 128 * (n / 16 % 2) ^^^ X / 34359738368 % 128 * (n / 32 % 2) ^^^
    X / 4398046511104 % 128 * (n / 64 % 2)

@[expose] def mul7Q (X Y : ℕ) : ℕ :=
  pk7 (app7Q X (Y % 128)) (app7Q X (Y / 128 % 128)) (app7Q X (Y / 16384 % 128))
    (app7Q X (Y / 2097152 % 128)) (app7Q X (Y / 268435456 % 128))
    (app7Q X (Y / 34359738368 % 128)) (app7Q X (Y / 4398046511104 % 128))

@[expose] def one7 : ℕ := 282578800148737

@[expose] def mk7Q (l : ℕ) (A : List ℕ) : ℕ :=
  pk7 1 (l % 2 + 2 * A.getD 0 0) (l / 2 % 2 + 2 * A.getD 1 0) (l / 4 % 2 + 2 * A.getD 2 0)
    (l / 8 % 2 + 2 * A.getD 3 0) (l / 16 % 2 + 2 * A.getD 4 0) (l / 32 % 2 + 2 * A.getD 5 0)

@[expose] def enum7Q (gs : List ℕ) : List ℕ :=
  closN (gs.map fun g x => mul7Q x g) 100000 [one7] (insP (.tip []) one7) []

@[expose] def closed7Q (gs X : List ℕ) : Bool :=
  let S := ofListP X
  X.all fun x => gs.all fun g => memP S (mul7Q x g)

@[expose] def aPartQ (X : ℕ) : List ℕ := ((un7 X).drop 1).map (· / 2)

@[expose] def fix7Q (X : ℕ) : ℕ := ((List.range 128).filter fun v => Nat.beq (app7Q X v) v).length

@[expose] def d7Q : List ℕ := [236358513262849, 280339246940417, 317869206372737]

@[expose] def r7Q : List ℕ :=
  [322266982351105, 330957311901953, 291446565601537, 286977115111681, 282579068584193,
    282613159903489]

@[expose] def wit1Q : ℕ := 179148234751873

@[expose] def wit2Q : ℕ := 269384693694209

@[expose] def t7Q : ℕ := mk7Q 10 idA

@[expose] def st48Q : List ℕ := stabWords48.map (wordQS g13Q)

@[expose] def res6Q (x : ℕ) : List ℕ := w1Basis.map fun b => crd6 (mvNR (unpackQ x) b)

@[expose] def s48Of (S : List ℕ) : List (List ℕ) := (S.map res6Q).dedup

@[expose] def c3Of (SA : List (List ℕ)) : List ℕ :=
  SA.flatMap fun A => (List.range 64).map fun l => mk7Q l A

@[expose] def b7Of (C : List ℕ) : List ℕ :=
  C.filter fun X => i7List.all fun v => Nat.beq (app7Q X v) v

@[expose] def s0M : ℕ := maskOf 0 (w1List.map (· ^^^ q0c))

@[expose] def imgS (A : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ)
    (fun m b acc => Bool.rec (Nat.lor acc (Nat.shiftLeft 1 (mvNR A b))) acc (Nat.beq m 0))
    (fun d ih m b acc => Bool.rec
      (ih (Nat.shiftRight m (Nat.pow 2 d)) (Nat.add b (Nat.pow 2 d))
        (ih (Nat.mod m (Nat.pow 2 (Nat.pow 2 d))) b acc)) acc (Nat.beq m 0))

@[expose] def imgF (g m : ℕ) : ℕ := imgS (unpackQ g) 12 (m % 2 ^ 2 ^ 12) 0 0

@[expose] def tOrbQ : List ℕ := closN (g13Q.map imgF) 100 [s0M] (insP (.tip []) s0M) []

@[expose] def core1Q : List ℕ := core1Rows.map fun r => codeQ r.toList

@[expose] def spQ : ℕ := codeQ spanRows48.toList

@[expose] def siQ : ℕ := codeQ spanInv48.toList

@[expose] def ncQ : List ℕ :=
  core1Q ++ ebQ ++ [mulQ (g13Q.headD oneQ) (mulQ (core1Q.headD oneQ) (invQ (g13Q.headD oneQ)))]

@[expose] def ncOrbQ : List ℕ := closN (ncQ.map imgF) 100 [s0M] (insP (.tip []) s0M) []

@[expose] def itOf (Eb : List ℕ) : List ℕ := (Eb.map fun e => mvNR (unpackQ e) q0c ^^^ q0c).dedup

@[expose] def tGens : List ℕ :=
  ((List.range 6).map fun i => mk7Q (2 ^ i) idA) ++ pQ.map fun p => mk7Q 0 (res6Q p)

@[expose] def stabAt (S O : List ℕ) : Bool :=
  gensOKQ st48Q && st48Q.all (fun g => bitQ w1M (mvNR (unpackQ g) q0c ^^^ q0c)) &&
    S.contains oneQ && closedQ st48Q S && nodupP S && Nat.beq S.length 768 && O.dedup.length == 45

@[expose] def c3At (SA : List (List ℕ)) (C B : List ℕ) : Bool :=
  SA.all (fun A => A.length == 6 && A.all (· < 64)) && nodupP C && Nat.beq C.length 3072 &&
    nodupP B && Nat.beq B.length 16 && B.contains t7Q &&
    B.all (fun x => B.all fun y => Nat.beq (mul7Q x y) (mul7Q y x)) &&
    B.all (fun x => Nat.beq (mul7Q x x) one7) &&
    C.all fun X => !(B.all fun b => Nat.beq (mul7Q X b) (mul7Q b X)) || memP (ofListP B) X

@[expose] def iAt (It C : List ℕ) : Bool :=
  It.length == 8 && It.all (fun w => w1List.contains w) &&
    It.all (fun w => i7List.contains (2 * crd6 w) && i7List.contains (2 * crd6 w + 1)) &&
    i7List.all (fun c => It.any fun w => crd6 w == c / 2) &&
    It.all (fun w => !inO1b w || (omList.contains (2 * crd6 w) && omList.contains (2 * crd6 w + 1))) &&
    omList.all (fun c => It.any fun w => inO1b w && crd6 w == c / 2) &&
    C.all (fun X => omList.all fun c => omList.contains (app7Q X c)) &&
    omList.all (fun c => C.any fun X => Nat.beq (app7Q X 2) c) &&
    C.contains wit1Q && C.contains wit2Q &&
    !Nat.beq (app7Q wit1Q (app7Q wit2Q 2)) (app7Q wit2Q (app7Q wit1Q 2)) &&
    inIb iWit48 && w1List.contains (q0c ^^^ iWit48)

@[expose] def fixEbQ (Eb : List ℕ) (r : ℕ) : ℕ :=
  (Eb.filter fun e => Nat.beq (mulQ r e) (mulQ e r)).length

@[expose] def fusP (SR : List (ℕ × List ℕ)) (Eb : List ℕ) (X : ℕ) : Bool :=
  !Nat.beq X one7 && SR.any fun p => p.2 == aPartQ X && Nat.ble 128 (fix7Q X * fixEbQ Eb p.1)

@[expose] def fusAt (R : List ℕ) (SR : List (ℕ × List ℕ)) (Eb : List ℕ) : Bool :=
  nodupP R && Nat.ble (R.filter (fusP SR Eb)).length 27

@[expose] def orbAt (B O : List ℕ) : Bool :=
  orbWords48.all (fun p => bitQ w1M (mvNR (unpackQ (wordQS g13Q p.2)) q0c ^^^ p.1)) &&
    Nat.beq (mulQ spQ siQ) oneQ && B.contains (mk7Q (lamOf 513) idA) && gensOKQ g13Q &&
    gensOKQ ncQ &&
    (stabWords48.zip stabNcWords48).all (fun p => Nat.beq (wordQS ncQ p.2) (wordQS g13Q p.1)) &&
    O.dedup.length == 45

@[expose] def s48L : List (List ℕ) :=
  [[62, 9, 15, 60, 47, 20], [62, 50, 15, 8, 16, 26], [62, 3, 15, 57, 46, 36],
    [62, 56, 15, 13, 17, 42], [1, 38, 5, 19, 47, 33], [1, 44, 5, 28, 17, 27],
    [1, 34, 5, 23, 46, 32], [1, 40, 5, 24, 16, 26], [1, 41, 5, 28, 17, 31],
    [63, 45, 52, 23, 46, 30], [63, 34, 52, 24, 16, 32], [62, 25, 49, 19, 47, 21],
    [62, 12, 15, 57, 46, 21], [63, 61, 11, 13, 17, 43], [1, 54, 4, 60, 47, 31],
    [63, 56, 11, 8, 16, 42], [63, 54, 11, 13, 17, 31], [1, 6, 4, 8, 16, 37],
    [1, 55, 4, 57, 46, 27], [63, 12, 11, 60, 47, 21], [63, 2, 11, 57, 46, 32],
    [63, 25, 52, 23, 46, 21], [1, 35, 5, 19, 47, 37], [62, 35, 49, 24, 16, 37],
    [63, 41, 52, 19, 47, 31], [63, 18, 52, 28, 17, 42], [62, 39, 49, 28, 17, 36],
    [63, 22, 52, 24, 16, 43], [62, 44, 49, 23, 46, 27], [62, 22, 49, 28, 17, 43],
    [62, 6, 15, 60, 47, 37], [63, 51, 11, 8, 16, 30], [1, 3, 4, 13, 17, 36],
    [1, 51, 4, 57, 46, 30], [62, 61, 15, 8, 16, 43], [62, 55, 15, 13, 17, 27],
    [1, 7, 4, 13, 17, 33], [1, 45, 5, 24, 16, 30], [1, 39, 5, 23, 46, 36],
    [62, 29, 49, 23, 46, 20], [63, 38, 52, 28, 17, 33], [63, 29, 52, 19, 47, 20],
    [63, 9, 11, 57, 46, 20], [63, 7, 11, 60, 47, 33], [1, 50, 4, 60, 47, 26],
    [62, 40, 49, 19, 47, 26], [62, 18, 49, 24, 16, 42], [1, 2, 4, 8, 16, 32]]

@[expose] def pbarL : List (List ℕ) :=
  [[1, 41, 5, 28, 17, 31], [1, 7, 4, 13, 17, 33], [1, 6, 4, 8, 16, 37], [1, 38, 5, 19, 47, 33],
    [1, 40, 5, 24, 16, 26], [1, 50, 4, 60, 47, 26], [1, 55, 4, 57, 46, 27],
    [1, 54, 4, 60, 47, 31], [1, 39, 5, 23, 46, 36], [1, 35, 5, 19, 47, 37],
    [1, 34, 5, 23, 46, 32], [1, 3, 4, 13, 17, 36], [1, 45, 5, 24, 16, 30],
    [1, 51, 4, 57, 46, 30], [1, 44, 5, 28, 17, 27], [1, 2, 4, 8, 16, 32]]

@[expose] def b7L : List ℕ :=
  [264995209642241, 264995211755777, 264995478094081, 264995480174849, 269393256169729,
    269393258250497, 269393524588801, 269393526702337, 282578800148737, 282578802262273,
    282579068600577, 282579070681345, 286976846676225, 286976848756993, 286977115095297,
    286977117208833]

@[expose] def r64L : List ℕ :=
  [286977115095297, 295844343677185, 326559533826305, 317869204275457, 282578800165121,
    286976846659841, 287011474850049, 287011206414593, 282613159887105, 282579068600577,
    317834844553473, 317868935840001, 326593893581057, 295878703431937, 326559265390849,
    295844612112641, 295878971851009, 326593625129217, 322266982367489, 317834576101633,
    330957311918337, 291446565617921, 322232891064577, 330991940092161, 291480656920833,
    287011206398209, 317834844537089, 317868935856385, 326593893564673, 326559265407233,
    295878703415553, 295844612129025, 330957580353793, 330991671640321, 326593625145601,
    322267250802945, 322232622612737, 317834576118017, 291446297182465, 291480925339905,
    295878971867393, 282613428322561, 291480656904449, 322232891048193, 330991940075777,
    295844343693569, 326559533842689, 317869204291841, 286976846676225, 291446297166081,
    330957580337409, 322267250786561, 282613428338945, 287011474833665, 291480925356289,
    330991671656705, 322232622629121, 282613159903489, 282579068584193, 286977115111681,
    291446565601537, 330957311901953, 322266982351105, 282578800148737]

@[expose] def r64OK : Bool := enum7Q r7Q == r64L

@[expose] def s48OK : Bool := s48Of (enumQ st48Q) == s48L

@[expose] def pbarOK : Bool := s48Of (enumQ pQ) == pbarL

@[expose] def b7OK : Bool := b7Of (c3Of s48L) == b7L

@[expose] def stab48Q : Bool := stabAt (enumQ st48Q) tOrbQ

@[expose] def c348Q : Bool := c3At s48L (c3Of s48L) b7L

@[expose] def i48Q : Bool := iAt (itOf (enumQ ebQ)) (c3Of s48L)

@[expose] def tBaseAt (PB SA : List (List ℕ)) (T B D R : List ℕ) : Bool :=
  let Ts := ofListP T
  PB.all (fun A => A.length == 6 && A.all (· < 64) && SA.contains A) &&
    nodupP T && Nat.beq T.length 1024 && B.all (fun b => memP Ts b) &&
    D.contains one7 && closed7Q d7Q D && nodupP D && Nat.beq D.length 64 &&
    D.all (fun x => memP Ts x) && D.all (fun x => !B.contains x || Nat.beq x one7) &&
    R.contains one7 && closed7Q r7Q R && nodupP R && Nat.beq R.length 64 &&
    R.all (fun x => memP Ts x) && R.all (fun x => R.all fun y => Nat.beq (mul7Q x y) (mul7Q y x)) &&
    R.all (fun x => Nat.beq (mul7Q x x) one7) && R.any (fun x => aPartQ x != idA) &&
    tGens.all fun g => memP Ts g

@[expose] def tNormAt (R Xs : List ℕ) : Bool :=
  Xs.all fun X => let RX := ofListP (R.map fun y' => mul7Q y' X)
    r7Q.all fun y => memP RX (mul7Q X y)

@[expose] def tCentAt (Xs : List ℕ) : Bool :=
  Xs.all fun X => !(tGens.all fun Y => Nat.beq (mul7Q X Y) (mul7Q Y X)) || Nat.beq X one7 ||
    Nat.beq X t7Q

@[expose] def tBase48Q : Bool := tBaseAt pbarL s48L (c3Of pbarL) b7L (enum7Q d7Q) r64L

@[expose] def tNorm48Q (i : ℕ) : Bool := tNormAt r64L (c3Of [pbarL.getD i []])

@[expose] def tCent48Q : Bool := tCentAt (c3Of pbarL)

@[expose] def fus48Q : Bool :=
  fusAt r64L ((enumQ st48Q).map fun r => (r, res6Q r)) (enumQ ebQ)

@[expose] def orb48Q : Bool := orbAt b7L ncOrbQ

end Certificates.Kernel.AS91K468

end

end
