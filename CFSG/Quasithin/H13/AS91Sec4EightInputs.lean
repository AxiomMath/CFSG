module

public import CFSG.Quasithin.H13.AS91Sec4SixInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour

@[expose] def w1Basis : List ℕ := [3, 40, 192, 276, 1028, 2560]

@[expose] def w1Piv : List ℕ := [1, 5, 7, 8, 10, 11]

@[expose] def crd6 (v : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc i => if v.testBit (w1Piv.getD i 0) then acc ||| 1 <<< i else acc) 0

@[expose] def res6 (r : Array ℕ) : List ℕ := w1Basis.map fun b => crd6 (appN r b)

@[expose] def polarB (a b : ℕ) : Bool := q0b (a ^^^ b) != (q0b a != q0b b)

@[expose] def lamOf (u : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc i => if polarB (w1Basis.getD i 0) u then acc ||| 1 <<< i else acc) 0

@[expose] def mk7 (l : ℕ) (A : List ℕ) : Array ℕ :=
  (1 :: (List.range 6).map fun i => (l >>> i) % 2 + 2 * A.getD i 0).toArray

@[expose] def app7 (M : Array ℕ) (n : ℕ) : ℕ :=
  (List.range 7).foldl (fun acc j => if n.testBit j then acc ^^^ M[j]! else acc) 0

@[expose] def mul7 (M N : Array ℕ) : Array ℕ := N.map (app7 M)

@[expose] def id7 : Array ℕ := #[1, 2, 4, 8, 16, 32, 64]

@[expose] def idA : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def aPart (M : Array ℕ) : List ℕ := (M.toList.drop 1).map (· / 2)

@[expose] def ok7 (M : Array ℕ) : Bool := M.size == 7 && M.all (· < 128)

@[expose] def enum7 (gs : List (Array ℕ)) : List (Array ℕ) :=
  bfsClosure (fun x : Array ℕ => x) (gs.map fun g x => mul7 x g) 100000 [id7]
    ((∅ : Std.HashSet (Array ℕ)).insert id7) []

@[expose] def closed7 (gs X : List (Array ℕ)) : Bool :=
  let S := Std.HashSet.ofList X
  X.all fun x => gs.all fun g => S.contains (mul7 x g)

@[expose] def fix7 (X : Array ℕ) : ℕ := ((List.range 128).filter fun v => app7 X v == v).length

@[expose] def fixEb (r : Array ℕ) : ℕ := ((enumGrp ebRows).filter fun e => mulR r e == mulR e r).length

@[expose] def q0c : ℕ := 516

@[expose] def lam0 : ℕ := 10

@[expose] def t7el : Array ℕ := mk7 lam0 idA

@[expose] def s0Mask (_ : Unit := ()) : ℕ := maskOf (w1List.map (· ^^^ q0c))

@[expose] def tOrbit (_ : Unit := ()) : List ℕ :=
  let m := s0Mask ()
  bfsClosure (fun x : ℕ => x) ((g13Gens ()).map imgMask) 100 [m] ((∅ : Std.HashSet ℕ).insert m) []

@[expose] def stabWords48 : List (List ℕ) :=
  [[1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1], [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1],
    [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0]]

@[expose] def stabGens48 (_ : Unit := ()) : List (Array ℕ) := stabWords48.map (wordRows (g13Gens ()))

@[expose] def s48 (_ : Unit := ()) : List (List ℕ) := ((enumGrp (stabGens48 ())).map res6).dedup

@[expose] def c3List (_ : Unit := ()) : List (Array ℕ) :=
  (s48 ()).flatMap fun A => (List.range 64).map fun l => mk7 l A

@[expose] def itList (_ : Unit := ()) : List ℕ :=
  ((enumGrp ebRows).map fun e => appN e q0c ^^^ q0c).dedup

@[expose] def i7List : List ℕ := [0, 1, 2, 3, 32, 33, 34, 35, 92, 93, 94, 95, 124, 125, 126, 127]

@[expose] def omList : List ℕ := [2, 3, 124, 125, 126, 127]

@[expose] def b7List (_ : Unit := ()) : List (Array ℕ) :=
  (c3List ()).filter fun X => i7List.all fun v => app7 X v == v

@[expose] def pbar (_ : Unit := ()) : List (List ℕ) := ((pList ()).map res6).dedup

@[expose] def t7List (_ : Unit := ()) : List (Array ℕ) :=
  (pbar ()).flatMap fun A => (List.range 64).map fun l => mk7 l A

@[expose] def d7Gens : List (Array ℕ) :=
  [#[1, 2, 100, 9, 120, 94, 53], #[1, 2, 108, 9, 121, 94, 63], #[1, 3, 6, 9, 27, 35, 72]]

@[expose] def r7Gens : List (Array ℕ) :=
  [#[1, 2, 6, 8, 26, 35, 73], #[1, 2, 12, 8, 16, 32, 75], #[1, 2, 14, 8, 27, 34, 66],
    #[1, 2, 5, 8, 17, 32, 65], #[1, 2, 4, 8, 17, 32, 64], #[1, 2, 5, 8, 16, 33, 64]]

@[expose] def wit48 : Array ℕ × Array ℕ :=
  (#[1, 127, 19, 23, 115, 93, 40], #[1, 126, 102, 23, 16, 32, 61])

@[expose] def spanRows48 : Array ℕ := #[1, 5, 8, 21, 64, 512, 3, 40, 192, 276, 1028, 2560]

@[expose] def spanInv48 : Array ℕ := #[1, 65, 3, 4, 10, 132, 16, 272, 521, 32, 1027, 2080]

@[expose] def orbWords48 : List (ℕ × List ℕ) :=
  [(1, [0, 1, 1, 1, 0, 0]), (5, [0, 0, 1, 1, 0, 1]), (8, [0, 0, 1, 1]), (21, [0, 0, 0, 1, 1]),
    (64, [1, 1, 0, 0]), (512, [1, 1, 0, 0, 0, 0]), (513, [0, 0, 0, 0, 0, 1, 0])]

@[expose] def iWit48 : ℕ := 824

@[expose] def ncGens48 (_ : Unit := ()) : List (Array ℕ) :=
  core1Rows ++ ebRows ++ [mulR ((g13Gens ()).headD idR)
    (mulR (core1Rows.headD idR) (Viol.invR ((g13Gens ()).headD idR)))]

@[expose] def stabNcWords48 : List (List ℕ) :=
  [[9, 4, 3, 1, 9], [0, 9, 5, 4, 2, 9, 4, 0], [9, 4, 3, 9, 6]]

@[expose] def ncOrbit (_ : Unit := ()) : List ℕ :=
  let m := s0Mask ()
  bfsClosure (fun x : ℕ => x) ((ncGens48 ()).map imgMask) 100 [m] ((∅ : Std.HashSet ℕ).insert m) []

@[expose] def crdOK48 (_ : Unit := ()) : Bool :=
  w1List.all (fun a => w1List.all fun b => crd6 (a ^^^ b) == (crd6 a ^^^ crd6 b)) &&
    (w1List.map crd6).dedup.length == 64 && w1List.all (fun a => crd6 a < 64) &&
    (List.range 6).all (fun i => crd6 (w1Basis.getD i 0) == 1 <<< i) &&
    w1Basis.all (fun b => w1List.contains b) && lamOf q0c == lam0

@[expose] def stabOK48 (_ : Unit := ()) : Bool :=
  let S := enumGrp (stabGens48 ())
  gensOKb (stabGens48 ()) && (stabGens48 ()).all (fun g => w1List.contains (appN g q0c ^^^ q0c)) &&
    S.contains idR && closedCheck (stabGens48 ()) S && S.dedup.length == 768 &&
    (tOrbit ()).dedup.length == 45

@[expose] def c3OK48 (_ : Unit := ()) : Bool :=
  let C3 := c3List ()
  let B := b7List ()
  let Bs := Std.HashSet.ofList B
  (s48 ()).all (fun A => A.length == 6 && A.all (· < 64)) &&
    C3.dedup.length == 3072 && B.dedup.length == 16 && B.contains t7el &&
    B.all (fun x => B.all fun y => mul7 x y == mul7 y x) && B.all (fun x => mul7 x x == id7) &&
    C3.all (fun X => !(B.all fun b => mul7 X b == mul7 b X) || Bs.contains X)

@[expose] def iOK48 (_ : Unit := ()) : Bool :=
  let It := itList ()
  let C3 := c3List ()
  It.length == 8 && It.all (fun w => w1List.contains w) &&
    It.all (fun w => i7List.contains (2 * crd6 w) && i7List.contains (2 * crd6 w + 1)) &&
    i7List.all (fun c => It.any fun w => crd6 w == c / 2) &&
    It.all (fun w => !inO1b w || (omList.contains (2 * crd6 w) && omList.contains (2 * crd6 w + 1))) &&
    omList.all (fun c => It.any fun w => inO1b w && crd6 w == c / 2) &&
    C3.all (fun X => omList.all fun c => omList.contains (app7 X c)) &&
    omList.all (fun c => C3.any fun X => app7 X 2 == c) &&
    C3.contains wit48.1 && C3.contains wit48.2 &&
    app7 wit48.1 (app7 wit48.2 2) != app7 wit48.2 (app7 wit48.1 2) &&
    inIb iWit48 && w1List.contains (q0c ^^^ iWit48)

@[expose] def tOK48 (_ : Unit := ()) : Bool :=
  let T := t7List ()
  let Ts := Std.HashSet.ofList T
  let B := b7List ()
  let D := enum7 d7Gens
  let R := enum7 r7Gens
  (pbar ()).all (fun A => A.length == 6 && A.all (· < 64) && (s48 ()).contains A) &&
    T.dedup.length == 1024 && B.all (fun b => Ts.contains b) &&
    d7Gens.all ok7 && D.contains id7 && closed7 d7Gens D && D.dedup.length == 64 &&
    D.all (fun x => Ts.contains x) && D.all (fun x => !B.contains x || x == id7) &&
    r7Gens.all ok7 && R.contains id7 && closed7 r7Gens R && R.dedup.length == 64 &&
    R.all (fun x => Ts.contains x) && R.all (fun x => R.all fun y => mul7 x y == mul7 y x) &&
    R.all (fun x => mul7 x x == id7) &&
    T.all (fun X => r7Gens.all fun y => R.any fun y' => mul7 X y == mul7 y' X) &&
    R.any (fun x => aPart x != idA) &&
    T.all (fun X => !(T.all fun Y => mul7 X Y == mul7 Y X) || X == id7 || X == t7el)

@[expose] def fusOK48 (_ : Unit := ()) : Bool :=
  let R := enum7 r7Gens
  let S := enumGrp (stabGens48 ())
  (R.filter fun X => X != id7 &&
    S.any fun r => res6 r == aPart X && 128 ≤ fix7 X * fixEb r).dedup.length ≤ 27

@[expose] def orbOK48 (_ : Unit := ()) : Bool :=
  let N := ncGens48 ()
  orbWords48.all (fun p => w1List.contains (appN (wordRows (g13Gens ()) p.2) q0c ^^^ p.1)) &&
    Viol.okRows spanRows48 && Viol.okRows spanInv48 && mulR spanRows48 spanInv48 == idR &&
    (List.range 6).all (fun i => orbWords48.any fun p => p.1 == spanRows48[i]!) &&
    (List.range 6).all (fun i => spanRows48[i + 6]! == w1Basis.getD i 0) &&
    (b7List ()).contains (mk7 (lamOf 513) idA) && mk7 (lamOf 513) idA != t7el &&
    (q0c ^^^ 513) == 5 &&
    gensOKb N && (stabWords48.zip stabNcWords48).all (fun p =>
      wordRows N p.2 == wordRows (g13Gens ()) p.1) &&
    stabNcWords48.all (fun w => w.all (· < N.length)) && (ncOrbit ()).dedup.length == 45

@[expose] def ok48 (_ : Unit := ()) : Bool :=
  crdOK48 () && stabOK48 () && c3OK48 () && iOK48 () && tOK48 () && fusOK48 () && orbOK48 ()

end CFSG.Quasithin.H13.AS91.Two
