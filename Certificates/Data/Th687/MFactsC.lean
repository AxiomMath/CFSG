module

public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.Th.Recog.JLettersInputs
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Recognition.PresentedWordsClosure
public import CFSG.Sporadic.Th.Max3.CentA

public section

namespace CFSG.Sporadic.Th.Recog.MFactsCData

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def commR (X Y : Array V4) : Bool := eqRows (mulRows X Y) (mulRows Y X)

@[expose] def rowsUI (U : Array V4) : Array V4 := powRows U 3

@[expose] def rowsX1 (C D : Array V4) : Array V4 := powRows (mulRows C D) 2

@[expose] def rowsW1 (D E : Array V4) : Array V4 := mulRows D E

@[expose] def rowsW1I (D E : Array V4) : Array V4 := mulRows E D

@[expose] def rowsY1 (W1 X1 W1I : Array V4) : Array V4 :=
  mulRows (mulRows W1 X1) W1I

@[expose] def rowsX2 (U X1 UI : Array V4) : Array V4 := mulRows (mulRows U X1) UI

@[expose] def rowsW2 (U W1 UI : Array V4) : Array V4 := mulRows (mulRows U W1) UI

@[expose] def rowsE0 (C D : Array V4) : Array V4 := mulRows (mulRows D C) D

@[expose] def rowsE1 (U E0 UI : Array V4) : Array V4 := mulRows (mulRows U E0) UI

@[expose] def rowsE8 (Z E0 E1 : Array V4) (l : Fin 8) : Array V4 :=
  mulRows (mulRows (powRows Z (l.val % 2)) (powRows E0 (l.val / 2 % 2)))
    (powRows E1 (l.val / 4))

@[expose] def e8Tab (Z E0 E1 : Array V4) : Array (Array V4) :=
  Array.ofFn fun l : Fin 8 => rowsE8 Z E0 E1 l

@[expose] def rowsPRE (W1 W2 D : Array V4) (a : Fin 18) : Array V4 :=
  mulRows (mulRows (powRows W1 (a.val / 6)) (powRows W2 (a.val / 2 % 3)))
    (powRows D (a.val % 2))

@[expose] def preTab (W1 W2 D : Array V4) : Array (Array V4) :=
  Array.ofFn fun a : Fin 18 => rowsPRE W1 W2 D a

@[expose] def neTab (C D E U UI : Array V4) : Array (Array V4) :=
  #[C,
    mulRows (mulRows (mulRows (mulRows D E) U) D) UI,
    mulRows (mulRows (mulRows (mulRows D E) U) D) U,
    mulRows (mulRows (mulRows D U) D) U,
    mulRows (mulRows (mulRows D U) D) UI]

@[expose] def neTgt0 : Array Nat := #[3, 4, 5, 6, 7]

@[expose] def neTgt1 : Array Nat := #[5, 2, 3, 3, 2]

@[expose] def ceTab (S T : Array V4) : Array (Array V4) :=
  #[idRows, S, powRows S 6, powRows S 2, mulRows S (powRows T 2), powRows S 5,
    mulRows (powRows S 6) (powRows T 2)]

@[expose] def ceiTab (S T : Array V4) : Array (Array V4) :=
  #[idRows, powRows S 6, S, powRows S 5, mulRows T (powRows S 6), powRows S 2, mulRows T S]

@[expose] def cnTab (D E U S T : Array V4) : Array (Array V4) :=
  #[mulRows (mulRows (mulRows D E) U) D, S, powRows S 2, powRows S 3,
    mulRows (mulRows (mulRows D E) D) T,
    mulRows (mulRows S (mulRows (mulRows D E) D)) S]

@[expose] def cniTab (D E UI S T : Array V4) : Array (Array V4) :=
  #[mulRows (mulRows (mulRows D UI) E) D, powRows S 6, powRows S 5, powRows S 4,
    mulRows (powRows T 2) (mulRows (mulRows D E) D),
    mulRows (mulRows (powRows S 6) (mulRows (mulRows D E) D)) (powRows S 6)]

@[expose] def checkR687011 (_ : Unit := ()) : Bool :=
  let C := rowsWJ 2
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let UI := rowsUI U
  let X1 := rowsX1 C D
  let W1 := rowsW1 D E
  let W1I := rowsW1I D E
  let Y1 := rowsY1 W1 X1 W1I
  let X2 := rowsX2 U X1 UI
  let W2 := rowsW2 U W1 UI
  eqRows (mulRows Y1 X1) (mulRows (powRows X1 3) Y1) &&
    eqRows (mulRows W1 Y1) (mulRows (mulRows Y1 X1) W1) &&
    commR X1 X2 && commR X1 W2 && commR W1 X2 && commR W1 W2

@[expose] def checkE687011 (_ : Unit := ()) : Bool :=
  let C := rowsWJ 2
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let UI := rowsUI U
  let E0 := rowsE0 C D
  let E1 := rowsE1 U E0 UI
  let E8t := e8Tab rowsA E0 E1
  commR E0 E1 &&
    (List.finRange 8).all fun l =>
      (List.finRange l).all fun l' => eqRows E8t[l]! E8t[l']! == false

@[expose] def checkN687011 (_ : Unit := ()) : Bool :=
  let C := rowsWJ 2
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let UI := rowsUI U
  let T := rowsWJ 6
  let E0 := rowsE0 C D
  let E1 := rowsE1 U E0 UI
  let E8t := e8Tab rowsA E0 E1
  let NEt := neTab C D E U UI
  (List.finRange 5).all fun i =>
    let ne := NEt[i]!
    commR ne T &&
      eqRows (mulRows ne E0) (mulRows E8t[neTgt0[i]!]! ne) &&
      eqRows (mulRows ne E1) (mulRows E8t[neTgt1[i]!]! ne)

@[expose] def checkCE687011 (_ : Unit := ()) : Bool :=
  let C := rowsWJ 2
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let UI := rowsUI U
  let T := rowsWJ 6
  let E0 := rowsE0 C D
  let E1 := rowsE1 U E0 UI
  let E8t := e8Tab rowsA E0 E1
  let W1 := rowsW1 D E
  let W2 := rowsW2 U W1 UI
  let PREt := preTab W1 W2 D
  let NF := rowsNfTab
  (List.finRange 512).all fun k =>
    let nf := NF[k]!
    !commR nf T ||
      (List.finRange 18).all fun a =>
        let P := mulRows PREt[a]! nf
        !(commR P E0 && commR P E1) ||
          (a = 0 && (List.finRange 8).any fun l => eqRows nf E8t[l]!)

@[expose] def checkC687011 (_ : Unit := ()) : Bool :=
  let C := rowsWJ 2
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let S := rowsWJ 5
  let T := rowsWJ 6
  let E0 := rowsE0 C D
  let CEt := ceTab S T
  let CEIt := ceiTab S T
  let CNt := cnTab D E U S T
  let CNIt := cniTab D E (rowsUI U) S T
  (List.finRange 7).all (fun i =>
      eqRows (mulRows CEt[i]! CEIt[i]!) idRows && commR CEt[i]! E0) &&
    (List.finRange 6).all fun j =>
      eqRows (mulRows CNt[j]! CNIt[j]!) idRows && commR CNt[j]! E0

@[expose] def checkA687011 (_ : Unit := ()) : Bool :=
  let C := rowsWJ 2
  let D := rowsWJ 3
  let E := rowsWJ 4
  let U := rowsWJ 7
  let UI := rowsUI U
  let S := rowsWJ 5
  let T := rowsWJ 6
  let E0 := rowsE0 C D
  let E1 := rowsE1 U E0 UI
  let E8t := e8Tab rowsA E0 E1
  let E1E8 := Array.ofFn fun l : Fin 8 => mulRows E1 E8t[l.val]!
  let CEt := ceTab S T
  let CEIt := ceiTab S T
  let CNt := cnTab D E U S T
  let CNIt := cniTab D E UI S T
  let NF := rowsNfTab
  (List.finRange 512).all fun k =>
    let nf := NF[k]!
    !commR nf E0 ||
      (List.finRange 4).any (fun l => eqRows nf E8t[l]!) ||
      (List.finRange 6).any (fun j =>
        !commR (mulRows (mulRows CNt[j]! nf) CNIt[j]!) nf) ||
      (List.finRange 7).any fun i =>
        (List.finRange 4).any fun l =>
          eqRows (mulRows (mulRows CEt[i]! nf) CEIt[i]!) E1E8[l]!

theorem e8Tab_get (Z E0 E1 : Array V4) (l : Fin 8) :
    (e8Tab Z E0 E1)[l.val]! = rowsE8 Z E0 E1 l := by
  rw [getElem!_pos _ _ (by simp [e8Tab])]
  simp [e8Tab]

theorem preTab_get (W1 W2 D : Array V4) (a : Fin 18) :
    (preTab W1 W2 D)[a.val]! = rowsPRE W1 W2 D a := by
  rw [getElem!_pos _ _ (by simp [preTab])]
  simp [preTab]

theorem rowsNfTab_get (k : Fin 512) : rowsNfTab[k.val]! = rowsNfAt k := by
  rw [getElem!_pos _ _ (by simp [rowsNfTab])]
  rfl

end CFSG.Sporadic.Th.Recog.MFactsCData
