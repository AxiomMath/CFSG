module

public import Certificates.Data.CFSGNative.AS91.M24Trio

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def r121IdTab : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def compose (a b : Array Nat) : Array Nat :=
  (Array.range 24).map fun i => a[b[i]!]!

@[expose] def prodTab (s : Nat) : Array Nat :=
  (List.range 6).foldl
    (fun acc j => if s.testBit j then compose acc (tTabs.getD j #[]) else acc) r121IdTab

@[expose] def genTabCheck (_ : Unit := ()) : Bool :=
  (List.range 6).all (fun j => prodTab (1 <<< j) == tTabs.getD j #[]) && prodTab 0 == r121IdTab

@[expose] def mulTabCheck (_ : Unit := ()) : Bool :=
  (List.range 64).all fun s => (List.range 64).all fun s' =>
    compose (prodTab s) (prodTab s') == prodTab (s ^^^ s')

@[expose] def distinctTabCheck (_ : Unit := ()) : Bool :=
  (List.range 64).all fun s => (List.range s).all fun s' =>
    (List.range 24).any fun i => (prodTab s)[i]! != (prodTab s')[i]!

@[expose] def groupCheck (_ : Unit := ()) : Bool :=
  genTabCheck () && mulTabCheck () && distinctTabCheck ()

@[expose] def sextsOfTrio (T : Array (Nat × Nat × Nat)) (S : Array (List Nat)) (p : Nat) :
    List Nat :=
  (List.range nSext).filter fun q => trioIn T[p]! S[q]!

@[expose] def fixCopCheck (_ : Unit := ()) : Bool :=
  let T := trioList ()
  let S := sextList ()
  let row0 := sextsOfTrio T S 0
  let P := (List.range 63).map fun s => prodTab (s + 1)
  (List.range nTrio).all fun p =>
    let fixing := P.filter fun t => (octsT T[p]!).all fun o => img t o == o
    fixing.isEmpty ||
      (let row := sextsOfTrio T S p
       fixing.all fun t =>
         !(row.all fun q => S[q]!.all fun x => S[q]!.contains (img t x)) ||
           row0.any fun q => row.contains q)

@[expose] def r121Check (_ : Unit := ()) : Bool := groupCheck () && fixCopCheck ()

end CFSG.Quasithin.H13.AS91.M24G.Native
