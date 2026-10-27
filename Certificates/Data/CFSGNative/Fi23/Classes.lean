module

public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Data.CFSGNative.Fi23.ClassesData

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def jGen (L : Array Table) (z : Int) : Table := L[z.toNat]!

@[expose] def sylLetters (L : Array Table) : Array Table := buildLetters 31671 (jGen L) sylWords

@[expose] def treeTabs (n : Nat) (T : Tree) (letters : Array Table) : Array Table :=
  Array.ofFn (n := T.pts.size) fun k => (walk T letters k (Array.range n)).map UInt32.ofNat

@[expose] def dLetters (_ : Unit := ()) : List Int := dWord.map fun x => if x = 0 then 1 else 2

@[expose] def dTab (O : WOrbit) : Table := powT 31671 7 (wordT 31671 (genTables O) dLetters)

@[expose] def conjTabs (O : WOrbit) (D : Table) : Array (Table × Table × Table) :=
  conjWords.map fun w =>
    let W := wordT 31671 (genTables O) w
    let Wi := invT 31671 W
    (W, Wi, compT 31671 W (compT 31671 D Wi))

@[expose] def invo2OK (n : Nat) (A B : Table) : Bool :=
  allIn 0 n fun i => ap A (ap B (ap A (ap B i))) == i

@[expose] def leafOK (ws : Array (Table × Table × Table)) (P : Table) : Bool :=
  isIdT P || ws.any fun W =>
    order3OK 31671 (compT 31671 P W.2.2) ||
      let R := compT 31671 P (compT 31671 (compT 31671 W.1 P) W.2.1)
      !isIdT R && !invoOK 31671 R && !order3OK 31671 R

@[expose] def pairOK (ws : Array (Table × Table × Table)) (A B : Table) : Bool :=
  !invo2OK 31671 A B || leafOK ws (compT 31671 A B)

@[expose] def sylChecks (O : WOrbit) (chunks : Nat) : Bool :=
  let LJ := chainLetters O
  let L := sylLetters LJ
  let T := chainTrees 31671 L sylBase
  let t0 := treeTabs 31671 T[0]! L
  let t1 := treeTabs 31671 T[1]! L
  let ws := conjTabs O (dTab O)
  (sylWords.all fun w => w.all fun z => z.toNat < LJ.size) &&
    chainOK 31671 L sylBase chainQ sylQb T chunks && orbitSizes T == [512, 512] &&
    ws.all (fun W => invOK 31671 W.1 W.2.1) &&
    parAll t0.size chunks fun k => t1.all fun B => pairOK ws t0[k]! B

@[expose] def classesCertificate (chunks : Nat) : Bool := sylChecks (orbitData ()) chunks

end CFSG.Sporadic.Fi23.Native
