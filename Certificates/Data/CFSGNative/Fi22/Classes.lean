module

public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.CFSGNative.Fi22.ClassesData

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def jGen (L : Array Table) (z : Int) : Table := L[z.toNat]!

@[expose] def sylLetters (L : Array Table) : Array Table := buildLetters 3510 (jGen L) sylWords

@[expose] def treeTabs (n : Nat) (T : Tree) (letters : Array Table) : Array Table :=
  Array.ofFn (n := T.pts.size) fun k => (walk T letters k.val (Array.range n)).map UInt32.ofNat

@[expose] def idOK (n : Nat) (P : Table) : Bool := allIn 0 n fun i => ap P i == i

@[expose] def conjTabs (O : COrbit) : Array (Table × Table) :=
  conjWords.map fun w => let W := wordT 3510 (genTables O) w; (W, invT 3510 W)

@[expose] def leafOK (A : Table) (ws : Array (Table × Table)) (P : Table) : Bool :=
  !invoOK 3510 P || idOK 3510 P || order3OK 3510 (compT 3510 P A) ||
    ws.any fun W =>
      let R := compT 3510 P (compT 3510 (compT 3510 W.1 P) W.2)
      !idOK 3510 R && !invoOK 3510 R && !order3OK 3510 R

@[expose] def sylChecks (O : COrbit) (chunks : Nat) : Bool :=
  let LJ := chainLetters O
  let L := sylLetters LJ
  let T := chainTrees 3510 L sylBase
  let t0 := treeTabs 3510 T[0]! L
  let t1 := treeTabs 3510 T[1]! L
  let ws := conjTabs O
  (sylWords.all fun w => w.all fun z => z.toNat < LJ.size) &&
    chainOK 3510 L sylBase chainQ sylQb T chunks && orbitSizes T == [1024, 128] &&
    ws.all (fun W => invOK 3510 W.1 W.2) &&
    parAll t0.size chunks fun k => t1.all fun B => leafOK O.alpha ws (compT 3510 t0[k]! B)

@[expose] def classesCertificate (chunks : Nat) : Bool := sylChecks (orbitData ()) chunks

end CFSG.Sporadic.Fi22.Native
