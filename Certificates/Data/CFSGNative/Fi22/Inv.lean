module

public import Certificates.Data.CFSGNative.Fi22.Classes
public import Certificates.Data.CFSGNative.Fi22.Centralizer
public import Certificates.Data.CFSGNative.Fi22.InvData

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def fixLeaf (A B : Table) : Bool :=
  !allIn 0 3510 (fun i => ap A (ap B (ap A (ap B i))) == i) ||
    allIn 0 3510 (fun i => ap A (ap B i) == i) ||
    (let c := (List.range 3510).countP fun i => ap A (ap B i) == i
     c == 54 || c == 182 || c == 694)

@[expose] def stabChecks (O : COrbit) : Bool :=
  let bi := genTables O (-2)
  let W1 := wit1.map (cTab O bi)
  let W2 := wit2.map (cTab O bi)
  wit1.all (· < 3510) && wit2.all (· < 3510) &&
    W1.all (fun T => ap T 0 == 0 && ap T 1 == 1) &&
    W2.all (fun T => ap T 0 == 0 && ap T subRoot == subRoot) &&
    ap O.alpha subRoot == subRoot && ap O.alpha 1 != subRoot &&
    allIn 0 3510 (fun p => p == 0 || p == 1 || p == ap O.alpha 1 ||
      W1.any fun T => ap T p != p) &&
    allIn 0 3510 (fun p => p == 0 || p == subRoot || W2.any fun T => ap T p != p)

@[expose] def fixExact (P : Table) (c : Nat) : Bool :=
  invoOK 3510 P && !idOK 3510 P && (List.range 3510).countP (fun i => ap P i == i) == c

@[expose] def attainChecks (O : COrbit) : Bool :=
  let bi := genTables O (-2)
  fixWords.all fun w => w.1.all (· < 3510) && fixExact (wordTab O bi w.1) w.2

@[expose] def invChecks (O : COrbit) (chunks : Nat) : Bool :=
  let LJ := chainLetters O
  let L := sylLetters LJ
  let T := chainTrees 3510 L sylBase
  let t0 := treeTabs 3510 T[0]! L
  let t1 := treeTabs 3510 T[1]! L
  stabChecks O && attainChecks O &&
    parAll t0.size chunks fun k => t1.all fun B => fixLeaf t0[k]! B

@[expose] def invCertificate (chunks : Nat) : Bool := invChecks (orbitData ()) chunks

end CFSG.Sporadic.Fi22.Native
