module

public import Certificates.Data.CFSGNative.Ly.Certificate
public import Certificates.Data.CFSGNative.LySchreier.Data

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

set_option compiler.extract_closed false

@[expose] def parseInts (s : String) : List Int :=
  (s.splitOn " ").filterMap fun t => (t.replace "\n" "").toInt?

@[expose] def parseNats (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap fun t => (t.replace "\n" "").toNat?).toArray

@[expose] def digitsTxt (s : String) : Array Nat := digitsOf (s.replace "\n" "")

@[expose] def bpRootArr : Array Nat := digitsTxt rootDigitsTxt

@[expose] def bpRootKey : ByteArray :=
  encodeDigits fun p => if p < 826 then bpRootArr[p]! else 0

@[expose] def bpForm : Array (Array Nat) := matOfDigits (formDigitsTxt.replace "\n" "")

@[expose] def bpOrbit (_ : Unit) : KOrbit := bfsPar tabA tabB bpRootKey nPts 4096 4

@[expose] def bpRootChecks (_ : Unit) : Bool :=
  bpRootKey.size == 276 && allIn 0 276 (fun q => (bpRootKey.get! q).toNat < 125) &&
    rrefOK (keyRows bpRootKey) #[0, 1, 2, 3, 4, 5, 6] &&
    mul7 (keyS bpRootKey) (inv7 (keyS bpRootKey)) == id7

@[expose] def formCertificate (_ : Unit) : Bool :=
  bpRootChecks () && bpRootArr.size == 826 && allIn 0 826 (fun p => bpRootArr[p]! < 5) &&
    bpForm.size == 111 && (bpForm.all fun r => r.size == 111) &&
    allIn 0 111 (fun i => allIn 0 111 fun j => bpForm[i]![j]! % 5 == 4 * formF[i]![j]! % 5) &&
    mulM 5 111 formF (invM 5 111 formF) == idM 111

@[inline, expose] def orbitDiscPos (O : KOrbit) (k : Nat) : Nat := 2 * ap O.par k + (ap O.lab k - 1)

@[expose] def bfsOrderOK (O : KOrbit) : Bool :=
  let n := O.keys.size
  allIn 1 (n - 1) (fun k => orbitDiscPos O k < orbitDiscPos O (k + 1)) &&
    allIn 0 n (fun i => (ap O.alpha i == 0 || orbitDiscPos O (ap O.alpha i) ≤ 2 * i) &&
      (ap O.beta i == 0 || orbitDiscPos O (ap O.beta i) ≤ 2 * i + 1))

@[expose] def fixedIdx : Array Nat := parseNats fixedIndicesTxt

@[expose] def fixedPerm0 : Array Nat := parseNats fixedPerm0Txt

@[expose] def fixedPerm1 : Array Nat := parseNats fixedPerm1Txt

@[expose] def fixedPerm (j : Nat) : Array Nat := if j = 0 then fixedPerm0 else fixedPerm1

@[expose] def seedWord0 : List Int := parseInts seedWord0Txt

@[expose] def seedWord1 : List Int := parseInts seedWord1Txt

@[expose] def seedWord (j : Nat) : List Int := if j = 0 then seedWord0 else seedWord1

@[expose] def maskOf (n : Nat) (xs : Array Nat) : Array Bool :=
  xs.foldl (fun m x => m.set! x true) (Array.replicate n false)

@[expose] def fixedSetOK (n : Nat) (alpha : Table) (fi : Array Nat) : Bool :=
  let m := maskOf n fi
  fi.size == 2772 && allIn 0 (fi.size - 1) (fun k => fi[k]! < fi[k + 1]!) &&
    allIn 0 fi.size (fun k => fi[k]! < n) &&
    allIn 0 n (fun i => (ap alpha i == i) == m[i]!)

@[inline, expose] def seedTab (alpha beta betaInv : Table) (l : Int) : Table :=
  if 0 < l then (if l.toNat - 1 = 0 then alpha else beta)
  else (if (-l).toNat - 1 = 0 then alpha else betaInv)

@[expose] def wordAp (tab : Int → Table) (w : List Int) (x : Nat) : Nat :=
  w.foldr (fun l y => ap (tab l) y) x

@[expose] def seedPermOK (tab : Int → Table) (fi : Array Nat) (p : Nat → Array Nat)
    (w : Nat → List Int) : Bool :=
  allIn 0 2 fun j => (p j).size == fi.size && allIn 0 fi.size fun k =>
    (p j)[k]! < fi.size && wordAp tab (w j) fi[k]! == fi[(p j)[k]!]!

@[expose] def transTree (m : Nat) (p : Nat → Array Nat) : Array Nat × Array Nat × Array Nat :=
  Id.run do
  let mut seen : Array Bool := (Array.replicate m false).set! 0 true
  let mut pts : Array Nat := #[0]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:m] do
    if h < pts.size then
      let x := pts[h]!
      for j in [0:2] do
        let y := (p j)[x]!
        if y < m && !seen[y]! then
          seen := seen.set! y true
          pts := pts.push y
          par := par.push h
          lab := lab.push j
  return (pts, par, lab)

@[expose] def posOf (m : Nat) (pts : Array Nat) : Array Nat := Id.run do
  let mut pos : Array Nat := Array.replicate m 0
  for k in [0:pts.size] do
    pos := pos.set! pts[k]! k
  return pos

@[expose] def treeReachOK (m : Nat) (p : Nat → Array Nat) (pts par lab pos : Array Nat) :
    Bool :=
  pts.size == m && par.size == m && lab.size == m && pts[0]! == 0 &&
    allIn 1 m (fun k =>
      par[k]! < k && lab[k]! < 2 && (p lab[k]!)[pts[par[k]!]!]! == pts[k]!) &&
    allIn 0 m (fun y => pos[y]! < m && pts[pos[y]!]! == y)

@[expose] def transOK (_ : Unit) : Bool :=
  let T := transTree 2772 fixedPerm
  treeReachOK 2772 fixedPerm T.1 T.2.1 T.2.2 (posOf 2772 T.1)

@[expose] def orbitCertificate (_ : Unit) : Bool :=
  let O := bpOrbit ()
  let bi := invT nPts O.beta
  let tab := seedTab O.alpha O.beta bi
  orbitOK tabA tabB bpRootKey O 3 && O.keys.size == nPts && invOK nPts O.beta bi &&
    bfsOrderOK O && fixedSetOK nPts O.alpha fixedIdx &&
    seedPermOK tab fixedIdx fixedPerm seedWord && transOK () &&
    wordAp tab transporterWord 0 == fixedIndex && ap O.alpha fixedIndex == fixedIndex

end CFSG.Sporadic.LySchreier.Native
