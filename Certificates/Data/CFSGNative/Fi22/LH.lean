module

public import Certificates.Data.CFSGNative.Fi22.Nfp
public import Certificates.Data.CFSGNative.Fi22.LHData
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F4.Native

set_option compiler.extract_closed false

@[expose] def lhFailT (_ : Unit := ()) : Nat := 63

@[expose] def lhFailC (_ : Unit := ()) : Nat := 2751

@[expose] def xiGens : Array Nat := #[3, 5, 29, 44, 89, 148, 186]

abbrev Bits := Array UInt64

@[inline, expose] def bitAt (B : Bits) (x : Nat) : Bool :=
  (B[x / 64]! >>> UInt64.ofNat (x % 64)) &&& 1 != 0

@[inline, expose] def setBit (B : Bits) (x : Nat) : Bits :=
  B.modify (x / 64) fun w => w ||| ((1 : UInt64) <<< UInt64.ofNat (x % 64))

@[expose] def emptyBits (_ : Unit := ()) : Bits := Array.replicate 55 0

@[expose] def bitsOf (xs : Array Nat) : Bits := xs.foldl setBit emptyBits

@[expose] def imgBits (T : Table) (B : Bits) : Bits :=
  Nat.fold 3510 (fun x _ C => if bitAt B x then setBit C (ap T x) else C) emptyBits

@[inline, expose] def pop64 (x : UInt64) : Nat :=
  let x : UInt64 := x - ((x >>> 1) &&& (0x5555555555555555 : UInt64))
  let x : UInt64 := (x &&& (0x3333333333333333 : UInt64)) +
    ((x >>> 2) &&& (0x3333333333333333 : UInt64))
  let x : UInt64 := (x + (x >>> 4)) &&& (0x0f0f0f0f0f0f0f0f : UInt64)
  ((x * (0x0101010101010101 : UInt64)) >>> 56).toNat

@[inline, expose] def andPop (A B : Bits) : Nat :=
  Nat.fold 55 (fun w _ acc => acc + pop64 (A[w]! &&& B[w]!)) 0

@[inline, expose] def andBits (A B : Bits) : Bits :=
  Array.ofFn (n := 55) fun w => A[w.val]! &&& B[w.val]!

@[inline, expose] def diffBits (A B : Bits) : Bits :=
  Array.ofFn (n := 55) fun w => A[w.val]! &&& ~~~B[w.val]!

@[expose] def canonKey (B : Bits) : List Nat := (List.range 3510).filter (bitAt B)

@[expose] def commonCount (A B : Bits) : Nat :=
  (List.range 3510).countP fun x => bitAt A x && bitAt B x

@[noinline, expose] def tauAll (O : COrbit) : Array Table :=
  Array.ofFn (n := 3510) fun c => tabOf O c.val

@[noinline, expose] def commBits (T : Array Table) : Array Bits :=
  Array.ofFn (n := 3510) fun c =>
    Nat.fold 3510 (fun x _ B => if ap T[c.val]! x == x then setBit B x else B) emptyBits

@[inline, expose] def mapsOnto (T : Table) (A B : Bits) : Bool :=
  allIn 0 3510 fun x => bitAt B (ap T x) == bitAt A x

structure LHOrb where
  sets : Array Bits
  pa : Array Nat
  pb : Array Nat
  par : Array Nat
  lab : Array Nat
  tbl : Std.HashMap Bits Nat
deriving Inhabited

@[inline, expose] def LHOrb.find (O : LHOrb) (B : Bits) : Nat := (O.tbl.get? B).getD O.sets.size

@[noinline, expose] def lhOrbitBFS (alpha beta : Table) (S0 : Bits) (limit : Nat) : LHOrb :=
  Id.run do
  let mut sets : Array Bits := #[S0]
  let mut tbl : Std.HashMap Bits Nat := (∅ : Std.HashMap Bits Nat).insert S0 0
  let mut pa : Array Nat := #[]
  let mut pb : Array Nat := #[]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:limit] do
    if h < sets.size then
      let S := sets[h]!
      let A := imgBits alpha S
      match tbl.get? A with
      | some j => pa := pa.push j
      | none =>
        tbl := tbl.insert A sets.size
        pa := pa.push sets.size
        par := par.push h
        lab := lab.push 1
        sets := sets.push A
      let B := imgBits beta S
      match tbl.get? B with
      | some j => pb := pb.push j
      | none =>
        tbl := tbl.insert B sets.size
        pb := pb.push sets.size
        par := par.push h
        lab := lab.push 2
        sets := sets.push B
    else break
  return ⟨sets, pa, pb, par, lab, tbl⟩

@[noinline, expose] def keyTable (sets : Array Bits) : Std.HashMap (List Nat) Nat :=
  (List.range sets.size).foldl (fun K k => K.insert (canonKey sets[k]!) k) ∅

@[inline, expose] def keyFind (K : Std.HashMap (List Nat) Nat) (B : Bits) : Nat :=
  (K.get? (canonKey B)).getD 14080

@[noinline, expose] def edgeWit (T : Array Table) (CB : Array Bits) (A B : Bits) : Nat :=
  let I := andBits A B
  let C := Nat.fold 3510 (fun z _ acc => if bitAt I z then andBits acc CB[z]! else acc)
    (Array.replicate 55 (~~~0))
  let C := diffBits C A
  (List.range 3510).find? (fun k => bitAt C k && mapsOnto T[k]! A B) |>.getD 3510

@[noinline, expose] def commTree (T : Array Table) (S : Array Nat) : Array Nat × Array Nat :=
  Id.run do
  let mut ord : Array Nat := #[0]
  let mut par : Array Nat := #[0]
  let mut seen : Bits := setBit emptyBits 0
  for h in [0:S.size] do
    if h < ord.size then
      let x := ord[h]!
      for y in S do
        if !bitAt seen y && ap T[x]! y == y then
          seen := setBit seen y
          ord := ord.push y
          par := par.push h
    else break
  return (ord, par)

@[expose] def lhUTab (O : COrbit) : Table :=
  reconTab (closTree (nfpBase.map (tabOf O)) 6) (uImg.map (tabOf O)) uImg[0]!

structure LHComp where
  B : Array Bits
  orb : Array LHOrb
  keys : Array (Std.HashMap (List Nat) Nat)
  letters : Array (Array Table)
  trees : Array Tree
  cord : Array (Array Nat)
  cpar : Array (Array Nat)
  uIdx : Array Nat
  rowR : Array Nat
  rowInv : Array Nat
  phi : Array Table
  v0 : Nat
  farTree : Tree
  muW : Array Nat
  mOrd : Array Nat
  mPar : Array Nat
  mWit : Array Nat
  edW : Array Nat
  edF : Array Nat
  edK : Array Nat
deriving Inhabited

@[noinline, expose] def mkRowR (T : Array Table) (B0 : Bits) (O0 : LHOrb) : Array Nat :=
  Array.ofFn (n := 3510) fun f =>
    if bitAt B0 f.val then 14080 else O0.find (imgBits T[f.val]! B0)

@[noinline, expose] def mkRowInv (B0 : Bits) (rowR : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate 14080 3510
  for f in [0:3510] do
    if !bitAt B0 f && rowR[f]! < 14080 then
      r := r.set! rowR[f]! f
  return r

@[noinline, expose] def mkPhi (T : Array Table) (O0 : LHOrb) : Array Table :=
  xiGens.map fun g => Array.ofFn (n := 14080) fun m =>
    UInt32.ofNat (O0.find (imgBits T[g]! O0.sets[m.val]!))

@[inline, expose] def isFar (rowInv : Array Nat) (m : Nat) : Bool := m != 0 && rowInv[m]! == 3510

@[noinline, expose] def mkMuW (T : Array Table) (CB : Array Bits) (B0 : Bits) (O0 : LHOrb)
    (rowR : Array Nat) (v0 : Nat) : Array Nat :=
  Array.ofFn (n := 3510) fun f =>
    if bitAt B0 f.val then 3510 else
      let A := O0.sets[rowR[f.val]!]!
      let V := O0.sets[v0]!
      if andPop A V == 63 then edgeWit T CB A V else 3510

@[noinline, expose] def mkMuTree (T : Array Table) (CB : Array Bits) (O0 : LHOrb)
    (rowR muW : Array Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let M := (List.range 3510).filter fun f => muW[f]! < 3510
  match M with
  | [] => return (#[], #[], #[])
  | f0 :: _ =>
    let mut ord : Array Nat := #[f0]
    let mut par : Array Nat := #[0]
    let mut wit : Array Nat := #[0]
    let mut seen : Bits := setBit emptyBits f0
    for h in [0:M.length] do
      if h < ord.size then
        let A := O0.sets[rowR[ord[h]!]!]!
        for f in M do
          if !bitAt seen f then
            let C := O0.sets[rowR[f]!]!
            if andPop A C == 63 then
              let k := edgeWit T CB A C
              if k < 3510 then
                seen := setBit seen f
                ord := ord.push f
                par := par.push h
                wit := wit.push k
      else break
    return (ord, par, wit)

@[noinline, expose] def mkEdW (T : Array Table) (O0 : LHOrb) (v0 : Nat) : Array Nat :=
  Array.ofFn (n := 3510) fun h =>
    let V := O0.sets[v0]!
    if bitAt V h.val then 14080 else O0.find (imgBits T[h.val]! V)

@[noinline, expose] def mkEd (T : Array Table) (CB : Array Bits) (O0 : LHOrb)
    (rowR rowInv muW edW : Array Nat) (v0 : Nat) : Array Nat × Array Nat := Id.run do
  let M := (List.range 3510).filter fun f => muW[f]! < 3510
  let mut ef : Array Nat := Array.replicate 3510 3510
  let mut ek : Array Nat := Array.replicate 3510 3510
  let V := O0.sets[v0]!
  for h in [0:3510] do
    if !bitAt V h && edW[h]! < 14080 && isFar rowInv edW[h]! then
      let W := O0.sets[edW[h]!]!
      match M.find? (fun f => andPop O0.sets[rowR[f]!]! W == 63 &&
          edgeWit T CB O0.sets[rowR[f]!]! W < 3510) with
      | some f =>
        ef := ef.set! h f
        ek := ek.set! h (edgeWit T CB O0.sets[rowR[f]!]! W)
      | none => pure ()
  return (ef, ek)

@[noinline, expose] def lhCompute (O : COrbit) (T : Array Table) : LHComp :=
  let CB := commBits T
  let B := lhData.map bitsOf
  let orb := B.map fun S => lhOrbitBFS O.alpha O.beta S 20000
  let keys := orb.map fun o => keyTable o.sets
  let letters := lhData.map fun S => S.map fun s => T[s]!
  let trees := (Array.range 2).map fun i => treeBFS 3510 0 letters[i]! (Array.range 351)
  let ct := lhData.map fun S => commTree T S
  let U := lhUTab O
  let uIdx := #[orb[1]!.find (imgBits U B[0]!), orb[0]!.find (imgBits U B[1]!)]
  let O0 := orb[0]!
  let rowR := mkRowR T B[0]! O0
  let rowInv := mkRowInv B[0]! rowR
  let phi := mkPhi T O0
  let v0 := ((List.range 14080).find? fun m => isFar rowInv m).getD 0
  let farTree := treeBFS 14080 v0 phi (Array.range xiGens.size)
  let muW := mkMuW T CB B[0]! O0 rowR v0
  let mt := mkMuTree T CB O0 rowR muW
  let edW := mkEdW T O0 v0
  let ed := mkEd T CB O0 rowR rowInv muW edW v0
  ⟨B, orb, keys, letters, trees, ct.map (·.1), ct.map (·.2), uIdx, rowR, rowInv, phi, v0,
    farTree, muW, mt.1, mt.2.1, mt.2.2, edW, ed.1, ed.2⟩

@[inline, expose] def anyBelow (n : Nat) (p : Nat → Bool) : Bool := (List.range n).any p

@[expose] def prodC (c : Nat) : Nat := (List.range 6).foldl (fun acc i => f4mul acc (coord c i)) 1

@[expose] def hypC (j c : Nat) : Bool := weightC c == 2 || (weightC c == 6 && prodC c == j + 1)

@[noinline, expose] def dataOK (L : Array (Array Nat)) : Bool :=
  L.size == 2 && L.all fun S => S.size == 351 && S[0]! == 0 &&
    allIn 0 350 (fun k => S[k]! < S[k + 1]!) && S[350]! < 3510

@[noinline, expose] def memOK (B : Bits) (S : Array Nat) : Bool :=
  allIn 0 3510 fun x => bitAt B x == S.contains x

@[noinline, expose] def closedOK (T : Array Table) (B : Bits) : Bool :=
  allIn 0 3510 fun s => !bitAt B s || allIn 0 3510 fun t => !bitAt B t || bitAt B (ap T[s]! t)

@[noinline, expose] def starOK (ea : Array Nat) (B : Bits) (j : Nat) : Bool :=
  allIn 0 693 fun u => bitAt B ea[phiPos[u]!]! == hypC j uPts[u]!

@[noinline, expose] def rootTreeOK (T : Array Table) (S : Array Nat) (letters : Array Table)
    (tr : Tree) : Bool :=
  letters.size == 351 && allIn 0 351 (fun l => letters[l]! == T[S[l]!]!) &&
    treeOK 3510 0 tr letters (Array.range 351) &&
    S.all (fun x => ap tr.pos x < tr.pts.size && ap tr.pts (ap tr.pos x) == x)

@[noinline, expose] def commTreeOK (T : Array Table) (S : Array Nat) (B : Bits)
    (ord par : Array Nat) : Bool :=
  ord.size == 351 && par.size == 351 && ord[0]! == 0 &&
    allIn 1 351 (fun k => par[k]! < k && bitAt B ord[k]! &&
      ap T[ord[par[k]!]!]! ord[k]! == ord[k]! && ord[par[k]!]! != ord[k]!) &&
    S.all (fun x => ord.contains x)

@[noinline, expose] def domOK (T : Array Table) (B : Bits) : Bool :=
  allIn 0 3510 fun f => bitAt B f ||
    (anyBelow 3510 (fun x => bitAt B x && ap T[f]! x == x) &&
      anyBelow 3510 (fun x => bitAt B x && ap T[f]! x != x))

@[noinline, expose] def count63OK (T : Array Table) (B : Bits) : Bool :=
  allIn 0 3510 fun f => bitAt B f ||
    (List.range 3510).countP (fun x => bitAt B x && ap T[f]! x == x) == 63

@[noinline, expose] def failOK (T : Array Table) (ep : Array Nat) : Bool :=
  let t := lhFailT
  let c := lhFailC
  ep[t]! < 693 && hypC 1 uPts[phiData[ep[t]!]!]! && ap T[t]! c == c && c != t &&
    ap T[0]! c != c &&
    allIn 0 3510 fun x =>
      ((ep[x]! < 693 && hypC 1 uPts[phiData[ep[x]!]!]!) && ap T[t]! x == x && x != t) ==
        (ap T[t]! x == x && x != t && ap T[0]! x == x && x != 0 && ap T[c]! x == x && x != c)

@[noinline, expose] def orbitOK (alpha beta : Table) (B : Bits) (o : LHOrb)
    (K : Std.HashMap (List Nat) Nat) : Bool :=
  o.sets.size == 14080 && o.pa.size == 14080 && o.pb.size == 14080 && o.par.size == 14080 &&
    o.lab.size == 14080 && allIn 0 3510 (fun x => bitAt o.sets[0]! x == bitAt B x) &&
    parAll 14080 3 (fun k => o.pa[k]! < 14080 && o.pb[k]! < 14080 &&
      mapsOnto alpha o.sets[k]! o.sets[o.pa[k]!]! && mapsOnto beta o.sets[k]! o.sets[o.pb[k]!]!) &&
    allIn 1 14080 (fun k => o.par[k]! < k &&
      ((o.lab[k]! == 1 && o.pa[o.par[k]!]! == k) || (o.lab[k]! == 2 && o.pb[o.par[k]!]! == k))) &&
    parAll 14080 3 (fun k => keyFind K o.sets[k]! == k)

@[noinline, expose] def swapOK (U : Table) (B0 B1 : Bits) (o0 o1 : LHOrb) (uIdx : Array Nat) :
    Bool :=
  uIdx.size == 2 && uIdx[0]! < 14080 && mapsOnto U B0 o1.sets[uIdx[0]!]! &&
    uIdx[1]! < 14080 && mapsOnto U B1 o0.sets[uIdx[1]!]!

@[noinline, expose] def rowOK (T : Array Table) (B0 : Bits) (o0 : LHOrb)
    (rowR rowInv : Array Nat) : Bool :=
  rowR.size == 3510 && rowInv.size == 14080 &&
    allIn 0 3510 (fun f => bitAt B0 f || (rowR[f]! < 14080 && rowR[f]! != 0 &&
      mapsOnto T[f]! B0 o0.sets[rowR[f]!]! && rowInv[rowR[f]!]! == f)) &&
    allIn 0 14080 (fun m => rowInv[m]! == 3510 ||
      (rowInv[m]! < 3510 && !bitAt B0 rowInv[m]! && rowR[rowInv[m]!]! == m))

@[noinline, expose] def phiOK (T : Array Table) (B0 : Bits) (o0 : LHOrb) (phi : Array Table) :
    Bool :=
  phi.size == xiGens.size && allIn 0 xiGens.size fun l =>
    xiGens[l]! < 3510 && bitAt B0 xiGens[l]! && phi[l]!.size == 14080 &&
      parAll 14080 3 fun m => ap phi[l]! m < 14080 &&
        mapsOnto T[xiGens[l]!]! o0.sets[m]! o0.sets[ap phi[l]! m]!

@[noinline, expose] def farOK (rowInv : Array Nat) (phi : Array Table) (v0 : Nat) (tr : Tree) :
    Bool :=
  v0 < 14080 && isFar rowInv v0 && treeOK 14080 v0 tr phi (Array.range xiGens.size) &&
    allIn 0 14080 fun m => !isFar rowInv m ||
      (ap tr.pos m < tr.pts.size && ap tr.pts (ap tr.pos m) == m)

@[noinline, expose] def muOK (T : Array Table) (B0 : Bits) (o0 : LHOrb)
    (rowR muW mOrd mPar mWit : Array Nat) (v0 : Nat) : Bool :=
  let V := o0.sets[v0]!
  muW.size == 3510 &&
    allIn 0 3510 (fun f => bitAt B0 f ||
      (if muW[f]! < 3510 then
        !bitAt o0.sets[rowR[f]!]! muW[f]! && mapsOnto T[muW[f]!]! o0.sets[rowR[f]!]! V
      else commonCount o0.sets[rowR[f]!]! V != 63)) &&
    0 < mOrd.size && mPar.size == mOrd.size && mWit.size == mOrd.size &&
    allIn 0 mOrd.size (fun k => mOrd[k]! < 3510 && !bitAt B0 mOrd[k]! && muW[mOrd[k]!]! < 3510) &&
    allIn 1 mOrd.size (fun k => mPar[k]! < k && mWit[k]! < 3510 &&
      !bitAt o0.sets[rowR[mOrd[mPar[k]!]!]!]! mWit[k]! &&
      mapsOnto T[mWit[k]!]! o0.sets[rowR[mOrd[mPar[k]!]!]!]! o0.sets[rowR[mOrd[k]!]!]!) &&
    allIn 0 3510 (fun f => bitAt B0 f || muW[f]! == 3510 || mOrd.contains f)

@[noinline, expose] def edOK (T : Array Table) (B0 : Bits) (o0 : LHOrb)
    (rowR rowInv muW edW edF edK : Array Nat) (v0 : Nat) : Bool :=
  let V := o0.sets[v0]!
  allIn 0 3510 fun h => bitAt V h || (edW[h]! < 14080 && mapsOnto T[h]! V o0.sets[edW[h]!]! &&
    (!isFar rowInv edW[h]! || (edF[h]! < 3510 && !bitAt B0 edF[h]! && muW[edF[h]!]! < 3510 &&
      edK[h]! < 3510 && !bitAt o0.sets[rowR[edF[h]!]!]! edK[h]! &&
      mapsOnto T[edK[h]!]! o0.sets[rowR[edF[h]!]!]! o0.sets[edW[h]!]!)))

@[noinline, expose] def lhChecks (O : COrbit) (T : Array Table) (C : LHComp) : Bool :=
  let ea := eaPts O
  T.size == 3510 && dataOK lhData && C.B.size == 2 && C.orb.size == 2 && C.keys.size == 2 &&
    C.letters.size == 2 && C.trees.size == 2 && C.cord.size == 2 && C.cpar.size == 2 &&
    allIn 0 2 (fun i => memOK C.B[i]! lhData[i]! && closedOK T C.B[i]! &&
      starOK ea C.B[i]! (2 * i) && rootTreeOK T lhData[i]! C.letters[i]! C.trees[i]! &&
      commTreeOK T lhData[i]! C.B[i]! C.cord[i]! C.cpar[i]! && domOK T C.B[i]! &&
      orbitOK O.alpha O.beta C.B[i]! C.orb[i]! C.keys[i]!) &&
    count63OK T C.B[0]! && failOK T (ePos ea) && keyFind C.keys[0]! C.B[1]! == 14080 &&
    swapOK (lhUTab O) C.B[0]! C.B[1]! C.orb[0]! C.orb[1]! C.uIdx &&
    rowOK T C.B[0]! C.orb[0]! C.rowR C.rowInv && phiOK T C.B[0]! C.orb[0]! C.phi &&
    farOK C.rowInv C.phi C.v0 C.farTree &&
    muOK T C.B[0]! C.orb[0]! C.rowR C.muW C.mOrd C.mPar C.mWit C.v0 &&
    edOK T C.B[0]! C.orb[0]! C.rowR C.rowInv C.muW C.edW C.edF C.edK C.v0

@[expose] def lhCertificate (_ : Unit) : Bool :=
  let O := orbitData ()
  let T := tauAll O
  lhChecks O T (lhCompute O T)

end CFSG.Sporadic.Fi22.Native
