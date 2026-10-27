module

public import Certificates.Data.CFSGNative.Fi23.Centralizer
public import Certificates.Data.CFSGNative.Fi23.TrData
public import Certificates.Data.CFSGNative.Fi22.LHData
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def failC (_ : Unit := ()) : Nat := 11504

@[expose] def cGens : Array Nat := #[1, 32, 37, 39, 49, 52, 53, 59, 64]

@[expose] def rRoot (_ : Unit := ()) : Nat := 71

@[expose] def csV (_ : Unit := ()) : Nat := 71

@[expose] def csW (_ : Unit := ()) : Nat := 92

@[expose] def xiGens : Array Nat := #[1, 32, 37, 39, 49, 52, 53, 59, 64, 71]

abbrev PBits := ByteArray

@[inline, expose] def pBit (B : PBits) (x : Nat) : Bool :=
  (B.get! (x / 8) >>> (x % 8).toUInt8) &&& 1 != 0

@[inline, expose] def pSet (B : PBits) (x : Nat) : PBits :=
  B.set! (x / 8) (B.get! (x / 8) ||| ((1 : UInt8) <<< (x % 8).toUInt8))

@[expose] def pZero (_ : Unit) : PBits := ⟨Array.replicate 3959 0⟩

@[expose] def pOf (z : PBits) (xs : Array Nat) : PBits := xs.foldl pSet z

@[expose] def pImg (z : PBits) (T : Table) (B : PBits) : PBits := Id.run do
  let mut C := z
  for w in [0:3959] do
    let byte := B.get! w
    if byte != 0 then
      for i in [0:8] do
        if (byte >>> i.toUInt8) &&& 1 != 0 then
          C := pSet C (ap T (8 * w + i))
  return C

@[expose] def pKey (z : PBits) (B : PBits) : PBits :=
  Nat.fold 31671 (fun x _ C => if pBit B x then pSet C x else C) z

@[inline, expose] def pMaps (T : Table) (A B : PBits) : Bool :=
  allIn 0 31671 fun x => pBit B (ap T x) == pBit A x

@[inline, expose] def tauAct (O : WOrbit) (D bi : Table) (k m : Nat) : Nat :=
  treeAct O.par O.lab O.alpha O.beta D bi k m

@[noinline, expose] def trLetters (O : WOrbit) (D bi : Table) : Array Table :=
  cGens.map fun g => treeActTab O D bi g

structure TrOrb where
  sets : Array PBits
  pa : Table
  pb : Table
  par : Table
  lab : Table
  tbl : Std.HashMap PBits Nat
deriving Inhabited

@[noinline, expose] def trBFS (z : PBits) (alpha beta : Table) (S0 : PBits) (limit : Nat) :
    TrOrb := Id.run do
  let mut sets : Array PBits := #[S0]
  let mut tbl : Std.HashMap PBits Nat := (∅ : Std.HashMap PBits Nat).insert S0 0
  let mut pa : Table := #[]
  let mut pb : Table := #[]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  for h in [0:limit] do
    if h < sets.size then
      let S := sets[h]!
      let A := pImg z alpha S
      match tbl.get? A with
      | some j => pa := pa.push (UInt32.ofNat j)
      | none =>
        tbl := tbl.insert A sets.size
        pa := pa.push (UInt32.ofNat sets.size)
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
        sets := sets.push A
      let B := pImg z beta S
      match tbl.get? B with
      | some j => pb := pb.push (UInt32.ofNat j)
      | none =>
        tbl := tbl.insert B sets.size
        pb := pb.push (UInt32.ofNat sets.size)
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
        sets := sets.push B
    else break
  return ⟨sets, pa, pb, par, lab, tbl⟩

@[inline, expose] def trFind (o : TrOrb) (z : PBits) (B : PBits) : Nat :=
  (o.tbl.get? (pKey z B)).getD 137632

@[expose] def trBi (o : TrOrb) : Table := compT 137632 o.pb o.pb

@[expose] def trD (o : TrOrb) : Table :=
  powT 137632 7
    (dWord.foldr (fun x T => compT 137632 (if x = 0 then o.pa else o.pb) T) (idT 137632))

@[inline, expose] def trAct (O : WOrbit) (o : TrOrb) (D bi : Table) (k m : Nat) : Nat :=
  treeAct O.par O.lab o.pa o.pb D bi k m

@[noinline, expose] def domWit (O : WOrbit) (D bi : Table) (C : Array Nat) (f : Nat) : Nat :=
  (C.find? fun x => tauAct O D bi x f == f).getD 31671

@[noinline, expose] def ncWit (O : WOrbit) (D bi : Table) (C : Array Nat) (f : Nat) : Nat :=
  (C.find? fun x => tauAct O D bi x f != f).getD 31671

@[noinline, expose] def commTreeP (O : WOrbit) (D bi : Table) (z : PBits) (S : Array Nat) :
    Array Nat × Array Nat := Id.run do
  let mut ord : Array Nat := #[S[0]!]
  let mut par : Array Nat := #[0]
  let mut seen : PBits := pSet z S[0]!
  for h in [0:S.size] do
    if h < ord.size then
      let x := ord[h]!
      for y in S do
        if !pBit seen y && tauAct O D bi x y == y then
          seen := pSet seen y
          ord := ord.push y
          par := par.push h
    else break
  return (ord, par)

structure TrComp where
  treeC : Tree
  treeR : Tree
  cord : Array Nat
  cpar : Array Nat
  domW : Array Nat
  ncW : Array Nat
  orb : TrOrb
  rowInv : Table
  v0 : Nat
  farTree : Tree
  mOrd : Array Nat
  mPar : Array Nat
  mWit : Array Nat
  mH : Array Nat
  muPos : Table
  edX : Array Nat
  edK : Array Nat
deriving Inhabited

@[noinline, expose] def mkRowInv (O : WOrbit) (o : TrOrb) (D bi : Table) (tB : PBits) : Table :=
  Id.run do
  let mut r : Table := Array.replicate 137632 none32
  for f in [0:31671] do
    if !pBit tB f then
      r := r.set! (trAct O o D bi f 0) (UInt32.ofNat f)
  return r

@[inline, expose] def trIsFar (rowInv : Table) (m : Nat) : Bool := m != 0 && rowInv[m]! == none32

@[noinline, expose] def trPhi (O : WOrbit) (o : TrOrb) (D bi : Table) : Array Table :=
  xiGens.map fun g => Array.ofFn (n := 137632) fun m => UInt32.ofNat (trAct O o D bi g m.val)

@[noinline, expose] def nbrWit (O : WOrbit) (o : TrOrb) (D bi : Table) (m : Nat) : Table :=
  Id.run do
  let mut r : Table := Array.replicate 137632 (UInt32.ofNat 31671)
  let S := o.sets[m]!
  for h in [0:31671] do
    if !pBit S h then
      r := r.set! (trAct O o D bi h m) (UInt32.ofNat h)
  return r

@[noinline, expose] def mkMu (O : WOrbit) (o : TrOrb) (D bi : Table) (rowInv : Table) (v0 : Nat) :
    Array Nat × Array Nat := Id.run do
  let mut ms : Array Nat := #[]
  let mut hs : Array Nat := #[]
  let mut seen : Array Bool := Array.replicate 137632 false
  let V := o.sets[v0]!
  for h in [0:31671] do
    if !pBit V h then
      let m := trAct O o D bi h v0
      if rowInv[m]! != none32 && !seen[m]! then
        seen := seen.set! m true
        ms := ms.push m
        hs := hs.push h
  return (ms, hs)

@[noinline, expose] def mkMuTree (O : WOrbit) (o : TrOrb) (D bi : Table) (ms hs : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array (Nat × Table) := Id.run do
  let mut inM : Array Bool := Array.replicate 137632 false
  for m in ms do
    inM := inM.set! m true
  let mut hOf : Array Nat := Array.replicate 137632 31671
  for i in [0:ms.size] do
    hOf := hOf.set! ms[i]! hs[i]!
  let mut ord : Array Nat := #[ms[0]!]
  let mut par : Array Nat := #[0]
  let mut wit : Array Nat := #[0]
  let mut hw : Array Nat := #[hs[0]!]
  let mut seen : Array Bool := (Array.replicate 137632 false).set! ms[0]! true
  let mut nbrs : Array (Nat × Table) := #[]
  for h in [0:ms.size] do
    if ord.size < ms.size && h < ord.size then
      let x := ord[h]!
      let W := nbrWit O o D bi x
      nbrs := nbrs.push (x, W)
      for y in ms do
        if !seen[y]! && ap W y < 31671 then
          seen := seen.set! y true
          ord := ord.push y
          par := par.push h
          wit := wit.push (ap W y)
          hw := hw.push hOf[y]!
    else break
  return (ord, par, wit, hw, nbrs)

@[noinline, expose] def mkEd (O : WOrbit) (o : TrOrb) (D bi : Table) (rowInv : Table) (v0 : Nat)
    (ord : Array Nat) (nbrs0 : Array (Nat × Table)) : Array Nat × Array Nat := Id.run do
  let mut ex : Array Nat := Array.replicate 31671 0
  let mut ek : Array Nat := Array.replicate 31671 31671
  let mut nbrs := nbrs0
  let mut pos : Array Nat := Array.replicate 137632 0
  for i in [0:ord.size] do
    pos := pos.set! ord[i]! i
  let V := o.sets[v0]!
  let mut todo : Array Nat := #[]
  for h in [0:31671] do
    if !pBit V h then
      let w := trAct O o D bi h v0
      if trIsFar rowInv w then
        todo := todo.push h
  let mut next := nbrs.size
  for _ in [0:ord.size] do
    if todo.isEmpty then break
    let mut rest : Array Nat := #[]
    for h in todo do
      let w := trAct O o D bi h v0
      match nbrs.find? (fun p => ap p.2 w < 31671) with
      | some p =>
        ex := ex.set! h pos[p.1]!
        ek := ek.set! h (ap p.2 w)
      | none => rest := rest.push h
    todo := rest
    if !todo.isEmpty && next < ord.size then
      nbrs := nbrs.push (ord[next]!, nbrWit O o D bi ord[next]!)
      next := next + 1
  return (ex, ek)

@[noinline, expose] def trCompute (O : WOrbit) (D bi : Table) (z : PBits) : TrComp :=
  let tB := pOf z trData
  let letters := trLetters O D bi
  let treeC := treeBFS 31671 0 letters (Array.range cGens.size)
  let treeR := treeBFS 31671 rRoot letters (Array.range cGens.size)
  let ct := commTreeP O D bi z cData
  let domW := Array.ofFn (n := 31671) fun f =>
    if pBit tB f.val then 0 else domWit O D bi cData f.val
  let ncW := Array.ofFn (n := 31671) fun f =>
    if pBit tB f.val then 0 else ncWit O D bi cData f.val
  let orb := trBFS z O.alpha O.beta tB 200000
  let bi' := trBi orb
  let dd := trD orb
  let rowInv := mkRowInv O orb dd bi' tB
  let phi := trPhi O orb dd bi'
  let v0 := ((List.range 137632).find? fun m => trIsFar rowInv m).getD 0
  let farTree := treeBFS 137632 v0 phi (Array.range xiGens.size)
  let mu := mkMu O orb dd bi' rowInv v0
  let mt := mkMuTree O orb dd bi' mu.1 mu.2
  let muPos := Id.run do
    let mut p : Table := Array.replicate 137632 none32
    for i in [0:mt.1.size] do
      p := p.set! mt.1[i]! (UInt32.ofNat i)
    return p
  let ed := mkEd O orb dd bi' rowInv v0 mt.1 mt.2.2.2.2
  ⟨treeC, treeR, ct.1, ct.2, domW, ncW, orb, rowInv, v0, farTree, mt.1, mt.2.1, mt.2.2.1,
    mt.2.2.2.1, muPos, ed.1, ed.2⟩

@[noinline, expose] def trIncOK (S : Array Nat) (n : Nat) : Bool :=
  S.size == n && allIn 0 (n - 1) (fun k => S[k]! < S[k + 1]!) && S[n - 1]! < 31671

@[noinline, expose] def trMemOK (B : PBits) (S : Array Nat) : Bool :=
  allIn 0 31671 fun x => pBit B x == S.contains x

@[noinline, expose] def trStarOK (O : WOrbit) (D bi : Table) (ea phiP : Array Nat) (cB : PBits) :
    Bool :=
  failC < 31671 && failC != 0 && ap D failC != failC &&
    allIn 0 3510 fun u => pBit cB ea[phiP[u]!]! == Fi22.Native.lhData[0]!.contains u &&
      Fi22.Native.lhData[1]!.contains u == (tauAct O D bi failC ea[phiP[u]!]! == ea[phiP[u]!]!)

@[noinline, expose] def trGensOK (cB tB : PBits) (letters : Array Table) (treeC treeR : Tree) :
    Bool :=
  letters.size == cGens.size &&
    allIn 0 cGens.size (fun l => cGens[l]! < 31671 && pBit cB cGens[l]! &&
      pMaps letters[l]! cB cB) &&
    treeOK 31671 0 treeC letters (Array.range cGens.size) &&
    treeOK 31671 rRoot treeR letters (Array.range cGens.size) &&
    allIn 0 31671 (fun x => (!pBit cB x || inTreeB treeC x) &&
      (!pBit tB x || pBit cB x || inTreeB treeR x) && (!pBit cB x || pBit tB x))

@[noinline, expose] def trCommOK (O : WOrbit) (D bi : Table) (cB : PBits) (ord par : Array Nat) :
    Bool :=
  ord.size == 1080 && par.size == 1080 && ord[0]! == 0 && pBit cB 0 &&
    allIn 1 1080 (fun k => par[k]! < k && ord[k]! < 31671 && pBit cB ord[k]! &&
      tauAct O D bi ord[par[k]!]! ord[k]! == ord[k]! && ord[par[k]!]! != ord[k]!) &&
    cData.all (fun x => ord.contains x)

@[noinline, expose] def trDomOK (O : WOrbit) (D bi : Table) (cB tB : PBits) (domW ncW : Array Nat) :
    Bool :=
  allIn 0 31671 fun f => pBit tB f ||
    (domW[f]! < 31671 && pBit cB domW[f]! && tauAct O D bi domW[f]! f == f &&
      ncW[f]! < 31671 && pBit tB ncW[f]! && tauAct O D bi ncW[f]! f != f)

@[noinline, expose] def trCsOK (O : WOrbit) (D bi : Table) (cB tB : PBits) : Bool :=
  csV != csW && csV < 31671 && csW < 31671 && pBit tB csV && !pBit cB csV && pBit tB csW &&
    !pBit cB csW &&
    allIn 0 31671 fun y => pBit cB (tauAct O D bi csV y) == pBit cB (tauAct O D bi csW y)

@[noinline, expose] def trOrbitOK (alpha beta : Table) (z tB : PBits) (o : TrOrb) (chunks : Nat) :
    Bool :=
  o.sets.size == 137632 && o.pa.size == 137632 && o.pb.size == 137632 && o.par.size == 137632 &&
    o.lab.size == 137632 && allIn 0 31671 (fun x => pBit o.sets[0]! x == pBit tB x) &&
    parAll 137632 chunks (fun k => ap o.pa k < 137632 && ap o.pb k < 137632 &&
      pMaps alpha o.sets[k]! o.sets[ap o.pa k]! && pMaps beta o.sets[k]! o.sets[ap o.pb k]!) &&
    allIn 1 137632 (fun k => ap o.par k < k &&
      ((ap o.lab k == 1 && ap o.pa (ap o.par k) == k) ||
        (ap o.lab k == 2 && ap o.pb (ap o.par k) == k))) &&
    parAll 137632 chunks (fun k => trFind o z o.sets[k]! == k)

@[noinline, expose] def trRowOK (O : WOrbit) (o : TrOrb) (D bi : Table) (tB : PBits)
    (rowInv : Table) : Bool :=
  rowInv.size == 137632 &&
    allIn 0 31671 (fun f => pBit tB f || (trAct O o D bi f 0 != 0 &&
      ap rowInv (trAct O o D bi f 0) == f)) &&
    allIn 0 137632 (fun m => rowInv[m]! == none32 ||
      (ap rowInv m < 31671 && !pBit tB (ap rowInv m) && trAct O o D bi (ap rowInv m) 0 == m))

@[noinline, expose] def trFarOK (O : WOrbit) (o : TrOrb) (D bi : Table) (tB : PBits)
    (rowInv : Table) (phi : Array Table) (v0 : Nat) (tr : Tree) : Bool :=
  allIn 0 xiGens.size (fun l => xiGens[l]! < 31671 && pBit tB xiGens[l]! &&
      trAct O o D bi xiGens[l]! 0 == 0) &&
    v0 < 137632 && trIsFar rowInv v0 && treeOK 137632 v0 tr phi (Array.range xiGens.size) &&
    allIn 0 137632 fun m => !trIsFar rowInv m || inTreeB tr m

@[noinline, expose] def trMuOK (O : WOrbit) (o : TrOrb) (D bi : Table) (rowInv : Table) (v0 : Nat)
    (mOrd mPar mWit mH : Array Nat) (muPos : Table) : Bool :=
  let V := o.sets[v0]!
  0 < mOrd.size && mPar.size == mOrd.size && mWit.size == mOrd.size && mH.size == mOrd.size &&
    muPos.size == 137632 &&
    allIn 0 mOrd.size (fun k => mOrd[k]! < 137632 && rowInv[mOrd[k]!]! != none32 &&
      mH[k]! < 31671 && !pBit V mH[k]! && trAct O o D bi mH[k]! v0 == mOrd[k]! &&
      ap muPos mOrd[k]! == k) &&
    allIn 1 mOrd.size (fun k => mPar[k]! < k && mWit[k]! < 31671 &&
      !pBit o.sets[mOrd[mPar[k]!]!]! mWit[k]! &&
      trAct O o D bi mWit[k]! mOrd[mPar[k]!]! == mOrd[k]!) &&
    allIn 0 31671 (fun h => pBit V h || rowInv[trAct O o D bi h v0]! == none32 ||
      (ap muPos (trAct O o D bi h v0) < mOrd.size &&
        mOrd[ap muPos (trAct O o D bi h v0)]! == trAct O o D bi h v0))

@[noinline, expose] def trEdOK (O : WOrbit) (o : TrOrb) (D bi : Table) (rowInv : Table) (v0 : Nat)
    (mOrd edX edK : Array Nat) : Bool :=
  let V := o.sets[v0]!
  allIn 0 31671 fun h => pBit V h || !trIsFar rowInv (trAct O o D bi h v0) ||
    (edX[h]! < mOrd.size && edK[h]! < 31671 && !pBit o.sets[mOrd[edX[h]!]!]! edK[h]! &&
      trAct O o D bi edK[h]! mOrd[edX[h]!]! == trAct O o D bi h v0)

@[noinline, expose] def trChecks (O : WOrbit) (D bi : Table) (z : PBits) (C : TrComp)
    (chunks : Nat) : Bool :=
  let ea := starPts D
  let cB := pOf z cData
  let tB := pOf z trData
  let letters := trLetters O D bi
  let tbi := trBi C.orb
  let tdd := trD C.orb
  let phi := trPhi O C.orb tdd tbi
  trIncOK cData 1080 && trIncOK trData 3240 && trMemOK cB cData && trMemOK tB trData &&
    trStarOK O D bi ea starPhiPos cB && trGensOK cB tB letters C.treeC C.treeR &&
    trCommOK O D bi cB C.cord C.cpar && trDomOK O D bi cB tB C.domW C.ncW &&
    trCsOK O D bi cB tB && trOrbitOK O.alpha O.beta z tB C.orb chunks &&
    trRowOK O C.orb tdd tbi tB C.rowInv &&
    trFarOK O C.orb tdd tbi tB C.rowInv phi C.v0 C.farTree &&
    trMuOK O C.orb tdd tbi C.rowInv C.v0 C.mOrd C.mPar C.mWit C.mH C.muPos &&
    trEdOK O C.orb tdd tbi C.rowInv C.v0 C.mOrd C.edX C.edK

@[expose] def trCertificate (chunks : Nat) : Bool :=
  let O := orbitData ()
  let D := dTable O
  let bi := genTables O (-2)
  let z := pZero ()
  trChecks O D bi z (trCompute O D bi z) chunks

end CFSG.Sporadic.Fi23.Native
