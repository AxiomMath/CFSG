module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import Std.Data.HashMap

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev Word := List Int

@[expose] def commP (n : Nat) (x y : Table) : Bool := tblEq n (compT n x y) (compT n y x)

@[expose] def permP (n : Nat) (x : Table) : Bool :=
  CFSG.Monster.B.Co2.Native.isInvA n (natArr x) (CFSG.Monster.B.Co2.Native.invCand n (natArr x))

@[expose] def involP (n : Nat) (x : Table) : Bool := invoOK n x && !tblEq n x (idT n)

@[expose] def gensP (n : Nat) (gs : Array Table) : Bool :=
  gs.all fun x => permP n x && invOK n x (invT n x)

@[expose] def letterT (n : Nat) (gs gsInv : Array Table) (l : Int) : Table :=
  if 0 < l ∧ (l - 1).toNat < gs.size then gs[(l - 1).toNat]!
  else if l < 0 ∧ (-l - 1).toNat < gsInv.size then gsInv[(-l - 1).toNat]!
  else idT n

@[expose] def wordTab (n : Nat) (gs gsInv : Array Table) (w : Word) : Table :=
  wordT n (letterT n gs gsInv) w

@[expose] def commutT (n : Nat) (a b : Table) : Table :=
  compT n (compT n a b) (compT n (invT n a) (invT n b))

@[expose] def hindex (n : Nat) (L : Array Table) : Std.HashMap UInt64 Nat := Id.run do
  let mut m : Std.HashMap UInt64 Nat := {}
  for i in [0:L.size] do
    m := m.insert (hkey n L[i]!) i
  return m

@[expose] def closedHOK (n : Nat) (gens L : Array Table) : Bool :=
  let ix := hindex n L
  L.all fun x => gens.all fun g =>
    let z := compT n x g
    match ix[hkey n z]? with
    | some i => decide (i < L.size) && tblEq n L[i]! z
    | none => false

@[expose] def enumP (n cap : Nat) (gs : Array Table) (N : Nat) : Bool :=
  let e := mulClosureH n gs cap
  gensP n gs && mulTreeOK n gs e.1 e.2.1 e.2.2 && closedHOK n (gs ++ gs.map (invT n)) e.1 &&
    hkeysDistinct n e.1.toList && e.1.size == N

@[expose] def orbitP (n cap : Nat) (gs gsInv : Array Table) (x : Table) : Bool :=
  let q := conjClosureH n gs gsInv x cap
  conjTreeOK n gs gsInv x q.1 q.2.1 q.2.2

structure JWords where
  a₁ : Word
  b₁ : Word
  a₂ : Word
  b₂ : Word

@[expose] def jEls (n : Nat) (gs gi : Array Table) (jw : JWords) : Array Table :=
  #[wordTab n gs gi jw.a₁, wordTab n gs gi jw.b₁, wordTab n gs gi jw.a₂, wordTab n gs gi jw.b₂]

@[expose] def jGens (n : Nat) (gs gi : Array Table) (jw : JWords) : Array Table :=
  let e := jEls n gs gi jw
  #[commutT n e[0]! e[1]!, commutT n e[2]! e[3]!]

@[expose] def wordsLE (m : Nat) (w : Word) : Bool := w.all fun l => l != 0 && decide (l.natAbs ≤ m)

structure G5Row where
  z : Word
  k : Word
  wa : Word
  wb : Word

structure DData where
  gens : Array Table
  x : Word
  jw : JWords
  rB : Word
  g5 : List G5Row

@[expose] def g5RowOK (n : Nat) (gs gi : Array Table) (x j₁ j₂ : Table) (r : G5Row) : Bool :=
  let js := #[j₁, j₂]
  let ji := js.map (invT n)
  let z := wordTab n js ji r.z
  let k := wordTab n gs gi r.k
  let ki := invT n k
  let gl := #[j₁, j₂, conjT n k ki j₁, conjT n k ki j₂]
  let gli := gl.map (invT n)
  gensP n js && gensP n gl && invOK n k ki && tblEq n (conjT n k ki x) (compT n x z) &&
    tblEq n (wordTab n gl gli r.wa) gs[0]! && tblEq n (wordTab n gl gli r.wb) gs[1]!

@[expose] def commClosedOK (n : Nat) (E JL : Array Table) : Bool :=
  E.all fun a => invOK n a (invT n a) && E.all fun b => memT n JL (commutT n a b)

@[expose] def centerTrivialOK (n : Nat) (j₁ j₂ : Table) (JL : Array Table) : Bool :=
  JL.all fun s => tblEq n s (idT n) || !(commP n j₁ s && commP n j₂ s)

@[expose] def g5CoverOK (n : Nat) (js ji JL : Array Table) (rows : List G5Row) : Bool :=
  JL.all fun s => !involP n s || rows.any fun r => tblEq n s (wordTab n js ji r.z)

@[expose] def i3OK (n : Nat) (DL OA OB : Array Table) : Bool :=
  DL.all fun y => !involP n y || memT n OA y || memT n OB y

@[expose] def checkD (n cap : Nat) (d : DData) : Bool :=
  let gs := d.gens
  let gi := gs.map (invT n)
  let DL := mulClosureH n gs cap
  let x := wordTab n gs gi d.x
  let rB := wordTab n gs gi d.rB
  let je := jEls n gs gi d.jw
  let js := jGens n gs gi d.jw
  let ji := js.map (invT n)
  let JL := mulClosureH n js cap
  let E := DL.1.filter (commP n x)
  let OA := conjClosureH n gs gi x cap
  let OB := conjClosureH n gs gi rB cap
  gs.size == 2 && enumP n cap gs 95040 &&
    wordsLE 2 d.x && wordsLE 2 d.rB && wordsLE 2 d.jw.a₁ && wordsLE 2 d.jw.b₁ &&
    wordsLE 2 d.jw.a₂ && wordsLE 2 d.jw.b₂ &&
    involP n x && involP n rB &&
    conjTreeOK n gs gi x OA.1 OA.2.1 OA.2.2 && conjTreeOK n gs gi rB OB.1 OB.2.1 OB.2.2 &&
    (DL.1.filter (commP n rB)).size != 240 &&
    gensP n je && je.all (commP n x) && enumP n cap js 60 &&
    commClosedOK n E JL.1 && centerTrivialOK n js[0]! js[1]! JL.1 &&
    d.g5.all (g5RowOK n gs gi x js[0]! js[1]!) && g5CoverOK n js ji JL.1 d.g5 &&
    i3OK n DL.1 OA.1 OB.1

structure RData where
  gens : List Word
  order : Nat
  perf : List (List (Word × Word))

structure RepData where
  rep : Word
  rdata : Option RData

structure KData where
  gens : Array Table
  x : Word
  jw : JWords
  reps : List RepData

@[expose] def commProd (n : Nat) (rg rgi : Array Table) (ps : List (Word × Word)) : Table :=
  ps.foldr (fun p acc =>
    compT n (commutT n (wordTab n rg rgi p.1) (wordTab n rg rgi p.2)) acc) (idT n)

@[expose] def commPairOK (n : Nat) (rg rgi : Array Table) (p : Word × Word) : Bool :=
  invOK n (wordTab n rg rgi p.1) (invT n (wordTab n rg rgi p.1)) &&
    invOK n (wordTab n rg rgi p.2) (invT n (wordTab n rg rgi p.2))

@[expose] def rdataOK (n cap : Nat) (gs gi : Array Table) (r : Table) (rd : RData) : Bool :=
  let rg := (rd.gens.map (wordTab n gs gi)).toArray
  let rgi := rg.map (invT n)
  gensP n rg && rg.all (commP n r) && enumP n cap rg rd.order && decide (60 ≤ rd.order) &&
    rd.gens.length == rd.perf.length && rd.perf.all (·.all (commPairOK n rg rgi)) &&
    (List.range rg.size).all fun k => tblEq n rg[k]! (commProd n rg rgi rd.perf[k]!)

@[expose] def repOK (n cap : Nat) (gs gi KL : Array Table) (x j₁ j₂ : Table) (rd : RepData) :
    Bool :=
  let r := wordTab n gs gi rd.rep
  let o := conjClosureH n gs gi r cap
  let c := (KL.filter (commP n r)).size
  involP n r && conjTreeOK n gs gi r o.1 o.2.1 o.2.2 &&
    o.1.any (fun y => commP n x y && !(commP n j₁ y && commP n j₂ y)) &&
    (960 % c != 0 ||
      match rd.rdata with
      | none => false
      | some rr => rdataOK n cap gs gi r rr)

@[expose] def jNormalOK (n : Nat) (HL JL : Array Table) : Bool :=
  HL.all fun h =>
    let hi := invT n h
    invOK n h hi && JL.all fun j => memT n JL (conjT n h hi j)

@[expose] def g3OK (n : Nat) (HL YL : Array Table) (x : Table) : Bool :=
  HL.any fun c => invOK n c (invT n c) &&
    YL.any fun y => invOK n y (invT n y) && tblEq n (commutT n c y) x

@[expose] def kCoverOK (n : Nat) (KL : Array Table) (t : Table)
    (orbs : List (Array Table × Array Nat × Array Nat)) : Bool :=
  KL.all fun w => !involP n w || tblEq n w t || orbs.any fun o => memT n o.1 w

@[expose] def checkK (n cap : Nat) (d : KData) : Bool :=
  let gs := d.gens
  let gi := gs.map (invT n)
  let KL := mulClosureH n gs cap
  let x := wordTab n gs gi d.x
  let je := jEls n gs gi d.jw
  let js := jGens n gs gi d.jw
  let JL := mulClosureH n js cap
  let HL := KL.1.filter (commP n x)
  let YL := HL.filter (fun y => commP n js[0]! y && commP n js[1]! y)
  let t := gs[3]!
  let orbs := d.reps.map fun rd => conjClosureH n gs gi (wordTab n gs gi rd.rep) cap
  gs.size == 4 && enumP n cap gs 380160 &&
    wordsLE 2 d.x && wordsLE 2 d.jw.a₁ && wordsLE 2 d.jw.b₁ && wordsLE 2 d.jw.a₂ &&
    wordsLE 2 d.jw.b₂ && involP n x && involP n t && gs.all (commP n t) &&
    HL.size == 960 && gensP n je && je.all (commP n x) && enumP n cap js 60 &&
    jNormalOK n HL JL.1 && YL.size == 8 && g3OK n HL YL x &&
    d.reps.all (repOK n cap gs gi KL.1 x js[0]! js[1]!) && kCoverOK n KL.1 t orbs

end CFSG.EvenSporadicStandard.M12Std.PropA.Native
