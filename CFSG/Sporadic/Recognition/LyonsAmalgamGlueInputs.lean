module

public import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
public import CFSG.Sporadic.Recognition.LyonsModelInputs
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
public meta import CFSG.Sporadic.Recognition.LyonsModelInputs
public meta import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Glue

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def txStrings : List String :=
  ["dcdCDCdCDCDCDCdCDCdCDCdC", "dcdcdcDcDcDCdCDCdCDCdCdCdCDCDCD",
    "cdcdcdcDcDcDcdcDCdCDCdCdCdCDCDCDC", "dcdcdcdcdcdcdcDcdCDCdCDCDCDCDCDCDCD"]

@[expose] def txWords : List (List ℤ) := txStrings.map Ly0.decodeWord

@[expose] def txB : Array Table := (txWords.map (Ly0.wT Ly0.tabs0 Ly0.invs0)).toArray

@[expose] def txInvB : Array Table := txB.map (invT Ly0.deg)

@[expose] def txLetB (l : Int) : Table :=
  if 0 < l then txB[l.toNat - 1]! else txInvB[(-l).toNat - 1]!

@[expose] def uLetB (l : Int) : Table :=
  if 0 < l then Ly0.uTabs[l.toNat - 1]! else Ly0.uInvTabs[(-l).toNat - 1]!

@[expose] def txyB : Array Table := Ly1080.txyWords.toArray.map (wordT Ly0.deg uLetB)

@[expose] def txyBx : Array Table := Ly243.txyWords.toArray.map (wordT Ly0.deg txLetB)

@[expose] def hEnumB : Array Table := Id.run do
  let par := Tau.yEnum.2.1
  let lab := Tau.yEnum.2.2
  let mut out : Array Table := #[idT Ly0.deg]
  for k in [1:par.size] do
    out := out.push (compT Ly0.deg out[par[k]!]! txyB[lab[k]!]!)
  return out

@[expose] def treeBOK : Bool :=
  mulTreeOK Ly0.deg txyB hEnumB Tau.yEnum.2.1 Tau.yEnum.2.2 &&
    hkeysDistinct Ly0.deg hEnumB.toList && hEnumB.size == Tau.yEnum.1.size &&
    (List.range 5).all (fun j => tblEq Ly0.deg txyB[j]! txyBx[j]!) &&
    (List.range hEnumB.size).all fun k => (List.range 5).all fun l =>
      let k' := (Tau.succTab[k]!)[l]!
      k' < hEnumB.size && tblEq Ly0.deg hEnumB[k']! (compT Ly0.deg hEnumB[k]! txyB[l]!)

@[expose] def tKeys : Std.HashMap UInt64 Nat :=
  (Tau.tEnum.toList.zipIdx).foldl (fun m p =>
    m.insert (hkey Ly243.deg p.1) p.2) {}

@[expose] def cosetSearch (n : Nat) (gens H : Array Table) (keys : Std.HashMap UInt64 Nat) :
    Array (List ℤ) × Array (Array (Nat × Nat)) := Id.run do
  let mut reps : Array (List ℤ) := #[[]]
  let mut repT : Array Table := #[idT n]
  let mut succ : Array (Array (Nat × Nat)) := #[]
  let mut i := 0
  while i < reps.size do
    let mut row : Array (Nat × Nat) := #[]
    for k in [0:gens.size] do
      let x := compT n repT[i]! gens[k]!
      let mut found : Option (Nat × Nat) := none
      for j in [0:reps.size] do
        if found.isNone then
          let h := compT n x (invT n repT[j]!)
          match keys.get? (hkey n h) with
          | some ix => if tblEq n H[ix]! h then found := some (j, ix) else pure ()
          | none => pure ()
      match found with
      | some p => row := row.push p
      | none =>
        reps := reps.push (reps[i]! ++ [((k : Int) + 1)])
        repT := repT.push x
        row := row.push (reps.size - 1, 0)
    succ := succ.push row
    i := i + 1
  return (reps, succ)

@[expose] def ySearch : Array (List ℤ) × Array (Array (Nat × Nat)) :=
  cosetSearch Ly1080.deg Ly1080.uTabs Tau.yEnum.1 Tau.yKeys

@[expose] def xSearch : Array (List ℤ) × Array (Array (Nat × Nat)) :=
  cosetSearch Ly243.deg (Ly243.genTabs.extract 0 4) Tau.tEnum tKeys

@[expose] def repTables (n : Nat) (lt : Int → Table) (ws : Array (List ℤ)) : Array Table :=
  ws.map (wordT n lt)

@[expose] def sideOK (n : Nat) (G V E : Array Table) (succ : Array (Array (Nat × Nat))) : Bool :=
  0 < V.size && tblEq n V[0]! (idT n) && succ.size == V.size &&
    (List.range V.size).all (fun i =>
      (succ[i]!).size == G.size &&
      (List.range G.size).all fun k =>
        let p := (succ[i]!)[k]!
        p.1 < V.size && p.2 < E.size &&
          tblEq n (compT n V[i]! G[k]!) (compT n E[p.2]! V[p.1]!)) &&
    (List.range V.size).all fun i => (List.range V.size).all fun j =>
      i == j || !memT n E (compT n V[i]! (invT n V[j]!))

@[expose] def yRepsA : Array Table := repTables Ly1080.deg Ly1080.uLet ySearch.1

@[expose] def yRepsB : Array Table := repTables Ly0.deg uLetB ySearch.1

@[expose] def xRepsA : Array Table := repTables Ly243.deg Ly243.trLet xSearch.1

@[expose] def xRepsB : Array Table := repTables Ly0.deg txLetB xSearch.1

@[expose] def wordsInRange (ws : Array (List ℤ)) (m : Nat) : Bool :=
  ws.all fun w => w.all fun l => l != 0 && l.natAbs ≤ m

@[expose] def yCosetOK : Bool :=
  wordsInRange ySearch.1 4 && ySearch.1.size == 90 &&
    sideOK Ly1080.deg Ly1080.uTabs yRepsA Tau.yEnum.1 ySearch.2 &&
    sideOK Ly0.deg Ly0.uTabs yRepsB hEnumB ySearch.2

@[expose] def xCosetOK : Bool :=
  wordsInRange xSearch.1 4 && xSearch.1.size == 2 &&
    sideOK Ly243.deg (Ly243.genTabs.extract 0 4) xRepsA Tau.tEnum xSearch.2 &&
    sideOK Ly0.deg txB xRepsB hEnumB xSearch.2

@[expose] def lineOK (T X Xi : Table) : Bool := tblEq Ly0.deg T X || tblEq Ly0.deg T Xi

@[expose] def normLinesOK (g gi : Table) : Bool :=
  lineOK (conjT Ly0.deg g gi Ly0.tabX) Ly0.tabX (invT Ly0.deg Ly0.tabX) &&
    lineOK (conjT Ly0.deg g gi Ly0.tabYw) Ly0.tabYw Ly0.tabYinv &&
    lineOK (conjT Ly0.deg g gi Ly0.tabW) Ly0.tabW Ly0.tabWinv

@[expose] def a3Enum : Array Table × Array Nat × Array Nat :=
  mulClosureH Ly0.deg #[Ly0.tabX, Ly0.tabYw, Ly0.tabW] 100

@[expose] def normA3OK (g gi : Table) : Bool :=
  memT Ly0.deg a3Enum.1 (conjT Ly0.deg g gi Ly0.tabX) &&
    memT Ly0.deg a3Enum.1 (conjT Ly0.deg g gi Ly0.tabYw) &&
    memT Ly0.deg a3Enum.1 (conjT Ly0.deg g gi Ly0.tabW)

@[expose] def normOK : Bool :=
  mulTreeOK Ly0.deg #[Ly0.tabX, Ly0.tabYw, Ly0.tabW] a3Enum.1 a3Enum.2.1 a3Enum.2.2 &&
    (List.range 5).all (fun j => normLinesOK txyB[j]! (invT Ly0.deg txyB[j]!)) &&
    (List.range 4).all fun k => normA3OK txB[k]! txInvB[k]!

@[expose] def glueCheck : Bool := treeBOK && yCosetOK && xCosetOK && normOK

end CFSG.Sporadic.Recognition.LyonsSims.Glue
