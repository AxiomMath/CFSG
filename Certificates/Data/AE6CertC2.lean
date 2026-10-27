module

public import Certificates.Data.AE6ModelSmall
public import Certificates.Data.TwinPerpV3A6iCurtis
public import Mathlib.Data.List.Defs

public section

namespace Certificates.AE6Model

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native Certificates.S7Twin

@[expose] def pWordsC2 : List (List ℕ) :=
  [[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2], [0, 6, 2, 0, 4, 2, 6, 0, 2, 0, 2, 4, 2],
    [6, 2, 0, 4, 2, 6, 0, 2, 0, 2, 4, 2, 0], [2, 4, 0, 2, 0, 6, 2, 4, 2, 0, 2, 0, 6],
    [2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 0, 6], [0, 2, 0, 2, 4, 2, 0, 6, 2, 4, 0, 2, 6]]

@[expose] def c2Qs (_ : Unit := ()) : List (List Table) :=
  let PL := allTables (plQ ())
  let G := curtisPerms ()
  (List.range 8).map fun i =>
    let g := G.getD i 1
    let Gt := toTable g
    let Gi := toTable g⁻¹
    PL.filter fun T => memT 360 PL (conjT 360 Gt Gi T)

@[expose] def c2L3 (_ : Unit := ()) : List Table :=
  let Q3 := (c2Qs ()).getD 3 []
  filterProducts 360 (fun T => Q3.all fun q => commT 360 T q) (levelTables (czQ ())) (idT 360) []

@[expose] def c2Ls (_ : Unit := ()) : List (List Table) :=
  let L3 := c2L3 ()
  (c2Qs ()).map fun Q => L3.filter fun T => Q.all fun q => commT 360 T q

@[expose] def tableEval (HT : List (Table × Table)) (w : List ℕ) : Table :=
  w.foldl (fun acc k => compT 360 acc
    (if k % 2 = 0 then (HT.getD (k / 2) (idT 360, idT 360)).1
      else (HT.getD (k / 2) (idT 360, idT 360)).2)) (idT 360)

@[expose] def wordTable (HT : List (Table × Table)) (w : List ℕ) : Table :=
  w.foldl (fun acc i => compT 360 acc (HT.getD i (idT 360, idT 360)).1) (idT 360)

@[expose] def c2Basic (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let PL := allTables (plQ ())
  let Qs := c2Qs ()
  let Q3 := Qs.getD 3 []
  let Z := toTable (z0 ())
  pWordsC2.all (fun w => memT 360 PL (toTable (aeWord G w))) &&
    Qs.length == 8 && Qs.all (fun Q => memT 360 Q Z && Q3.all (memT 360 Q)) &&
    (c2Ls ()).all fun L => L.all fun T => invOK 360 T (invT 360 T)

@[expose] def c2HT (GT : List (Table × Table)) (cs : List Table) : List (Table × Table) :=
  (List.range 8).map fun i =>
    let gp := GT.getD i (idT 360, idT 360)
    let T := cs.getD i (idT 360)
    (compT 360 gp.1 T, compT 360 (invT 360 T) gp.2)

@[expose] def c2Search (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let GT := G.map fun g => (toTable g, toTable g⁻¹)
  let Z := z0 ()
  let ZC := (List.range 8).map fun i => let g := G.getD i 1; toTable (g⁻¹ * Z * g * Z⁻¹)
  let targets := pWordsC2.map fun w => (w, toTable (aeWord G w))
  (List.sections (c2Ls ())).all fun cs =>
    let HT := c2HT GT cs
    !(targets.all (fun wt => tblEq 360 (wordTable HT wt.1) wt.2) &&
        CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6.curtisRels.all fun r =>
          tblEq 360 (tableEval HT r) (idT 360)) ||
      (List.range 8).all (fun i => tblEq 360 (cs.getD i (idT 360)) (idT 360)) ||
      (List.range 8).all fun i => tblEq 360 (cs.getD i (idT 360)) (ZC.getD i (idT 360))

end Certificates.AE6Model
