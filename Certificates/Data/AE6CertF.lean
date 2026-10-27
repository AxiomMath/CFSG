module

public import Certificates.Data.AE6CertC2
public import Certificates.Data.AE6CertF5

public section

namespace Certificates.AE6Model

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native Certificates.S7Twin

@[expose] def fKWordsN : List (List ℕ) :=
  [[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6, 0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]]

@[expose] def fTwinWordsN : List (List ℕ) := [[], [0], [4], [6]]

@[expose] def fCycWordN (m : ℕ) : List ℕ :=
  let t := fTwinWordsN.getD (m / 3) []
  t ++ fKWordsN.getD (m % 3) [] ++ t.reverse

@[expose] def fCLettersN : List ℕ := [0, 1, 2, 4, 5, 6, 7]

@[expose] def fDiagN : List (List ℕ) := [[4, 5, 2, 3, 0, 1, 6, 7], [6, 7, 2, 3, 4, 5, 0, 1]]

@[expose] def fCycs (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  (List.range 12).map fun m => aeWord G (fCycWordN m)

@[expose] def fBasic (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let Z := toTable (z0 ())
  let K0 := toTable (aeWord G (fKWordsN.getD 0 []))
  let K1 := toTable (aeWord G (fKWordsN.getD 1 []))
  (fKWordsN.all fun w => let k := toTable (aeWord G w); tblEq 360 (compT 360 k k) Z) &&
    !tblEq 360 Z (idT 360) && tblEq 360 (compT 360 Z Z) (idT 360) &&
    tblEq 360 (compT 360 (compT 360 K1 K0) (compT 360 K0 K1)) (idT 360) &&
    G.all fun g => sqOneT 360 (toTable g)

@[expose] def fTwinPairs (_ : Unit := ()) :
    List (Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  let x := aeWord G (fKWordsN.getD 0 [])
  let y := aeWord G (fKWordsN.getD 1 [])
  fTwinWordsN.map fun w => let c := aeWord G w; (c * x * c⁻¹, c * y * c⁻¹)

@[expose] def fTwinChecks (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let TP := fTwinPairs ()
  let TS := TP.map fun p => spanQ (toTable p.1) (toTable p.2)
  fCLettersN.all fun l =>
    let g := G.getD l 1
    let Gt := toTable g
    let Gi := toTable g⁻¹
    TP.all fun p => TS.any fun sp =>
      memT 360 sp (conjT 360 Gt Gi (toTable p.1)) && memT 360 sp (conjT 360 Gt Gi (toTable p.2))

@[expose] def fCycTabs (_ : Unit := ()) : List (Table × Table) :=
  (fCycs ()).map fun g => (toTable g, toTable g⁻¹)

@[expose] def fCycChecks (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let CT := fCycTabs ()
  (List.range 12).all (fun m => (List.range 12).all fun n =>
    let gm := CT.getD m (idT 360, idT 360)
    let gn := CT.getD n (idT 360, idT 360)
    (m == n || (!tblEq 360 gm.1 gn.1 && !tblEq 360 gm.1 gn.2)) &&
      (m / 3 == n / 3 || commT 360 gm.1 gn.1) &&
      (m / 3 != n / 3 || m == n || tblEq 360 (compT 360 (compT 360 gm.1 gn.1) gm.2) gn.2)) &&
    (List.range 7).all fun x =>
      let a := toTable (G.getD (fCLettersN.getD x 0) 1)
      (List.range 12).all fun m =>
        let t := CT.getD ((fLetterHat.getD x []).getD m 0) (idT 360, idT 360)
        let v := compT 360 (compT 360 a (CT.getD m (idT 360, idT 360)).1) a
        tblEq 360 v t.1 || tblEq 360 v t.2

@[expose] def diagWordTable (G : List (Equiv.Perm (Fin 360))) (d w : List ℕ) : Table :=
  toTable (aeWord G (w.map fun i => d.getD i 0))

@[expose] def fDiagChecks (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let WT := allTables (wQ ())
  let Z := toTable (z0 ())
  let CT := fCycTabs ()
  (List.range 2).all fun c =>
    let d := fDiagN.getD c []
    let gh := fGammaHat.getD c []
    let HT := (List.range 8).map fun i =>
      let g := G.getD (d.getD i 0) 1
      (toTable g, toTable g⁻¹)
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6.curtisRels.all
        (fun r => tblEq 360 (tableEval HT r) (idT 360)) &&
      tblEq 360 (diagWordTable G d zWord) Z &&
      ((List.range 12).all fun m =>
        let t := CT.getD (gh.getD m 0) (idT 360, idT 360)
        let v := diagWordTable G d (fCycWordN m)
        tblEq 360 v t.1 || tblEq 360 v t.2) &&
      wWords.all fun w => memT 360 WT (diagWordTable G d w)

end Certificates.AE6Model
