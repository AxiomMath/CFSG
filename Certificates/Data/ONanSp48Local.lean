module

public import Certificates.Data.ONanSp48Code

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

@[expose] def t1c : Pc := ⟨#[2, 0, 4, 0, 0, 1, 0, 0, 4, 0, 6, 0, 0, 0, 0, 1], 0⟩

@[expose] def t2c : Pc := ⟨#[1, 0, 0, 0, 0, 2, 0, 4, 0, 0, 1, 0, 0, 4, 0, 6], 0⟩

@[expose] def wc : Pc := ⟨#[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], 0⟩

@[expose] def sc : Pc := ⟨#[0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0], 0⟩

@[expose] def fc : Pc := ⟨idCode, 1⟩

@[expose] def nf (i j k : ℕ) : Pc := mulP (mulP (powP t1c i) (powP t2c j)) (powP fc k)

@[expose] def lstT : List Pc :=
  (List.range 9).flatMap fun i => (List.range 9).flatMap fun j => (List.range 3).map fun k =>
    nf i j k

@[expose] def lstA : List Pc :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b => (List.range 3).map fun c =>
    nf (3 * a) (3 * b) c

@[expose] def lstE : List Pc :=
  (List.range 3).flatMap fun a => (List.range 3).map fun b => nf (3 * a) (3 * b) 0

@[expose] def gensValid : Bool := validB t1c.m && validB t2c.m && validB wc.m && validB sc.m

@[expose] def relOK : Bool :=
  powP t1c 9 == oneP && powP t2c 9 == oneP && powP fc 3 == oneP && !(powP t1c 3 == oneP) &&
  mulP t1c t2c == mulP t2c t1c &&
  mulP fc t1c == mulP (powP t1c 7) fc && mulP fc t2c == mulP (powP t2c 7) fc &&
  mulP wc wc == oneP && mulP sc sc == oneP &&
  mulP (mulP wc t1c) wc == powP t1c 8 && mulP wc t2c == mulP t2c wc && mulP wc fc == mulP fc wc &&
  mulP (mulP sc t1c) sc == t2c && mulP (mulP sc t2c) sc == t1c && mulP sc fc == mulP fc sc

@[expose] def normalFormOK : Bool :=
  decide lstT.Nodup && decide lstE.Nodup && decide lstA.Nodup && lstT.contains oneP &&
  lstA.contains oneP &&
  lstT.all (fun p => lstT.all fun q => lstT.contains (mulP p q)) &&
  lstT.all (fun p => powP p 9 == oneP && lstT.contains (powP p 8)) &&
  lstA.all (fun p => lstA.all fun q => lstA.contains (mulP p q)) &&
  lstA.all (fun p => lstT.contains p && lstA.contains (powP p 2)) &&
  lstE.all (fun p => lstA.contains p)

@[expose] def centreOK : Bool :=
  lstE.all (fun p => lstT.all fun q => mulP p q == mulP q p) &&
  lstT.all (fun p => !([t1c, t2c, fc].all fun g => mulP p g == mulP g p) || lstE.contains p)

@[expose] def ordThreeOK : Bool :=
  lstA.all (fun p => powP p 3 == oneP) &&
  lstA.all (fun p => lstA.all fun q => mulP p q == mulP q p) &&
  lstT.all (fun p => !(p.j == 0 && powP p 3 == oneP) || lstE.contains p)

@[expose] def normalOK : Bool :=
  [(t1c, powP t1c 8), (t2c, powP t2c 8), (wc, wc), (sc, sc), (fc, powP fc 2)].all fun bb =>
    mulP bb.1 bb.2 == oneP && lstT.all (fun p => lstT.contains (mulP (mulP bb.1 p) bb.2)) &&
    lstE.all fun p => lstE.contains (mulP (mulP bb.1 p) bb.2)

@[expose] def uList : List (Pc × Pc) :=
  [(oneP, oneP), (t1c, powP t1c 8), (powP t1c 2, powP t1c 7), (t2c, powP t2c 8)]

@[expose] def cj (k : ℕ) (p : Pc) : Pc := mulP (mulP (uList[k]!).1 p) (uList[k]!).2

@[expose] def orbitOK : Bool :=
  lstA.all fun p => lstE.contains p ||
    (List.range 4).all fun k => (List.range 4).all fun l =>
      k == l || (!(cj k p == oneP) && !(cj k p == cj l p) &&
        !(cj k p == mulP (cj l p) (cj l p)))

@[expose] def homOK : Bool :=
  (List.range 9).all fun a => (List.range 9).all fun b =>
    !(powP t1c a == powP t2c b) || a == 0

@[expose] def sp48LocalCheck : Bool :=
  gensValid && relOK && normalFormOK && centreOK && ordThreeOK && normalOK && orbitOK && homOK

end CFSG.AGLEmbedding.KFactProofs.Sp48
