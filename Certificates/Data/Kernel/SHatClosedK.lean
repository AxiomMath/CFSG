module

public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.SHatClosed

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (pw2)

@[expose] noncomputable def popK (x : Nat) : Nat :=
  strictN (Nat.sub x (Nat.land (Nat.shiftRight x (nat_lit 1))
    (nat_lit 711995678640303360798340568723184038200901507452217589982347202607406575260213516674320695645525))) fun a =>
  strictN (Nat.add
    (Nat.land a (nat_lit 427197407184182016479004341233910422920540904471330553989408321564443945156128110004592417387315))
    (Nat.land (Nat.shiftRight a (nat_lit 2))
      (nat_lit 427197407184182016479004341233910422920540904471330553989408321564443945156128110004592417387315))) fun b =>
  strictN (Nat.land (Nat.add b (Nat.shiftRight b (nat_lit 4)))
    (nat_lit 125646296230641769552648335657032477329570854256273692349825976930718807398861208824880122760975)) fun c =>
  strictN (Nat.land (Nat.add c (Nat.shiftRight c (nat_lit 8)))
    (nat_lit 8311233602805097596867788739959346749426865845745730622362029602421088427162025486470669598975)) fun d =>
  Nat.land (Nat.shiftRight (Nat.mul d
    (nat_lit 32593072952176853321050151921409202938928885669591100479851096480082699714360884260669292545))
    (nat_lit 304)) (nat_lit 65535)

@[expose] noncomputable def hasB (x k : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land x (pw2 k))

@[expose] noncomputable def f9 (x t : Nat) : Nat := fld(x, Nat.mul (nat_lit 9) t, nat_lit 511)

@[expose] noncomputable def l320 (x t : Nat) : Nat :=
  fld(x, Nat.mul (nat_lit 320) t,
    nat_lit 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936575)

@[expose] noncomputable def l64 (x t : Nat) : Nat :=
  fld(x, Nat.mul (nat_lit 64) t, nat_lit 18446744073709551615)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 64) (nat_lit 7) (nat_lit 127) p q

@[expose] noncomputable def invK (idn t : Nat) : Bool :=
  bAnd(Nat.beq (pc t t) idn, bIf(Nat.beq t idn, false, true))

@[expose] noncomputable def invStep (idn : Nat) (T I : Nat → Nat) (i s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 0,
    nIf(invK idn (T i),
      nIf(Nat.blt (nat_lit 1) s,
        nIf(Nat.beq (I (Nat.sub s (nat_lit 2))) i, Nat.sub s (nat_lit 1), nat_lit 0), nat_lit 0), s))

@[expose] noncomputable def invIdxK (N M : Nat) (T I : Nat → Nat) : Bool :=
  Nat.beq (strictN (pidn (nat_lit 64) (nat_lit 7)) fun idn =>
    foldN N (invStep idn T I) (Nat.succ M)) (nat_lit 1)

@[expose] noncomputable def bindK (M : Nat) (T I V : Nat → Nat) : Bool :=
  allN M fun j => Nat.beq (V j) (T (I j))

@[expose] noncomputable def fixK (a : Nat) : Nat :=
  foldN (nat_lit 64) (fun p s => nIf(Nat.beq (pg (nat_lit 7) (nat_lit 127) a p) p,
    Nat.lor s (pw2 p), s)) (nat_lit 0)

@[expose] noncomputable def rowK (M : Nat) (V CM FX PTR : Nat → Nat) (j : Nat) : Bool :=
  strictB (V j) fun a => strictB (CM j) fun r => strictB (PTR j) fun pt =>
    bAnd(Nat.beq (FX j) (fixK a),
    bAnd(Nat.beq (Nat.shiftRight r M) (nat_lit 0),
      allN M fun k => strictB (V k) fun b => strictB (pc a b) fun P =>
        bIf(Nat.beq P (pc b a),
          bAnd(hasB r k, bIf(Nat.beq k j, true,
            strictB (f9 pt k) fun q => bAnd(Nat.blt q M, Nat.beq (V q) P))),
          bIf(hasB r k, false, true))))

@[expose] noncomputable def ciStep (CM FX : Nat → Nat) (r cx cc fc k s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 0,
    nIf(hasB r k,
      nIf(Nat.blt (nat_lit 1) s,
        strictN (Nat.sub s (nat_lit 2)) fun t =>
          nIf(bAnd(Nat.beq (f9 cx t) k, bAnd(Nat.beq (l320 cc t) (CM k), Nat.beq (l64 fc t) (FX k))),
            Nat.sub s (nat_lit 1), nat_lit 0), nat_lit 0), s))

@[expose] noncomputable def ciK (M : Nat) (CM FX CN CIX CMC FXC : Nat → Nat) (i : Nat) : Bool :=
  strictB (CM i) fun r => strictB (CIX i) fun cx => strictB (CMC i) fun cc =>
    strictB (FXC i) fun fc =>
      Nat.beq (foldN M (ciStep CM FX r cx cc fc) (Nat.succ (CN i))) (nat_lit 1)

@[expose] noncomputable def f1K (M : Nat) (FX : Nat → Nat) : Bool :=
  allN M fun j => Nat.beq (popK (FX j)) (nat_lit 16)

@[expose] noncomputable def leafK (cnt cx cc fc G A F : Nat) : Bool :=
  allN cnt fun t =>
    bIf(Nat.beq (Nat.land G (pw2 (f9 cx t))) (nat_lit 0), true,
      bAnd(Nat.beq (popK (Nat.land A (l320 cc t))) (nat_lit 15),
        Nat.beq (popK (Nat.land F (l64 fc t))) (nat_lit 2)))

@[expose] noncomputable def kLoopK (cnt cx cc fc cmi fxi pti cmj fxj ptj cmp ptp s2 : Nat) : Bool :=
  allN cnt fun t => strictB (f9 cx t) fun k =>
    bIf(bAnd(hasB cmj k, bIf(hasB s2 k, false, true)),
      bAnd(hasB cmp k,
        strictB (l320 cc t) fun cmk => strictB (l64 fc t) fun fxk =>
        strictB (Nat.lor s2 (Nat.lor (pw2 k) (Nat.lor (pw2 (f9 pti k))
          (Nat.lor (pw2 (f9 ptj k)) (pw2 (f9 ptp k)))))) fun s3 =>
        strictB (Nat.land cmj cmk) fun B =>
          leafK cnt cx cc fc (Nat.sub B (Nat.land B s3)) (Nat.land cmi B)
            (Nat.land fxi (Nat.land fxj fxk))),
      true)

@[expose] noncomputable def f23K (CM FX PTR CN CIX CMC FXC : Nat → Nat) (i : Nat) : Bool :=
  strictB (CM i) fun cmi => strictB (FX i) fun fxi => strictB (PTR i) fun pti =>
  strictB (CN i) fun cnt => strictB (CIX i) fun cx => strictB (CMC i) fun cc =>
  strictB (FXC i) fun fc =>
    allN cnt fun t => strictB (f9 cx t) fun j =>
      bIf(Nat.beq j i, true,
        strictB (f9 pti j) fun p => strictB (PTR j) fun ptj => strictB (PTR p) fun ptp =>
        strictB (CM p) fun cmp =>
          kLoopK cnt cx cc fc cmi fxi pti (l320 cc t) (l64 fc t) ptj cmp ptp
            (Nat.lor (pw2 i) (Nat.lor (pw2 j) (pw2 p))))

end CFSG.KC.SHatClosed

end
