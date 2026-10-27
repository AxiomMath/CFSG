module

public import Certificates.Data.Kernel.M24G.Img
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.CFSGNative.AS91.M24Trio

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

@[expose] def genFixF (bs : List (Nat × Nat × Nat)) (SL : List (List Nat)) (B : List Nat) : Bool :=
  B.length == 7 && bs.all fun b =>
    imgF b 255 == 255 && imgF b 65280 == 65280 && imgF b 16711680 == 16711680 &&
      B.all fun q => sortN ((SL.getD q []).map (imgF b)) == SL.getD q []

@[expose] def field12 (P i : Nat) : Nat := (P >>> (12 * i)) % 4096

@[expose] def stepP (P i : Nat) : Nat := if i < 3795 then field12 P i else 3795

@[expose] def piSteps (PI : List Nat) : List (Nat → Nat) := PI.map stepP

@[expose] def imgTrioB (b : Nat × Nat × Nat) (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  Native.sort3 (imgF b x.1) (imgF b x.2.1) (imgF b x.2.2)

@[expose] def closeOK (bs : List (Nat × Nat × Nat)) (PI : List Nat) (posT : KTree (Nat × Nat))
    (TL : List (Nat × Nat × Nat)) : Bool :=
  bs.length == PI.length &&
    allIdx (fun i t => allIdx (fun k b =>
      decide (field12 (PI.getD k 0) i < 3795) &&
        idxK posT 3795 (Native.key3 (imgTrioB b t)) == field12 (PI.getD k 0) i) bs 0) TL 0

@[expose] def exp1Go (x : Nat) : List (Nat → Nat) → Nat → List Nat × List Nat × List Nat →
    List Nat × List Nat × List Nat
  | [], _, r => r
  | s :: ss, j, (L, P, G) =>
    if L.contains (s x) then exp1Go x ss (j + 1) (L, P, G)
    else exp1Go x ss (j + 1) (L ++ [s x], P ++ [0], G ++ [j])

@[expose] def exp1 (st : List (Nat → Nat)) (p : Nat) : List Nat × List Nat × List Nat :=
  exp1Go p st 0 ([p], [0], [0])

@[expose] def orbOK (st : List (Nat → Nat)) (p : Nat) : Bool :=
  let r := exp1 st p
  let c := r.1.take 5
  c.length == 5 && decide c.Nodup && c.all (fun q => decide (q < 3795)) &&
    replayOK (fun i => i) st p 1 r.1 r.2.1 r.2.2 (posTree (fun i => i) r.1)

@[expose] def trioOrbF (st : List (Nat → Nat)) (TL : List (Nat × Nat × Nat)) : Bool :=
  allIdx (fun p t => decide (1 < Native.zc Native.baseTrio t) || orbOK st p) TL 0

@[expose] def stepTupF (O : List Nat) (posO : KTree (Nat × Nat)) (SL : List (List Nat))
    (posS : KTree (Nat × Nat)) (b : Nat × Nat × Nat) (c : Nat) : Nat :=
  let a := idxK posO 759 (imgF b (O.getD (c % 759) 0))
  let a' := idxK posO 759 (imgF b (O.getD (c / 759 % 759) 0))
  let u := idxK posS 1771 (Native.keyL (sortN ((SL.getD (c / 759 / 759 % 1771) []).map (imgF b))))
  let v := idxK posS 1771
    (Native.keyL (sortN ((SL.getD (c / 759 / 759 / 1771 % 1771) []).map (imgF b))))
  let w := idxK posS 1771
    (Native.keyL (sortN ((SL.getD (c / 759 / 759 / 1771 / 1771 % 1771) []).map (imgF b))))
  if a < 759 && a' < 759 && u < 1771 && v < 1771 && w < 1771 then Native.encTup a a' u v w
  else Native.nTup

@[expose] def tupStepsF (O : List Nat) (posO : KTree (Nat × Nat)) (SL : List (List Nat))
    (posS : KTree (Nat × Nat)) (bs : List (Nat × Nat × Nat)) : List (Nat → Nat) :=
  bs.map fun b => stepTupF O posO SL posS b

@[expose] def x0F (posO posS : KTree (Nat × Nat)) : Nat :=
  Native.encTup (idxK posO 759 255) (idxK posO 759 65280)
    (idxK posS 1771 (Native.keyL Native.baseSext)) (idxK posS 1771 (Native.keyL Native.sextU2))
    (idxK posS 1771 (Native.keyL Native.sextU3))

@[expose] def tupOK (O : List Nat) (posO : KTree (Nat × Nat)) (SL : List (List Nat))
    (posS : KTree (Nat × Nat)) (bs : List (Nat × Nat × Nat)) (U uPar uGen : List Nat) : Bool :=
  decide (1008 ≤ U.length) && U.all (fun q => decide (q < Native.nTup)) &&
    replayOK (fun i => i) (tupStepsF O posO SL posS bs) (x0F posO posS) 5000 U uPar uGen
      (posTree (fun i => i) U)

end CFSG.KC.M24G
