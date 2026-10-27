module

public import Certificates.Data.Kernel.HSMK
public import Certificates.Data.Kernel.PCent

public section

namespace Certificates.NFMK

open Certificates.WEMK Certificates.TWLK Certificates.HSMK CFSG.KC.PCent

@[expose] def wordN (n : Nat) (S : List NMat) (w : List Nat) : NMat :=
  w.foldl (fun x s => nmul n x (S.getD s [])) (idN n)

@[expose] def scalN (n c : Nat) : NMat :=
  (List.range n).map fun r => (List.range n).map fun j => if r = j then c else 0

@[expose] def unitN (n u : Nat) : NMat :=
  (List.range n).map fun r => (List.range n).map fun j => if n * r + j = u then 1 else 0

@[expose] def maddN (c : Nat) (A B : NMat) : NMat :=
  List.zipWith (fun r t => List.zipWith (fun x y => (c * x + y) % 13) r t) A B

@[expose] def lcombN (Z : NMat) : List Nat → List NMat → NMat
  | c :: cs, M :: Ms => maddN c M (lcombN Z cs Ms)
  | _, _ => Z

@[expose] def kEl (n : Nat) (S E : List NMat) (T : PTree NMat) (Yi : List Nat) (YW : List (List Nat))
    (ET EN : List (List Nat)) (Ep : List (Nat × Nat)) : Bool :=
  decide (E.head? = some (idN n)) && E.all (wfM n) &&
  E.all (fun x => isOneN n (nmul n (nmul n x x) (nmul n x x))) &&
  decide (Yi.length = YW.length) &&
  (List.zip Yi YW).all (fun p => decide (p.1 < E.length) && p.2.all (fun s => decide (s < S.length)) &&
    decide (wordN n S p.2 = getT T p.1)) &&
  decide (ET.length = E.length) &&
  (List.zip E ET).all (fun p => decide (p.2.length = Yi.length) &&
    (List.zip Yi p.2).all fun q => decide (q.2 < E.length) && decide (nmul n p.1 (getT T q.1) = getT T q.2)) &&
  decide (Ep.length = E.length) &&
  (List.zip (List.range E.length) Ep).all (fun p => decide (p.1 = 0) ||
    (decide (p.2.1 < p.1) && decide (p.2.2 < Yi.length) && decide ((ET.getD p.2.1 []).getD p.2.2 0 = p.1))) &&
  decide (EN.length = S.length) &&
  (List.zip S EN).all (fun p => decide (p.2.length = Yi.length) &&
    (List.zip Yi p.2).all fun q => decide (q.2 < E.length) &&
      decide (nmul n (nmul n p.1 (getT T q.1)) p.1 = getT T q.2))

@[expose] def kSpan (n : Nat) (E : List NMat) (T : PTree NMat) (B : List Nat) (CF : List (List Nat)) : Bool :=
  decide (B.length = n * n) && B.all (fun b => decide (b < E.length)) && decide (CF.length = n * n) &&
  (List.zip (List.range (n * n)) CF).all fun p =>
    decide (p.2.length = n * n) && decide (lcombN (scalN n 0) p.2 (B.map (getT T)) = unitN n p.1)

@[expose] def kWords (n : Nat) (S : List NMat) (ZW IW : List Nat) : Bool :=
  ZW.all (fun s => decide (s < S.length)) && IW.all (fun s => decide (s < S.length)) &&
  decide (wordN n S ZW = scalN n 12) && decide (wordN n S IW = scalN n 5)

@[expose] def kCos (n : Nat) (S E C : List NMat) (TC TE : PTree NMat) (CT : List (List (Nat × Nat)))
    (CP : List (Nat × Nat)) : Bool :=
  decide (C.head? = some (idN n)) && C.all (wfM n) && decide (CT.length = C.length) &&
  (List.zip C CT).all (fun p => decide (p.2.length = S.length) &&
    (List.zip S p.2).all fun q => decide (q.2.1 < C.length) && decide (q.2.2 < E.length) &&
      decide (nmul n p.1 q.1 = nmul n (getT TC q.2.1) (getT TE q.2.2))) &&
  decide (CP.length = C.length) &&
  (List.zip (List.range C.length) CP).all fun p => decide (p.1 = 0) ||
    (decide (p.2.1 < p.1) && decide (p.2.2 < S.length) && decide ((CT.getD p.2.1 []).getD p.2.2 (0, 0) = (p.1, 0)))

@[expose] def kOrbRow (n : Nat) (S : List NMat) (nC nE : Nat) (TC TE : PTree NMat) (TO : PTree (List Nat))
    (EK roots : List Nat) (i : Nat) (x : NMat) (r : List Nat) : Bool :=
  (!EK.contains (kVKey 13 (nmul n x x)) || decide (r.getD 0 0 = 1)) &&
  (!decide (r.getD 0 0 = 1) ||
    (decide (r.getD 1 0 = 0) && roots.contains i) ||
    (decide (0 < r.getD 1 0) && decide (r.getD 2 0 < nC) && decide (r.getD 3 0 < S.length) &&
      decide (r.getD 4 0 < nE) && decide ((getT TO (r.getD 2 0)).getD 1 0 < r.getD 1 0) &&
      decide (nmul n (nmul n (S.getD (r.getD 3 0) []) x) (S.getD (r.getD 3 0) []) =
        nmul n (getT TC (r.getD 2 0)) (getT TE (r.getD 4 0)))))

@[expose] def kOrbT (n : Nat) (S E C : List NMat) (TC TE : PTree NMat) (OT : List (List Nat))
    (roots : List Nat) : Bool :=
  decide (OT.length = C.length) &&
  (List.zip (List.range C.length) (List.zip C OT)).all fun p =>
    kOrbRow n S C.length E.length TC TE (treeOf OT) (E.map (kVKey 13)) roots p.1 p.2.1 p.2.2

@[expose] def kWit1 (n : Nat) (TV : PTree KPair) (nV : Nat) (z x : NMat) (w : Nat × Nat × Nat) : Bool :=
  match w.1 with
  | 0 => !isOneN n (nmul n x x)
  | 1 => isOneN n x
  | 2 => decide (w.2.1 < nV) && decide (x = mat n (getT TV w.2.1))
  | 3 => decide (w.2.1 < nV) && decide (nmul n z x = mat n (getT TV w.2.1))
  | 4 => decide (w.2.1 < nV) && decide (w.2.2 < nV) && decide (nmul n (mat n (getT TV w.2.1)) x = mat n (getT TV w.2.2))
  | 5 => decide (w.2.1 < nV) && decide (w.2.2 < nV) &&
      decide (nmul n (mat n (getT TV w.2.1)) (nmul n z x) = mat n (getT TV w.2.2))
  | _ => false

@[expose] def kScan (n : Nat) (E : List NMat) (TC : PTree NMat) (nC : Nat) (V : List KPair)
    (W : List (Nat × List (Nat × Nat × Nat))) : Bool :=
  W.all fun p => decide (p.1 < nC) && decide (p.2.length = E.length) &&
    (List.zip E p.2).all fun q => kWit1 n (treeOf V) V.length (scalN n 12) (nmul n (getT TC p.1) q.1) q.2

@[expose] def kPairO (n : Nat) (V : List KPair) : Bool :=
  V.all fun q =>
    let P := nmul n (mat n (V.getD 0 kP0)) (mat n q)
    let P2 := nmul n P P
    isOneN n P || isOneN n P2 || isOneN n (nmul n P2 P) || isOneN n (nmul n P2 P2)

end Certificates.NFMK

end
