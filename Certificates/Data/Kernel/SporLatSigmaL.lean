module

public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.KC.SLSig

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def ctabL (s t : List Nat) : List Nat := t.map fun j => s.getD j 0

@[expose] def isOrd3L (n : Nat) (t : List Nat) : Bool :=
  !(t == List.range n) && ctabL t (ctabL t t) == List.range n

@[expose] def closeL (gens : List (List Nat)) :
    Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | f + 1, t :: rest, seen =>
    let r := gens.foldl (fun (p : List (List Nat) × List (List Nat)) g =>
      let u := ctabL g t
      bif p.1.contains u then p else (u :: p.1, u :: p.2)) (seen, rest)
    closeL gens f r.2 r.1

@[expose] def sylowListL (n : Nat) (gens : List (List Nat)) : List (List Nat) :=
  closeL gens 100000 [List.range n] [List.range n]

@[expose] def sylowClosedL (n : Nat) (gens : List (List Nat)) (L : List (List Nat)) : Bool :=
  L.contains (List.range n) && L.all fun t => gens.all fun g => L.contains (ctabL g t)

@[expose] def wordTabT (tabs : Array (Array Nat)) (n : Nat) (w : List Nat) : List Nat :=
  (List.range n).map (wordImg tabs w)

section Lat

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def memberTabsL (n : Nat) (D : LatData Lab) (LS : List (List Nat)) (j : Nat) :
    List (List Nat) :=
  (List.range D.Om[j]!.lbl.size).flatMap fun i =>
    LS.map (ctabL (wordTabT (D.sTabs ++ D.mt[j]!).toArray n (D.Om[j]!.pathWord i i)))

@[expose] def ord3TabsL (n : Nat) (D : LatData Lab) (LS : List (List Nat)) (j : Nat) :
    List (List Nat) :=
  (memberTabsL n D LS j).filter (isOrd3L n)

@[expose] def sigPairOK (LS : List (List Nat)) (inJ : List Nat → Bool) (te tx : List Nat) : Bool :=
  !(ctabL te tx == ctabL tx te) || inJ tx ||
    LS.all fun ts => !(ctabL ts te == ctabL (ctabL te te) ts) || !(ctabL ts tx == ctabL tx ts)

@[expose] def sigmaCheckL (act : List Nat → Lab → Lab) (n : Nat) (Δ : Lab) (D : LatData Lab)
    (lbl : Nat → List Lab) (js ks : List Nat) : Bool :=
  let LS := sylowListL n (D.sTabs.map Array.toList)
  sylowClosedL n (D.sTabs.map Array.toList) LS &&
  js.all fun j =>
    let E := ord3TabsL n D LS j
    ks.all fun k =>
      let X := ord3TabsL n D LS k
      E.all fun te => X.all fun tx => sigPairOK LS (fun t => (lbl j).contains (act t Δ)) te tx

@[expose] def gensInL (act : Array Nat → Lab → Lab) (Δ : Lab) (mt : List (Array Nat))
    (lbl : List Lab) : Bool :=
  mt.all fun t => lbl.contains (act t Δ)

end Lat

end CFSG.KC.SLSig

end
