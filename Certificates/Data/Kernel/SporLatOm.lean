module

public import Certificates.Data.Kernel.E64F
public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.KC.SLOm

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

section Twin

variable {Lab : Type} [DecidableEq Lab] [Inhabited Lab]

@[expose] def idxL (x : Lab) : List Lab → Option Nat
  | [] => none
  | y :: l => if x = y then some 0 else (idxL x l).map (· + 1)

abbrev St4 (Lab : Type) := Array Lab × Array Nat × Array Nat × Array (Array Nat)

@[expose] def omStep (actF : Nat → Lab → Lab) (L : Lab) (i : Nat) (s : St4 Lab) (l : Nat) :
    St4 Lab :=
  match idxL (actF l L) s.1.toList with
  | some j => (s.1, s.2.1, s.2.2.1, s.2.2.2.modify l fun a => a.push j)
  | none => (s.1.push (actF l L), s.2.1.push i, s.2.2.1.push l,
      s.2.2.2.modify l fun a => a.push s.1.size)

@[expose] def omRun (actF : Nat → Lab → Lab) (m cap : Nat) :
    Nat → St4 Lab → Nat → Option (OmegaData Lab × Bool)
  | 0, _, _ => none
  | f + 1, s, i =>
    if (decide (i < s.1.size) && decide (s.1.size ≤ cap)) = true then
      omRun actF m cap f ((List.range' 0 m).foldl (omStep actF s.1[i]! i) s) (i + 1)
    else some (⟨s.1, s.2.2.2, s.2.1, s.2.2.1⟩, i == s.1.size)

@[expose] def omTwin (actF : Nat → Lab → Lab) (m : Nat) (Δ : Lab) (cap fuel : Nat) :
    Option (OmegaData Lab × Bool) :=
  omRun actF m cap fuel (#[Δ], #[0], #[0], Array.replicate m #[]) 0

end Twin

@[expose] def omOK (Δ : List Nat) (L : Nat → Nat → Nat) (nl : Nat) (O : OmegaData (List Nat)) :
    Bool :=
  O.lbl[0]! == Δ && decide (0 < O.lbl.size) &&
    (List.range nl).all (fun l => (List.range O.lbl.size).all fun i =>
      decide ((O.pn[l]!)[i]! < O.lbl.size) &&
        O.lbl[(O.pn[l]!)[i]!]! == insN (O.lbl[i]!.map (L l))) &&
    (List.range O.lbl.size).all (fun i => i == 0 ||
      (decide (O.par[i]! < i) && decide (O.via[i]! < nl) && (O.pn[O.via[i]!]!)[O.par[i]!]! == i)) &&
    decide O.lbl.toList.Nodup

@[expose] def orbOK (Δ : List Nat) (L : Nat → Nat → Nat) (nl m : Nat) (x : Nat → Nat)
    (R : Option (OmegaData (List Nat) × Bool)) : Bool :=
  match R with
  | some R => omOK Δ L nl R.1 && R.1.lbl.size == m &&
      R.1.lbl.toList.all fun lb => insN (lb.map x) == lb
  | none => false

@[expose] def rChkF (n : Nat) (Δ : List Nat) (L : Nat → Nat → Nat) (ns : Nat)
    (AB : Nat → Nat → Nat) (z : Nat → Nat) (uWords : List (List Nat)) (yw nw : List Nat)
    (r m fuel : Nat) : Bool :=
  uWords.all (fun w => w.all fun l => decide (l < 2)) &&
    yw.all (fun l => decide (l < ns + uWords.length)) && nw.all (fun l => decide (l < ns)) &&
    Δ.all (fun p => decide (p < n)) &&
    (List.range uWords.length).all (fun k => (List.range n).all fun p =>
      L (ns + k) p == wordF AB (uWords.getD k []) p) &&
    orbOK Δ L (ns + uWords.length) m (wordF L nw)
      (omTwin (fun l lb => insN (lb.map (L l))) (ns + uWords.length) Δ (m + 1) fuel) &&
    (List.range uWords.length).all (fun k => (List.range n).all fun p =>
      L (ns + k) (z p) == z (L (ns + k) p)) &&
    (List.range n).all (fun p => wordF (fun _ => wordF L yw) (List.replicate r 0) p == p) &&
    !(List.range n).all (fun p => wordF L yw p == p) &&
    (List.range n).all (fun p => wordF L yw (z p) == z (wordF L yw p)) &&
    !(List.range n).all (fun p => wordF L yw (wordF L nw p) == wordF L nw (wordF L yw p))

@[expose] def ncChkF (n : Nat) (a z : Nat → Nat) : Bool :=
  !(List.range n).all fun p => a (z p) == z (a p)

end CFSG.KC.SLOm

end
