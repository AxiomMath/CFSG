module

public import Certificates.Data.Kernel.E64F
public import CFSG.Quasithin.EmptyFaithful.S151S9TNineData

public section

namespace CFSG.KC.IdxF

open CFSG.KC.E64F CFSG.Quasithin.S151S9T

@[expose] def three (f g h : Nat → Nat) : Nat → Nat → Nat
  | 0 => f
  | 1 => g
  | _ => h

@[expose] def idOn (n : Nat) (f : Nat → Nat) : Bool := (List.range n).all fun p => f p == p

@[expose] def eqOn (n : Nat) (f g : Nat → Nat) : Bool := (List.range n).all fun p => f p == g p

@[expose] def fixLab (Δ : List Nat) (f : Nat → Nat) : Bool := insN (Δ.map f) == Δ

@[expose] def distinct5 (n : Nat) (d : Nat → Nat → Nat) : Bool :=
  (List.range 5).all fun i => (List.range 5).all fun i' => i == i' || !eqOn n (d i) (d i')

@[expose] def xF (W : Idx3Wit) (M : Nat → Nat → Nat → Nat) : Nat → Nat := wordF (M W.p) W.xw

@[expose] def idx3OkF (W : Idx3Wit) (n : Nat) (Δ : List Nat) (nm ns : Nat) (mlen : Nat → Nat)
    (M : Nat → Nat → Nat → Nat) (Sl : Nat → Nat → Nat) (z : Nat → Nat) : Bool :=
  Δ.all (fun p => decide (p < n)) && decide (W.p < nm) && mlen W.p == 1 &&
    W.xw.all (fun l => decide (l < ns + 1)) &&
    W.czv.length == nm &&
    ((List.range nm).all fun j => W.czv.getD j false ==
      (List.range (mlen j)).all fun k =>
        eqOn n (fun p => z (M j (ns + k) p)) (fun p => M j (ns + k) (z p))) &&
    idOn n (fun p => xF W M (xF W M (xF W M p))) && !idOn n (xF W M) &&
    W.rw.length == 5 && W.ri.length == 5 &&
    (List.range 5).all (fun i =>
      (W.rw.getD i []).all (fun l => decide (l < ns)) &&
        (W.ri.getD i []).all (fun l => decide (l < ns)) &&
        idOn n (fun p => wordF Sl (W.rw.getD i []) (wordF Sl (W.ri.getD i []) p)) &&
        fixLab Δ (wordF (three (xF W M) (wordF Sl (W.rw.getD i [])) id) [0, 0, 1, 0]) &&
        fixLab Δ (wordF (three (xF W M) (wordF Sl (W.rw.getD i [])) id) [0, 1, 0, 0])) &&
    distinct5 n (fun i => wordF (three (wordF Sl (W.rw.getD i [])) (xF W M)
      (wordF Sl (W.ri.getD i []))) dcWord)

@[expose] def x1F (W : Idx9Wit) (M : Nat → Nat → Nat → Nat) : Nat → Nat := wordF (M W.p₁) W.x1w

@[expose] def x6F (W : Idx9Wit) (M : Nat → Nat → Nat → Nat) : Nat → Nat := wordF (M W.p₆) W.x6w

@[expose] def fF (W : Idx9Wit) (M : Nat → Nat → Nat → Nat) (k : Nat) : Nat → Nat :=
  if k = 0 then x1F W M else if k = 1 then x6F W M else
  if k = 2 then fun p => x1F W M (x6F W M p) else fun p => x1F W M (x6F W M (x6F W M p))

@[expose] def idx9OkF (W : Idx9Wit) (n : Nat) (Δ : List Nat) (nm ns : Nat) (mlen : Nat → Nat)
    (M : Nat → Nat → Nat → Nat) (Sl : Nat → Nat → Nat) : Bool :=
  Δ.all (fun p => decide (p < n)) && decide (W.p₁ < nm) && decide (W.p₆ < nm) &&
    mlen W.p₁ == 1 && mlen W.p₆ == 1 &&
    W.x1w.all (fun l => decide (l < ns + 1)) && W.x6w.all (fun l => decide (l < ns + 1)) &&
    idOn n (fun p => x1F W M (x1F W M (x1F W M p))) && !idOn n (x1F W M) &&
    idOn n (fun p => x6F W M (x6F W M (x6F W M p))) && !idOn n (x6F W M) &&
    eqOn n (fun p => x1F W M (x6F W M p)) (fun p => x6F W M (x1F W M p)) &&
    W.rw.length == 5 && W.ri.length == 5 &&
    (List.range 5).all (fun i =>
      (W.rw.getD i []).all (fun l => decide (l < ns)) &&
        (W.ri.getD i []).all (fun l => decide (l < ns)) &&
        idOn n (fun p => wordF Sl (W.rw.getD i []) (wordF Sl (W.ri.getD i []) p)) &&
        (List.range 3).all fun a => (List.range 3).all fun b =>
          fixLab Δ (wordF (three (x1F W M) (x6F W M) (wordF Sl (W.rw.getD i []))) (conj9Word a b))) &&
    (List.range 4).all fun k =>
      idOn n (fun p => fF W M k (fF W M k (fF W M k p))) &&
        distinct5 n (fun i => wordF (three (wordF Sl (W.rw.getD i [])) (fF W M k)
          (wordF Sl (W.ri.getD i []))) dcWord)

end CFSG.KC.IdxF

end
