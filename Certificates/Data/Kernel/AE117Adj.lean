module

public import Certificates.Data.GH74.AE117

public section

namespace Certificates.Kernel.AE117Adj

open Certificates.AE117 CFSG.ClassicalInvolution.Q3.AE

@[expose] def quads (n : Nat) : List (Fin n × Fin n × Fin n × Fin n) :=
  ((List.finRange n).flatMap fun a => (List.finRange n).flatMap fun b =>
    (List.finRange n).flatMap fun c => (List.finRange n).map fun d => (a, b, c, d)).filter
    fun q => decide (q.1 < q.2.1) && decide (q.2.1 < q.2.2.1) && decide (q.2.2.1 < q.2.2.2)

@[expose] def qset {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) : Finset (Fin n) :=
  [q.1, q.2.1, q.2.2.1, q.2.2.2].toFinset

@[expose] def memQ {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) (b : Bool) : List (Wr n) :=
  memLC q.1 q.2.1 q.2.2.1 q.2.2.2 b

@[expose] def ord5G {n : Nat} (x : Wr n) : Bool := decide (x.perm ^ 5 = 1) && ord5Pi x

@[expose] def adjB {n : Nat} (q q' : Fin n × Fin n × Fin n × Fin n) : Bool :=
  [true, false].any fun b => [true, false].any fun b' =>
    (memQ q b).any fun k => (memQ q' b').any fun k' => ord5G (k * k')

@[expose] def adjCheckOn (n : Nat) (qs : List (Fin n × Fin n × Fin n × Fin n)) : Bool :=
  qs.all fun q => (quads n).all fun q' =>
    decide ((qset q ∩ qset q').card = 3) == adjB q q'

@[expose] def adjCheckL (n : Nat) : Bool := adjCheckOn n (quads n)

@[expose] def sw {n : Nat} (a b i : Fin n) : Fin n := if i = a then b else if i = b then a else i

@[expose] def dT {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) :
    List (Fin n × Fin n × Fin n × Fin n) :=
  [(q.1, q.2.1, q.2.2.1, q.2.2.2), (q.1, q.2.2.1, q.2.1, q.2.2.2), (q.1, q.2.2.2, q.2.1, q.2.2.1)]

@[expose] def dP {n : Nat} (t : Fin n × Fin n × Fin n × Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap t.1 t.2.1 * Equiv.swap t.2.2.1 t.2.2.2

@[expose] def dF {n : Nat} (t : Fin n × Fin n × Fin n × Fin n) (i : Fin n) : Fin n :=
  sw t.1 t.2.1 (sw t.2.2.1 t.2.2.2 i)

@[expose] def dQ {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) : List (Equiv.Perm (Fin n)) :=
  (dT q).map dP

@[expose] def moves5F {n : Nat} (f : Fin n → Fin n) : Bool :=
  (List.finRange n).any fun i => f (f (f (f (f i)))) != i

@[expose] def vec5 {n : Nat} (x : Wr n) (i : Fin n) : ZMod 2 :=
  x.vec i + x.vec (x.perm.symm i) + x.vec (x.perm.symm (x.perm.symm i)) +
    x.vec (x.perm.symm (x.perm.symm (x.perm.symm i))) +
    x.vec (x.perm.symm (x.perm.symm (x.perm.symm (x.perm.symm i))))

@[expose] def ord5Fast {n : Nat} (x : Wr n) : Bool :=
  (List.finRange n).any (fun i => x.perm i != i) &&
    (List.finRange n).all (fun i => x.perm (x.perm (x.perm (x.perm (x.perm i)))) == i) &&
    ((List.finRange n).all (fun i => vec5 x i == 0) || (List.finRange n).all (fun i => vec5 x i == 1))

@[expose] def dOK {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) : Bool :=
  (dT q).all fun t => moves5F (dF t)

@[expose] def wit2 {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) : Wr n :=
  ⟨indL [q.1, q.2.2.1], Equiv.swap q.1 q.2.1 * Equiv.swap q.2.2.1 q.2.2.2⟩

@[expose] def wit4 {n : Nat} (q : Fin n × Fin n × Fin n × Fin n) : Wr n :=
  ⟨indL [q.1, q.2.2.2], Equiv.swap q.1 q.2.2.1 * Equiv.swap q.2.1 q.2.2.2⟩

@[expose] def adjPairW {n : Nat} (q q' : Fin n × Fin n × Fin n × Fin n) : Bool :=
  cond (decide ((qset q ∩ qset q').card = 3))
    (ord5Fast (wit2 q * wit4 q') || ord5Fast (wit2 q * wit2 q'))
    ((dT q).all fun t => (dT q').all fun t' =>
      moves5F (fun i => dF t (dF t' i)) || decide (dP t * dP t' = 1))

@[expose] def adjCheckLW (n : Nat) : Bool :=
  (quads n).all dOK && (quads n).all fun q => (quads n).all fun q' => adjPairW q q'

end Certificates.Kernel.AE117Adj
