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

end Certificates.Kernel.AE117Adj
