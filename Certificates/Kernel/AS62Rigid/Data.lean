module

public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.LargeExtraspecial.AS62C36RigidInputs
meta import CFSG.LargeExtraspecial.AS62C36RigidInputs

public section

namespace CertificateChecks.KernelAS62

open CFSG.LargeExtraspecial.AS62 CFSG.LargeExtraspecial.AS62.Rigid

meta def bitsM (n : Nat) (p : Nat → Bool) : Array Nat :=
  Array.ofFn (n := n) fun j => if p j.val then 1 else 0

meta def oneM : Array Nat × Array Nat := (idA, idA)

meta def bM (i : Nat) : Array Nat × Array Nat := (bTab ()).getD i oneM

meta def p1M (i : Nat) : Array Nat × Array Nat := (p1Tab ()).getD i oneM

meta def p2M (i : Nat) : Array Nat × Array Nat := (p2Tab ()).getD i oneM

meta def r4 (g : Fin 4 → Array Nat × Array Nat) (k : Nat) : Bool := relOK4 g (relsB.getD k [])

meta def r1x (g : Fin 5 → Array Nat × Array Nat) (k : Nat) : Bool :=
  relOK5 g (rels1Extra.getD k [])

meta def r2x (g : Fin 5 → Array Nat × Array Nat) (k : Nat) : Bool :=
  relOK5 g (rels2Extra.getD k [])

meta def bkM : Array (Array Nat) := (bTab ()).map Prod.fst
meta def bkiM : Array (Array Nat) := (bTab ()).map Prod.snd
meta def p2kM : Array (Array Nat) := (p2Tab ()).map Prod.fst
meta def p2kiM : Array (Array Nat) := (p2Tab ()).map Prod.snd
meta def gkM : Array (Array Nat) := (Array.range 6).map genA
meta def gkiM : Array (Array Nat) := (Array.range 6).map genInvA
meta def fhM : Array Nat := fhatA'

meta def unaryM : Array (Array Nat) := #[
  bitsM 192 (fun i => r4 ![bM i, oneM, oneM, oneM] 0 && (bM i).1 != idA),
  bitsM 192 (fun i => r4 ![oneM, bM i, oneM, oneM] 1),
  bitsM 192 (fun i => r4 ![oneM, oneM, bM i, oneM] 2),
  bitsM 192 (fun i => r4 ![oneM, oneM, oneM, bM i] 3),
  bitsM 576 (fun i => r1x ![oneM, oneM, oneM, oneM, p1M i] 0),
  bitsM 960 (fun i => r2x ![oneM, oneM, oneM, oneM, p2M i] 0)]

meta def p5M : Array (Array Nat) := Array.ofFn (n := 192) fun a =>
  bitsM 192 fun b => r4 ![bM a.val, bM b, oneM, oneM] 5
meta def p6M : Array (Array Nat) := Array.ofFn (n := 192) fun a =>
  bitsM 192 fun c => r4 ![bM a.val, oneM, bM c, oneM] 6
meta def p9M : Array (Array Nat) := Array.ofFn (n := 192) fun b =>
  bitsM 192 fun c => r4 ![oneM, bM b.val, bM c, oneM] 9
meta def p4M : Array (Array Nat) := Array.ofFn (n := 192) fun c =>
  bitsM 192 fun d => r4 ![oneM, oneM, bM c.val, bM d] 4
meta def p7M : Array (Array Nat) := Array.ofFn (n := 192) fun a =>
  bitsM 192 fun d => r4 ![bM a.val, oneM, oneM, bM d] 7
meta def p8M : Array (Array Nat) := Array.ofFn (n := 192) fun b =>
  bitsM 192 fun d => r4 ![oneM, bM b.val, oneM, bM d] 8
meta def q1M : Array (Array Nat) := Array.ofFn (n := 192) fun d =>
  bitsM 576 fun u => r1x ![oneM, oneM, oneM, bM d.val, p1M u] 1
meta def q2M : Array (Array Nat) := Array.ofFn (n := 192) fun b =>
  bitsM 576 fun u => r1x ![oneM, bM b.val, oneM, oneM, p1M u] 2
meta def r1M : Array (Array Nat) := Array.ofFn (n := 192) fun d =>
  bitsM 960 fun v => r2x ![oneM, oneM, oneM, bM d.val, p2M v] 1
meta def r2M : Array (Array Nat) := Array.ofFn (n := 192) fun c =>
  bitsM 960 fun v => r2x ![oneM, oneM, bM c.val, oneM, p2M v] 2
meta def c0M : Array (Array Nat) := Array.ofFn (n := 192) fun a =>
  bitsM 384 fun f => conjA ((bhTab ()).getD f oneM) (genA 0) == (bM a.val).1
meta def c1M : Array (Array Nat) := Array.ofFn (n := 192) fun b =>
  bitsM 384 fun f => conjA ((bhTab ()).getD f oneM) (genA 1) == (bM b.val).1

end CertificateChecks.KernelAS62

#kss_perms CertificateChecks.KernelAS62.BK 6 CertificateChecks.KernelAS62.bkM
#kss_perms CertificateChecks.KernelAS62.BKI 6 CertificateChecks.KernelAS62.bkiM
#kss_perms CertificateChecks.KernelAS62.P2K 6 CertificateChecks.KernelAS62.p2kM
#kss_perms CertificateChecks.KernelAS62.P2KI 6 CertificateChecks.KernelAS62.p2kiM
#kss_perms CertificateChecks.KernelAS62.GK 6 CertificateChecks.KernelAS62.gkM
#kss_perms CertificateChecks.KernelAS62.GKI 6 CertificateChecks.KernelAS62.gkiM
#ks_perm CertificateChecks.KernelAS62.FH 6 CertificateChecks.KernelAS62.fhM
#kss_perms CertificateChecks.KernelAS62.UN 1 CertificateChecks.KernelAS62.unaryM
#kss_perms CertificateChecks.KernelAS62.P5 1 CertificateChecks.KernelAS62.p5M
#kss_perms CertificateChecks.KernelAS62.P6 1 CertificateChecks.KernelAS62.p6M
#kss_perms CertificateChecks.KernelAS62.P9 1 CertificateChecks.KernelAS62.p9M
#kss_perms CertificateChecks.KernelAS62.P4 1 CertificateChecks.KernelAS62.p4M
#kss_perms CertificateChecks.KernelAS62.P7 1 CertificateChecks.KernelAS62.p7M
#kss_perms CertificateChecks.KernelAS62.P8 1 CertificateChecks.KernelAS62.p8M
#kss_perms CertificateChecks.KernelAS62.Q1 1 CertificateChecks.KernelAS62.q1M
#kss_perms CertificateChecks.KernelAS62.Q2 1 CertificateChecks.KernelAS62.q2M
#kss_perms CertificateChecks.KernelAS62.R1 1 CertificateChecks.KernelAS62.r1M
#kss_perms CertificateChecks.KernelAS62.R2 1 CertificateChecks.KernelAS62.r2M
#kss_perms CertificateChecks.KernelAS62.C0 1 CertificateChecks.KernelAS62.c0M
#kss_perms CertificateChecks.KernelAS62.C1 1 CertificateChecks.KernelAS62.c1M

end
