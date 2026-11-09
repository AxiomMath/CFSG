module

public import Certificates.Kernel.Co1P.Defs21150
public import Certificates.Kernel.Co1P.Pt4C

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK

@[expose] noncomputable def pt4T (i : Nat) : Nat :=
  fget (getL (nat_lit 0) PT4W (Nat.div i (nat_lit 1024))) (Nat.mod i (nat_lit 1024)) (nat_lit 576)

@[expose] noncomputable def in4T (Y j : Nat) : Bool := andB (Nat.blt j 34560) (eqK Y (pt4T j))

@[expose] noncomputable def clos4T (E i : Nat) : Bool :=
  (fun p => andB (andB p.2 (eqK (pt4T i) p.1)) (strictB p.1 fun P => allN 8 fun l => strictB (brI l P)
    fun Y => in4T Y (fget E (Nat.add (Nat.mul 8 (Nat.mod i 64)) l) 16))) (pt4M i)

@[expose] noncomputable def clos4TC (c : Nat) : Bool := strictB (getL 0 J4 c) fun E => chunkK 34560 (clos4T E) c

@[expose] noncomputable def clos4TQ (q c : Nat) : Bool := clos4TC (Nat.add (Nat.mul 135 q) c)

@[expose] noncomputable def clos4TQ0 (c : Nat) : Bool := clos4TQ 0 c
@[expose] noncomputable def clos4TQ1 (c : Nat) : Bool := clos4TQ 1 c
@[expose] noncomputable def clos4TQ2 (c : Nat) : Bool := clos4TQ 2 c
@[expose] noncomputable def clos4TQ3 (c : Nat) : Bool := clos4TQ 3 c

end CertificateChecks.KernelCo1P

end
