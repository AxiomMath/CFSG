module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.Seitz77Sec27L34Ord3

public section

namespace CFSG.Certificates.Kernel.PkCV.L34O3

open CFSG.GH74.KGroups.L34 CFSG.Certificates CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def o3N (p : Nat) : Bool :=
  allN 42 (fun i => Nat.beq (fpow (pg 6 (mask 6) p) 3 i) i) &&
    !allN 42 (fun i => Nat.beq (fpow (pg 6 (mask 6) p) 1 i) i)

@[expose] noncomputable def o3 (q : CV 42) : Bool := strictB q.1 o3N

@[expose] noncomputable def hcF (c : Nat) : List (CV 42) → Bool
  | a :: _ => strictB a.1 fun A =>
      ((elemsC QP).filter fun g => strictB g.1 fun p => eq22 42 6 (mask 6) p A A p).length == c
  | [] => false

@[expose] noncomputable def ord3F (m c : Nat) : Bool :=
  ((elemsC QP).filter o3).length == m && hcF c ((elemsC QP).filter o3)

end CFSG.Certificates.Kernel.PkCV.L34O3

end
