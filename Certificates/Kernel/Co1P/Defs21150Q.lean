module

public import Certificates.Kernel.Co1P.Defs21154
public import Certificates.Kernel.Co1P.Defs21156

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def forceKT {α : Sort _} (t : KT) (k : KT → α) : α :=
  KT.rec (motive := fun _ => (KT → α) → α) (fun k => k KT.leaf)
    (fun _ x _ ihl ihr k => ihl fun l' => Nat.rec (motive := fun _ => α)
      (ihr fun r' => k (KT.node l' 0 r')) (fun n _ => ihr fun r' => k (KT.node l' (Nat.succ n) r')) x) t k

@[expose] noncomputable def qClosS (L S : List Nat) : Bool :=
  andB (andB (sincK S) (treeAll 10 S))
    (forceKT (treeOf 10 S) fun T => L.all fun X => allN 8 fun l => memKT (keyK (mulWK X (getL 0 QG l))) T)

@[expose] noncomputable def qClosT : Bool := strictL QL fun L => qClosS L (sortP 10 (modL L))

end CertificateChecks.KernelCo1P

end
