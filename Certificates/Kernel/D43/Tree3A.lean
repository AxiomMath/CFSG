module

public import Certificates.Data.Kernel.D43.TreeDisj
public import Certificates.Kernel.D43.Tree3Data
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def tree3P1b (c : Nat) : Bool :=
  treeChunk GX.F TW T3R T3Q (nat_lit 1) (nat_lit 84) (nat_lit 6804) (nat_lit 479)
    (nat_lit 131069) c

@[expose] noncomputable def disj3P1b (c : Nat) : Bool :=
  disjChunk T3R (nat_lit 84) (nat_lit 6804) TR TQ (nat_lit 1) (nat_lit 26572) (nat_lit 19683) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.tree3P1b 0 27 1 as CertificateChecks.KernelD43.d43tree3a_

#kc_each_step CertificateChecks.KernelD43.disj3P1b 0 27 1 as CertificateChecks.KernelD43.d43disj3a_

namespace CertificateChecks.KernelD43

#kc_forall_chunks tree3A (fun c => tree3P1b c = true) 27 CertificateChecks.KernelD43.d43tree3a_ 1

#kc_forall_chunks disj3A (fun c => disj3P1b c = true) 27 CertificateChecks.KernelD43.d43disj3a_ 1

end CertificateChecks.KernelD43

end
