module

public import Certificates.Data.Kernel.D43.Tree
public import Certificates.Kernel.D43.Tree3Data
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def tree3P2c (c : Nat) : Bool :=
  treeChunk GX.F TW T3R T3Q (nat_lit 4) (nat_lit 7216) (nat_lit 26244) (nat_lit 26571)
    (nat_lit 131070) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.tree3P2c 0 103 1 as CertificateChecks.KernelD43.d43tree3b_

namespace CertificateChecks.KernelD43

#kc_forall_chunks tree3B (fun c => tree3P2c c = true) 103 CertificateChecks.KernelD43.d43tree3b_ 1

end CertificateChecks.KernelD43

end
