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

@[expose] noncomputable def tree3U8 (c : Nat) : Bool :=
  treeChunk GX.F TW T3R T3Q (nat_lit 8) (nat_lit 33787) (nat_lit 6561) (nat_lit 15916)
    (nat_lit 131040) c

@[expose] noncomputable def tree3U9 (c : Nat) : Bool :=
  treeChunk GX.F TW T3R T3Q (nat_lit 9) (nat_lit 40348) (nat_lit 19683) (nat_lit 26571)
    (nat_lit 131040) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.tree3U8 0 26 1 as CertificateChecks.KernelD43.d43tree3c8_

#kc_each_step CertificateChecks.KernelD43.tree3U9 0 77 1 as CertificateChecks.KernelD43.d43tree3c9_

namespace CertificateChecks.KernelD43

#kc_forall_chunks tree3C8 (fun c => tree3U8 c = true) 26 CertificateChecks.KernelD43.d43tree3c8_ 1

#kc_forall_chunks tree3C9 (fun c => tree3U9 c = true) 77 CertificateChecks.KernelD43.d43tree3c9_ 1

end CertificateChecks.KernelD43

end
