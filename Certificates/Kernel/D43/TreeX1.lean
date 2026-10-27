module

public import Certificates.Data.Kernel.D43.Tree
public import Certificates.Kernel.D43.TreeData
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def treeD43x1 (c : Nat) : Bool :=
  treeChunk GX.F TW TR TQ (nat_lit 1) (nat_lit 26572) (nat_lit 19683) (nat_lit 26571)
    (nat_lit 131069) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.treeD43x1 0 77 1 as CertificateChecks.KernelD43.d43treex1_

namespace CertificateChecks.KernelD43

#kc_forall_chunks treeX1 (fun c => treeD43x1 c = true) 77 CertificateChecks.KernelD43.d43treex1_ 1

end CertificateChecks.KernelD43

end
