module

public import Certificates.Data.Kernel.D43.TreeRel
public import Certificates.Kernel.D43.Rel3Data
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

abbrev B3X : Nat := 121695702607180549954634604969984

@[expose] noncomputable def rel3c (c : Nat) : Bool := brelChunk GX.F TW B3X R3W (nat_lit 179) c

@[expose] noncomputable def key3c (c : Nat) : Bool := bkeyChunk GX.F TW B3X K3W K3K (nat_lit 52) c

@[expose] noncomputable def neq3c (c : Nat) : Bool := neqChunk GX.F TW B3X X3W Y3W (nat_lit 51) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.rel3c 0 12 1 as CertificateChecks.KernelD43.d43rel3_

#kc_each_step CertificateChecks.KernelD43.key3c 0 4 1 as CertificateChecks.KernelD43.d43bkey3_

#kc_each_step CertificateChecks.KernelD43.neq3c 0 3 1 as CertificateChecks.KernelD43.d43neq3_

namespace CertificateChecks.KernelD43

#kc_forall_chunks rel3 (fun c => rel3c c = true) 12 CertificateChecks.KernelD43.d43rel3_ 1

#kc_forall_chunks key3 (fun c => key3c c = true) 4 CertificateChecks.KernelD43.d43bkey3_ 1

#kc_forall_chunks neq3 (fun c => neq3c c = true) 3 CertificateChecks.KernelD43.d43neq3_ 1

open CFSG.KC.D43

theorem dist3 : distinctAll K3K 52 = true := by decide +kernel

theorem negRel3 : (!relChk GX.F TW B3X 1 &&
    !distinctAll (fun i => K3K (Nat.add i (Nat.beq i 0).toNat)) 52) = true := by
  decide +kernel

end CertificateChecks.KernelD43

end
