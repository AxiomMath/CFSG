module

public import CFSG.Certificates.Kernel.D43.TwinWSound
public import Certificates.Kernel.D43.Data
public import Certificates.Kernel.D43.HexP
public import Certificates.Kernel.Sporadic.ON.GenF
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def keyD43g8 (c : Nat) : Bool := keyChunk KT (RL.getD 8 []) (tabAt PX.F 0) c

@[expose] noncomputable def keyD43g8W (c : Nat) : Bool :=
  keyChunkW KT (RL.getD 8 []) (tabAt PX.F 0) c

theorem keyD43g8_of_W (c : Nat) (h : keyD43g8W c = true) : keyD43g8 c = true := keyChunk_of_W h

end CertificateChecks.KernelD43

#konf_slices CertificateChecks.KernelD43.keyD43g8 CertificateChecks.KernelD43.keyD43g8_of_W 0 104

namespace CertificateChecks.KernelD43

#kc_forall_chunks keys8 (fun c => keyD43g8 c = true) 104 CertificateChecks.KernelD43.keyD43g8 1

end CertificateChecks.KernelD43

end
