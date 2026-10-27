module

public import Certificates.Kernel.Co2Smith.RootDefs
public import CFSG.Sporadic.Co2Smith.GlCosetWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def b3K : Nat := mulV x34K x43K
@[expose] noncomputable def vK : Nat := mulV (mulV uK w0K) uK
@[expose] noncomputable def v1K : Nat := mulV (mulV (mulV b3K b3K) vK) b3K

@[expose] noncomputable def cosetElemK : Bool :=
  mapsK zK 80 80 && mapsK (LP 14) 80 80 && mapsK (LP 14) 1172 1339 &&
    mapsK w0K 80 80 && mapsK b3K 80 80 && mapsK b3K 942 1172 && mapsK b3K 582 1348 &&
    mapsK uK 1348 728 && mapsK w0K 728 1172 &&
    mapsK (mulV v1K zK) 582 1977 && (glWit0Pts 1).contains 1977 &&
    glM2Words.all (fun w => w.all (· < 22) && mapsK (wK LP w) 80 80 && mapsK (wK LP w) 582 582) &&
    mapsK (wK LP glM2Words[0]!) 942 942

theorem cosetElem_k : cosetElemK = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
