module

public import CFSG.RankThree.Native.FiveTwoData
import Certificates.Kernel.FiveTwo.Glue
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Blueprint CFSG.SectionRank
  CFSG.SectionRank.Native in
theorem certificate8127 : (FiveTwoData.check (ops2 80) j3FiveTwo = true)
    ∧ (FiveTwoData.check (ops2 24) co1FiveTwo = true)
    ∧ (FiveTwoData.check (ops2 22) co2FiveTwo = true)
    ∧ (FiveTwoData.check (ops2 22) co3FiveTwo = true)
    ∧ (FiveTwoData.check (ops2 20) hsFiveTwo = true)
    ∧ (FiveTwoData.check (ops3 21) mclFiveTwo = true)
    ∧ (FiveTwoData.check (opsP 5 133) hnFiveTwo = true)
    ∧ (FiveTwoData.check (ops3 64) suzFiveTwo = true)
    ∧ (FiveTwoData.check (opsP 5 111) lyFiveTwo = true)
    ∧ (FiveTwoData.check (ops2 248) thFiveTwo = true)
    ∧ (FiveTwoData.check (ops3 154) onFiveTwo = true) :=
  ⟨KernelFT.j3, KernelFT.co1, KernelFT.co2, KernelFT.co3, KernelFT.hs, KernelFT.mcl, KernelFT.hn,
    KernelFT.suz, KernelFT.ly, KernelFT.th, KernelFT.on⟩

end Certificates
