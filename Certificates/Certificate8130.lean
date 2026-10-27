module

public import CFSG.RankThree.Native.LyFiveArrays
public import CFSG.RankThree.Native.LySeedCheck
public import CFSG.RankThree.Native.LyFiveCheckInputs
import Certificates.Kernel.SporSch.Ly.Five8130

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
  CFSG.Monster.B.Fischer in
theorem certificate8130 : (lyFiveSmallCheck = true)
    ∧ (lyFiveTreeCheck = true)
    ∧ (lyFiveRelsCheck = true) :=
  ⟨KernelSporSch.LyFR.small, KernelSporSch.LyFR.tree, KernelSporSch.LyFR.rels⟩

end Certificates
