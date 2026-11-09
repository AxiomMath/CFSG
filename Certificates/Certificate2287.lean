module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.SylowSimple
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.Sporadic.OddCore.McLLF

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native in
theorem certificate2287 : (mclFix.length = 35 ∧ mclXGens.size = 2 ∧ invsOK 35 mclXGens mclXInvs = true ∧
      mclXOrbits.size = 14 ∧ permOK 275 (mclCentTbl 4) = true ∧
      ∀ k < 2, permOK 275 (mclCentTbl (k + 5)) = true
    )
    ∧ (CFSG.PSL3Four.Native.enumOK 35 mclXGens mclXEnum = true ∧ mclXEnum.tabs.size = 20160)
    ∧ (∀ i < 4, (∀ w ∈ mclSylWords.getD i [], ∀ j ∈ w, j < mclXGens.size) ∧
      CFSG.PSL3Four.Native.enumOK 35 (mclSylGens i) (mclSylEnum i) = true ∧
      (mclSylEnum i).tabs.size = mclSylSizes.getD i 0 ∧
      ∀ q < (mclSylEnum i).tabs.size, (mclSylEnum i).tabs[q]! = idTab 35 ∨
        wordTabS 35 #[(mclSylEnum i).tabs[q]!] (List.replicate (mclSylPrimes.getD i 0) 0) ≠
          idTab 35 ∨
        ∃ cs W, nclWordsOK 35 mclXGens mclXInvs (mclSylEnum i).tabs[q]! cs W = true
    ) := KernelSpor.McL2287.facts2287

end Certificates
