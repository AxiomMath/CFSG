module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
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
    ∧ ((∀ l < 14, orbitOK 35 mclXGens mclXInvs (wordTabS 35 mclXGens (mclXWords.getD l []))
        mclXOrbits[l]! = true ∧ mclXOrbits[l]!.tabs.size = mclXSizes.getD l 0) ∧
      (∀ l < 14, ∀ l' < 14, l ≠ l' →
        notInOK mclXOrbits[l]!.tabs (wordTabS 35 mclXGens (mclXWords.getD l' [])) = true) ∧
      (∀ l < 14, ∀ j ∈ mclXWords.getD l [], j < mclXGens.size) ∧
      wordTabS 35 mclXGens (mclXWords.getD 0 []) = idTab 35
    )
    ∧ (coverAllOK mclXEnum.tabs mclXOrbits = true)
    ∧ (∀ U : Finset (Fin 14), 0 ∈ U → (∑ l ∈ U, mclXSizes.getD l 0) ∣ 20160 →
      U = {0} ∨ U = Finset.univ
    ) := KernelSpor.McL2287.facts2287

end Certificates
