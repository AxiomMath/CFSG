module

public import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.Sporadic.OddCore.HLF

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native CFSG.Sporadic.HeldB in
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2275 : (incListOK 8330 105 heOmega0 = true ∧
      (∀ j < 9, permChk 105 heKGens[j]! = true ∧ heKGens[j]!.size = 105 ∧
        agreeOK 105 (heInnerC0 j) heOmega0 heKGens[j]! = true) ∧
      (∀ j < 5, ∀ i ∈ heDWords.getD j [], i < 9)
    )
    ∧ (enumOK 105 heKGens heKEnum = true ∧ heKEnum.tabs.size = 40320)
    ∧ (enumOK 105 heDGens heDEnum = true ∧ heDEnum.tabs.size = 20160 ∧
      normalOK 105 heDEnum.tabs heKGens heKInvs heDGens = true
    )
    ∧ (heDOrbits.size = 10 ∧ heDGens.size = 5 ∧
      (∀ l < 10, orbitOK 105 heDGens heDInvs (wordTabS 105 heDGens (heDClassWords.getD l []))
        heDOrbits[l]! = true ∧ heDOrbits[l]!.tabs.size = heDClassSizes.getD l 0) ∧
      (∀ l < 10, ∀ l' < 10, l ≠ l' →
        notInOK heDOrbits[l]!.tabs (wordTabS 105 heDGens (heDClassWords.getD l' [])) = true) ∧
      (∀ l < 10, ∀ j ∈ heDClassWords.getD l [], j < heDGens.size) ∧
      wordTabS 105 heDGens (heDClassWords.getD 0 []) = idTab 105
    )
    ∧ (coverAllOK heDEnum.tabs heDOrbits = true)
    ∧ (∀ U : Finset (Fin 10), 0 ∈ U →
      (∑ l ∈ U, heDClassSizes.getD l 0) ∣ 20160 → U = {0} ∨ U = Finset.univ
    ) := KernelSpor.HeL.facts2275

end Certificates
