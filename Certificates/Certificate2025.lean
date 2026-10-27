module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuterCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.LocalComp.McLYK
import Certificates.Kernel.LocalComp.McLYSums
import Certificates.Kernel.LocalComp.McLYNeg

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd in
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore in
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native in
theorem certificate2025 : (mclFix1.length = 11 ∧ mclYGens.size = 4 ∧ invsOK 11 mclYGens mclYInvs = true ∧
      mclYOrbits.size = 10 ∧ permOK 275 (mclCentTbl 17) = true ∧
      ∀ k < 4, permOK 275 (mclCentTbl (k + 18)) = true
    )
    ∧ (enumOK 11 mclYGens mclYEnum = true ∧ mclYEnum.tabs.size = 7920)
    ∧ ((∀ l < 10, orbitOK 11 mclYGens mclYInvs (wordTabS 11 mclYGens (mclYWords.getD l []))
        mclYOrbits[l]! = true ∧ mclYOrbits[l]!.tabs.size = mclYSizes.getD l 0) ∧
      (∀ l < 10, ∀ l' < 10, l ≠ l' →
        notInOK mclYOrbits[l]!.tabs (wordTabS 11 mclYGens (mclYWords.getD l' [])) = true) ∧
      (∀ l < 10, ∀ j ∈ mclYWords.getD l [], j < mclYGens.size) ∧
      wordTabS 11 mclYGens (mclYWords.getD 0 []) = idTab 11
    )
    ∧ (coverAllOK mclYEnum.tabs mclYOrbits = true)
    ∧ (∀ U : Finset (Fin 10), 0 ∈ U → (∑ l ∈ U, mclYSizes.getD l 0) ∣ 7920 →
      U = {0} ∨ U = Finset.univ
    ) :=
  ⟨KernelLC.McLY.basic, KernelLC.McLY.enum, KernelLC.McLY.orbits, KernelLC.McLY.cover,
    KernelLC.McLY.sums⟩

end Certificates
