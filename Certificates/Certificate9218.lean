
module

public import Certificates.Certificate9218Base

public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Presentation.RuExact
public import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Sporadic.Ru.Rels
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Bridge.VecSurj TauCeti in
theorem certificate9218 : (∀ v ∈ Sporadic.ruPresentation.relatorLetters,
      wordProd (img ruSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1) ∧
    (∀ i < 2, ∀ z ∈ ruSpec.surjWords[i]!, z ≠ 0 ∧ z.natAbs ≤ 3) ∧
    CFSG.Sporadic.Th.wordG (imgG ruSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      ruSpec.surjWords[0]! = a CFSG.Sporadic.Ru.Native.ruData ∧
    CFSG.Sporadic.Th.wordG (imgG ruSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      ruSpec.surjWords[1]! = b CFSG.Sporadic.Ru.Native.ruData := KernelSpor.RuRels.facts

end Certificates
