module

public import CFSG.Sporadic.Schreier.J4SFormData
public meta import CFSG.Sporadic.Schreier.J4SFormData
public import Certificates.Certificate2171
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public meta import CFSG.Sporadic.Schreier.J4SNative
public meta import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

theorem formUp_check : xorRows112 formUpRows (transposeRows 112 formUpRows) = formRows ∧
    (∀ i < 112, ∀ j < 112, (formUpRows[i]?.getD 0).testBit j =
      if i < j then (formRows[i]?.getD 0).testBit j else decide (i = j)) ∧
    (∀ i < 112, formUpRows[i]?.getD 0 < 2 ^ 112) ∧ formRows.size = 112 ∧
    (∀ i < 112, formRows[i]?.getD 0 < 2 ^ 112) :=
  Certificates.certificate2171.1

theorem formInv_check : mulRows 112 formRows formInvRows = idRows 112 ∧
    mulRows 112 formInvRows formRows = idRows 112 :=
  Certificates.certificate2171.2.1

theorem formDefect_check : defectOK An.1 = true ∧ defectOK Bn.1 = true :=
  Certificates.certificate2171.2.2

end CFSG.Sporadic.J4Schreier
