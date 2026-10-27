module

public import Certificates.Data.G23RecogHFactsInputs
import Certificates.Kernel.HcReplay.FactsGlue

public section

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData in
theorem certificate320015 : F5Eq ∧ ClosedAt sH1 ∧ ClosedAt sH2 ∧ ClosedAt sK ∧ ClosedAt sP ∧ PFacts ∧
    ClosedAt [gA 0] ∧ ClosedAt [gA 2] ∧ ClosedAt [gA 0 * gA 2] ∧ ClosedAt [gA 0 * (gA 2)⁻¹] ∧
    CentOK (gA 0) sC1 ∧ CentOK (gA 2) sC2 ∧ DisjOK (gA 0) sH2 ∧ DisjOK (gA 2) sH1 ∧
    NormSetOK [gA 0] sN1 ∧ NormSetOK [gA 2] sN2 ∧ Cent2OK (gA 0) (gA 2) sPZ ∧
    NormSetOK sP sPE ∧ CentOK (gA 0 * gA 2) sPZ ∧ NormSetOK [gA 0 * gA 2] sPE ∧
    CentOK (gA 0 * (gA 2)⁻¹) sPZ ∧ NormSetOK [gA 0 * (gA 2)⁻¹] sPE ∧
    InvertOK (gA 0) (gA 2) ∧ InvertOK (gA 2) (gA 0) ∧ ConjOK sT2 ∧ ConjOK sT1 ∧
    CentInOK (gA 0) sH1 sL1 ∧ CentInOK (gA 2) sH2 sL2 ∧ InvKOK ∧ CardCentT :=
  CFSG.KC.HcPack.certificate320015_facts

end Certificates
