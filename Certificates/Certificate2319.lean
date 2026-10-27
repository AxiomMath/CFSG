module

public import CFSG.Sporadic.ThSchreier.PlaneSepDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
import Certificates.Kernel.SporSch.Th.PlaneText

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem certificate2319 : sepFNats.length = 248 ∧ (∀ n ∈ sepFNats, n < 2 ^ 248) ∧ sepWords.length = 124 ∧
    (∀ w ∈ sepWords, ∀ l ∈ w, l = 1 ∨ l = 2) ∧ sepRowNats.length = 248 ∧
    (∀ n ∈ sepRowNats, n < 2 ^ 248) ∧ sepWords.getD 0 [] = [] := KernelSporSch.ThPlane.facts2319

end Certificates
