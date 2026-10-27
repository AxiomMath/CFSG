module

public import CFSG.GH74.Uniqueness.SU.KI1r4QAutInputs
import Certificates.Kernel.UT3F4.Checks
import CFSG.Certificates.Kernel.UT3F4.Sound

public section

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Uniqueness in
open CFSG.GH74.Uniqueness.SU in
open CFSG.GH74.Uniqueness.SU.K in
open CFSG.GH74.Uniqueness.SU.K.R4 in
open CFSG.GH74.Uniqueness.SU.K.R4.Q64 in
open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.GLS.Bg.TwoGroups in
theorem certificate5141 : ∀ t ∈ candList,
    (∀ i, evalT wordOf t (evalT wordOf t (gen i)) = gen i) →
    IsAutT allP gen wordOf t →
    (allP.filter (fun g => evalT wordOf t g = g)).length = 8 →
    (allP.filter (fun g => evalT wordOf t g = g ∧ g * g = 1)).length = 2 →
    ∃ p ∈ pairList, IsAutT allP gen wordOf (mkS t p) ∧
      ∀ i, evalT wordOf (mkS t p) (phiFun (gen i)) = evalT wordOf t (mkS t p i) :=
  CFSG.Certificates.Kernel.UT3F4.key_of_checkN Kernel.UT3F4.checkN_true

end Certificates
