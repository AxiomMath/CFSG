module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public import Certificates.Kernel.MonsterB.Tower3049Data

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Fischer (F4)

namespace CertificateChecks.Batch16005

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Fischer (F4)

private theorem ringEquiv_F4_cases_0 : F4.ω * F4.ω + F4.ω + 1 = 0 := by
  decide +kernel

private theorem ringEquiv_F4_cases_1 :
    ∀ y : F4, y * y + y + 1 = 0 → y = F4.ω ∨ y = F4.ω * F4.ω := by
  decide +kernel

private theorem ringEquiv_F4_cases_2 : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = 1 + F4.ω := by
  decide +kernel

private theorem ringEquiv_F4_cases_3 : 1 + F4.ω * F4.ω = (1 + F4.ω) * (1 + F4.ω) := by
  decide +kernel

private theorem det_eq_one_of_conj_4 :
    ∀ d e c : F4, e * d = 1 → d * (e * e) = c ^ 6 → c ≠ 0 → d = 1 := by
  decide +kernel

end CertificateChecks.Batch16005

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
open CFSG.Fischer (F4) in
theorem certificate16005 : (
    F4.ω * F4.ω + F4.ω + 1 = 0
  ) ∧ (
    ∀ y : F4, y * y + y + 1 = 0 → y = F4.ω ∨ y = F4.ω * F4.ω
  ) ∧ (
    ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = 1 + F4.ω
  ) ∧ (
    1 + F4.ω * F4.ω = (1 + F4.ω) * (1 + F4.ω)
  ) ∧ (
    ∀ d e c : F4, e * d = 1 → d * (e * e) = c ^ 6 → c ≠ 0 → d = 1
  ) := by
  exact ⟨CertificateChecks.Batch16005.ringEquiv_F4_cases_0, CertificateChecks.Batch16005.ringEquiv_F4_cases_1,
    CertificateChecks.Batch16005.ringEquiv_F4_cases_2, CertificateChecks.Batch16005.ringEquiv_F4_cases_3,
    CertificateChecks.Batch16005.det_eq_one_of_conj_4⟩

end Certificates
