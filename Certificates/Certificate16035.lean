
module

public import Certificates.Certificate16035Base
import all Certificates.Certificate16035Base


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

namespace CertificateChecks.Batch16035

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

end CertificateChecks.Batch16035

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu in
theorem certificate16035 : (
    rowCheck (pairN (0 : Fin 24) (1 : Fin 24)) 12288 = true
  ) ∧ (
    ∀ i : Fin 7, rowCheck (pairN (pa7 i) (pb7 i)) (rCoord i) = true
  ) ∧ (
    ∀ i : Fin 7,
    Native.actD 22 Native.quotientBasis (sCoord i) = rCoord i ∨
      Native.actD 22 Native.quotientBasis (sCoord i) = rCoord i ^^^ 12288
  ) ∧ (
    ∀ c : Fin 4 → ZMod 2, xsel4 c = 0 ∨ xsel4 c = 31 ∨
    ∃ i : Fin 7, ∃ b : ZMod 2, xsel4 c = sCoord i ^^^ sel b 31
  ) ∧ (
    ∀ (i : Fin 7) (b : ZMod 2), ∃ c : Fin 4 → ZMod 2,
    xsel4 c = sCoord i ^^^ sel b 31
  ) ∧ (
    ∀ c : Fin 3 → ZMod 2,
    xsel3 c = 0 ∨
      xsel3 c = 31 ∨
      ∃ i : Fin 7, (i : ℕ) < 3 ∧ ∃ b : ZMod 2,
        xsel3 c = sCoord i ^^^ sel b 31
  ) ∧ (
    ∀ (i : Fin 7), (i : ℕ) < 3 → ∀ b : ZMod 2, ∃ c : Fin 3 → ZMod 2,
    xsel3 c = sCoord i ^^^ sel b 31
  ) ∧ (
    ∀ c : Fin 4 → ZMod 2, xsel4 c < 2 ^ 22
  ) ∧ (
    ∀ c : Fin 4 → ZMod 2, xsel4 c = 0 → c = 0
  ) ∧ (
    ∀ c : Fin 3 → ZMod 2, xsel3 c < 2 ^ 22
  ) ∧ (
    ∀ c : Fin 3 → ZMod 2, xsel3 c = 0 → c = 0
  ) := by
  exact ⟨CertificateChecks.Batch16035.dec_v0_0, CertificateChecks.Batch16035.rCoord_check_1, CertificateChecks.Batch16035.sCoord_act_2,
    CertificateChecks.Batch16035.xsel4_cases_3, CertificateChecks.Batch16035.xsel4_exists_4, CertificateChecks.Batch16035.xsel3_cases_5,
    CertificateChecks.Batch16035.xsel3_exists_6, CertificateChecks.Batch16035.linearIndependent_gen4_h1_7,
    CertificateChecks.Batch16035.linearIndependent_gen4_h3_8, CertificateChecks.Batch16035.linearIndependent_gen3_h1_9,
    CertificateChecks.Batch16035.linearIndependent_gen3_h3_10⟩

end Certificates
