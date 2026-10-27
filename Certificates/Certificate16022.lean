
module

public import Certificates.Certificate16022Base
import all Certificates.Certificate16022Base


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA.Census

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16022

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA.Census

end CertificateChecks.Batch16022

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA.Census in
theorem certificate16022 : (
    supp ((dC : C) : Fin 24 → ZMod 2) = Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8
  ) ∧ (
    (genRecord 12).kind = .codeSign
  ) ∧ (
    (genRecord 12).word = [4, 3]
  ) ∧ (
    (genRecord 23).kind = .xiSign
  ) ∧ (
    (genRecord 23).word = [0, 3]
  ) ∧ (
    ∀ k < 9, PermArr fPerms[k]! = true
  ) ∧ (
    ∀ k < 9, AutArr fPerms[k]!
  ) ∧ (
    ∀ k < 9, (fPerms[k]!)[0]! = 0 ∧ (fPerms[k]!)[1]! = 1 ∨
      (fPerms[k]!)[0]! = 1 ∧ (fPerms[k]!)[1]! = 0
  ) ∧ (
    ∀ k < 9, ∀ i < 24, (i < 8 ↔ (fPerms[k]!)[i]! < 8)
  ) ∧ (
    ∀ k < 9, permRowsOK fPerms[k]! fRows24[k]! = true
  ) ∧ (
    ∀ k < 9, quotRowsOK fRows24[k]! fRows22[k]! = true
  ) := by
  exact ⟨CertificateChecks.Batch16022.supp_dC_0, CertificateChecks.Batch16022.kind_twelve_1, CertificateChecks.Batch16022.word_twelve_2,
    CertificateChecks.Batch16022.kind_twentythree_3, CertificateChecks.Batch16022.word_twentythree_4, CertificateChecks.Batch16022.fPerms_PermArr_5,
    CertificateChecks.Batch16022.fPerms_AutArr_6, CertificateChecks.Batch16022.fPerms_fix01_7, CertificateChecks.Batch16022.fPerms_octad_8,
    CertificateChecks.Batch16022.fRows24_ok_9, CertificateChecks.Batch16022.fRows22_ok_10⟩

end Certificates
