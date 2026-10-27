module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3Check
import Certificates.Kernel.Sporadic.OddCore.J3PGGlue

namespace CertificateChecks.Batch129006

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.OddCore.J3W
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem hc : canonK 6156 13 (mask 13) (6156 * 13) Y129006 = true :=
  canonK_pcomp cn.2.1 (canonK_pcomp cn.2.2.2.1 (canonK_pcomp cn.2.1
    (canonK_pcomp cn.2.2.2.1 cn.2.2.2.1)))

theorem y_eq : j3OuterWitTbl () = tabT (unpack 6156 13 Y129006) := by
  simp only [j3OuterWitTbl]
  rw [t_eq, pg_eq (l := 1) (by norm_num), compT_unpack cn.2.2.2.1 cn.2.2.2.1,
    compT_unpack cn.2.1 (canonK_pcomp cn.2.2.2.1 cn.2.2.2.1),
    compT_unpack cn.2.2.2.1 (canonK_pcomp cn.2.1 (canonK_pcomp cn.2.2.2.1 cn.2.2.2.1)),
    compT_unpack cn.2.1
      (canonK_pcomp cn.2.2.2.1 (canonK_pcomp cn.2.1 (canonK_pcomp cn.2.2.2.1 cn.2.2.2.1)))]
  rfl

theorem holds : j3OuterWitCheck () = true := by
  have h := ord129006
  simp only [bAnd_iff] at h
  obtain ⟨h19, h1⟩ := h
  have h1' : Nat.beq Y129006 (pidn 6156 13) = false := not_of_bIf h1
  simp only [j3OuterWitCheck]
  rw [perm_t, y_eq, powT_unpack (pows _) idT_eq cn.2.2.2.2 hc 19, idT_eq,
    tblEq_unpack (pows_canon (pows _) cn.2.2.2.2 hc 19) cn.2.2.2.2,
    tblEq_unpack hc cn.2.2.2.2, h19, h1']
  rfl

end CertificateChecks.Batch129006

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129006 : j3OuterWitCheck () = true :=
  CertificateChecks.Batch129006.holds

end Certificates
