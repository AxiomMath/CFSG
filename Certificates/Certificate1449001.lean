module

public import CFSG.ClassicalGroups.Symplectic.PSp45.PresData
import Certificates.Kernel.PSp45.Tables
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CertificateChecks.Batch1449001

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ClassicalGroups.Symplectic.PSp45
  CFSG.ClassicalInvolution.Phan.Q3G

theorem card_le : Finite (PG 8 pspRels) ∧ Nat.card (PG 8 pspRels) ≤ 936 * 5000 :=
  TableFact.card_restrict pspRels (by norm_num) (subsetOf 8 [0, 1, 2, 3, 4, 5]) (by decide)
    CFSG.KBFact.PSI CFSG.KBFact.PSB

end CertificateChecks.Batch1449001

namespace Certificates

open CertificateChecks

open CFSG.CosetTable in
theorem certificate1449001 : Finite (PG 8 CFSG.ClassicalGroups.Symplectic.PSp45.pspRels) ∧
    Nat.card (PG 8 CFSG.ClassicalGroups.Symplectic.PSp45.pspRels) ≤ 4680000 :=
  ⟨CertificateChecks.Batch1449001.card_le.1, CertificateChecks.Batch1449001.card_le.2.trans (by norm_num)⟩

end Certificates
