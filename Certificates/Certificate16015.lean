module

public import CFSG.Monster.B.TwoA.Amalgam.Flag2PlaneInputs
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Amalgam.DataBase

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.Monster.B.TwoA.Unitary.LinThree
open scoped Pointwise

namespace CertificateChecks.Batch16015

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.Monster.B.TwoA.Unitary.LinThree
open scoped Pointwise

private theorem genPt_eq_0 : ∀ (k : Fin 6) (i : Fin 21), genPt k i =
    normIdx (CFSG.Monster.B.Classical.ThreePlane.pairVec (genMat k) (genFrob k) (Ω i)) := by
  decide +kernel

private theorem genLn_spec_1 : ∀ (k : Fin 6) (b : Fin 21),
    (projLine b).image (genPt k) = projLine (genLn k b) := by
  decide +kernel

private theorem flagCert_spec_2 : ∀ i b : Fin 21, i ∈ projLine b →
    ∃ e ∈ flagCert, e.1 = i ∧ e.2.1 = b ∧ e.2.2.foldr genPt 5 = i ∧ e.2.2.foldr genLn 0 = b := by
  decide +kernel

end CertificateChecks.Batch16015

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.Monster.B.TwoA.Unitary.LinThree in
open scoped Pointwise in
theorem certificate16015 : (
    ∀ (k : Fin 6) (i : Fin 21), genPt k i =
    normIdx (CFSG.Monster.B.Classical.ThreePlane.pairVec (genMat k) (genFrob k) (Ω i))
  ) ∧ (
    ∀ (k : Fin 6) (b : Fin 21),
    (projLine b).image (genPt k) = projLine (genLn k b)
  ) ∧ (
    ∀ i b : Fin 21, i ∈ projLine b →
    ∃ e ∈ flagCert, e.1 = i ∧ e.2.1 = b ∧ e.2.2.foldr genPt 5 = i ∧ e.2.2.foldr genLn 0 = b
  ) := by
  exact ⟨CertificateChecks.Batch16015.genPt_eq_0, CertificateChecks.Batch16015.genLn_spec_1, CertificateChecks.Batch16015.flagCert_spec_2⟩

end Certificates
