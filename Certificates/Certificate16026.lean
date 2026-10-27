module

public import CFSG.Monster.AxisCount.BabySetupInputs
public import CFSG.Monster.AxisCount.BabyBalance
public import Certificates.Certificate8955

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Monster.B.TwoA (hE0)

public section


open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Monster.B.TwoA (hE0)

namespace CertificateChecks.Batch16026

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short
open CFSG.Monster.B.TwoA (hE0)

private theorem shapeOK_eq_true_0 : shapeOK = true := by
  decide +kernel

private theorem babyM_data_1 :
    ∀ t i : Fin 10,
      (∑ r : Fin (nrec i), sz i r * ((if tfin i r true = t then 1 else 0) +
        (if tfin i r false = t then 1 else 0))) = babyM t i := by
  decide +kernel

end CertificateChecks.Batch16026

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short in
open CFSG.Monster.B.TwoA (hE0) in
theorem certificate16026 : (
    shapeOK = true
  ) ∧ (
    ∀ t i : Fin 10,
      (∑ r : Fin (nrec i), sz i r * ((if tfin i r true = t then 1 else 0) +
        (if tfin i r false = t then 1 else 0))) = babyM t i
  ) := by
  exact ⟨CertificateChecks.Batch16026.shapeOK_eq_true_0, CertificateChecks.Batch16026.babyM_data_1⟩

end Certificates
