
module

public import Certificates.Certificate16028Base
import all Certificates.Certificate16028Base


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.VisCert CFSG.Monster.B.Co2

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.VisCert CFSG.Monster.B.Co2

namespace CertificateChecks.Batch16028

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.VisCert CFSG.Monster.B.Co2

end CertificateChecks.Batch16028

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.VisCert CFSG.Monster.B.Co2 in
theorem certificate16028 : (
    rowCheck (pairN (2 : Fin 24) (4 : Fin 24)) 81920 = true
  ) ∧ (
    rowCheck (pairN (2 : Fin 24) (5 : Fin 24)) 147456 = true
  ) ∧ (
    rowCheck (pairN (2 : Fin 24) (6 : Fin 24)) 278528 = true
  ) ∧ (
    (fun k : Fin 24 => if P ((dC : C) : Fin 24 → ZMod 2) = 0 then
      2 * bitLift (((dC : C) : Fin 24 → ZMod 2) k) else
      2 * (1 - bitLift (((dC : C) : Fin 24 → ZMod 2) k))) = fun k : Fin 24 => twoD k
  ) := by
  exact ⟨CertificateChecks.Batch16028.pairW24_eq_decW_0, CertificateChecks.Batch16028.pairW25_eq_decW_1,
    CertificateChecks.Batch16028.pairW26_eq_decW_2, CertificateChecks.Batch16028.lamX_form_eq_3⟩

end Certificates
