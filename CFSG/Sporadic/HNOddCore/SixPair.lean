module

public import CFSG.Sporadic.HNOddCore.SixD
public import CFSG.Sporadic.SuzOddCore.CompQuot
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2092
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier

theorem cti_hn_six_pair_centralizer_component_simple_quotient_order
    (B : Subgroup (Subgroup.centralizer {t6J} : Subgroup JH)) (hB : CFSG.IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 44352000 := by
  rw [← card_Dr]
  have hker : Group.IsSolvable phi6.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact isSolvable_of_card_two card_ker_phi6
  exact CFSG.Sporadic.SuzOddCore.card_quotient_center_of_component phi6.rangeRestrict
    phi6.rangeRestrict_surjective hker Dr index_Dr Dr_simple Dr_noncomm hB

end CFSG.Sporadic.HNOddCore
