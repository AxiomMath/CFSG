module

public import CFSG.Sporadic.HNOddCore.AlmostSimple
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.FischerOddCore

theorem center_bot_of_mulEquiv_sub {G G0 : Type*} [Group G] [Group G0] {J : Subgroup G0}
    (e : G ≃* J) (h : Subgroup.center J = ⊥) : Subgroup.center G = ⊥ :=
  center_eq_bot_of_mulEquiv e h

theorem ctuc_hn_generalized_fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (_hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.HN)) :
    ((CFSG.generalizedFitting X).index = 1 ∨ (CFSG.generalizedFitting X).index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hZ : Subgroup.center (CFSG.generalizedFitting X) = ⊥ :=
    center_bot_of_mulEquiv_sub (hJ.some.trans hnEquivJ) center_JH
  exact ctuc_hn_almost_simple_involution_centralizer_odd_core_trivial _ hJ
    (centralizer_generalizedFitting_eq_bot_of_center hZ)

end CFSG.Sporadic.HNOddCore
