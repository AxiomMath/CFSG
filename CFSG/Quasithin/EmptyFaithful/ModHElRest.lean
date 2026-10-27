module

public import CFSG.Quasithin.EmptyFaithful.ModHTop
public import CFSG.Quasithin.EmptyFaithful.ModHJ2
public import CFSG.Quasithin.EmptyFaithful.ModHJ4El
public import CFSG.Quasithin.EmptyFaithful.ModHHSEl
public import CFSG.Quasithin.EmptyFaithful.ModHRuEl
public import CFSG.Quasithin.EmptyFaithful.ModHHeEl

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.R3c14

theorem not_elConfig_j2 (hJ : SylowFactsJ2) :
    ¬ ElConfig (NativeSporadic.Carrier .J2) := by
  have : Finite (NativeSporadic.Carrier .J2) := (CFSG.Sporadic.J2.fam_j2_simplicity).1
  exact not_elConfig_of_center hJ.2 hJ.1

theorem noElConfigRest_of_J2He
    (hJ2 : SylowFactsJ2) (hHe : FactHeCentralizer) : NoElConfigRest :=
  ⟨not_elConfig_j2 hJ2, J4El.not_elConfig_j4, HSEl.not_elConfig_hs, HeEl.not_elConfig_he hHe,
    RuEl.not_elConfig_ru⟩

end CFSG.Quasithin.ModH
