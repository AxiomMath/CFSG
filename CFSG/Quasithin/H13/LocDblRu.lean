module

public import CFSG.Quasithin.H13.LocDblRuCheck
public import CFSG.Quasithin.H13.LocDblOvergroups
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.Ru.Native (ruData)

theorem sylowNoDouble_Ru_group :
    SylowNoDouble ↥(J ruData) :=
  sylowNoDouble_of_overgroups RuCert.ru_S_sylow RuCert.ru_sq RuCert.ru_over_dvd

theorem sylowNoDouble_Ru :
    SylowNoDouble (Carrier .Ru) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have h : SylowNoDouble CFSG.Blueprint.NativeSporadic.Ru :=
    SylowNoDouble.of_mulEquiv (A := ↥(J ruData)) (A' := CFSG.Blueprint.NativeSporadic.Ru)
      (seedEquiv hF.toBaseFacts).symm sylowNoDouble_Ru_group
  exact h

end CFSG.Quasithin.H13.LocDbl
