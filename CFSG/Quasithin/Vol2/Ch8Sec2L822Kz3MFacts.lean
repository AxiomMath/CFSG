module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3MFactsA
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3MFactsB
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3MFactsC

public section

namespace CFSG.Quasithin.H13

theorem kzM22Cover17280_kz3_proved :
    KzM22Cover17280_kz3 :=
  kzM22Cover17280_kz3_of kzM22Sub5760_kz3_proved

theorem kz3_facts_proved :
    KzM22Sub5760_kz3 ∧ KzM22Cover17280_kz3 ∧ KzCodeHexad5760_kz3 :=
  ⟨kzM22Sub5760_kz3_proved, kzM22Cover17280_kz3_proved, kzCodeHexad5760_kz3_proved⟩

end CFSG.Quasithin.H13
