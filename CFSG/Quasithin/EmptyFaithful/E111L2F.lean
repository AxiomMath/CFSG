module

public import CFSG.Quasithin.EmptyFaithful.E111L2OB
public import CFSG.Quasithin.EmptyFaithful.E111L2II

public section

namespace CFSG.Quasithin.E2.E22N.E111L

theorem e111CoreMultiL2_holds : E111CoreMultiL2 :=
  e111CoreMultiL2_of (fun _ hp hp8 => kleinMemberInner_holds hp hp8)
    fun _ hp hp8 => kleinMemberOuter_holds hp hp8

end CFSG.Quasithin.E2.E22N.E111L
