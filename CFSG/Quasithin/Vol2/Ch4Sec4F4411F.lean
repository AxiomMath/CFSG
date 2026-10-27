module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411C
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411E

public section

namespace CFSG.Quasithin.H13.Ch4.E443


theorem fact4411_holds : Fact4411 := by
  intro K _ _ hK hL
  rcases hL with ⟨n, h⟩ | ⟨n, h⟩ | h | ⟨p, e, hp, hp3, he, -, h⟩ | h
  · exact F4411.perfCentral_of_isPSL_two hK h
  · exact F4411.perfCentral_of_isSz hK h
  · exact F4411.perfCentral_of_isJ1 hK h
  · exact F4411.perfCentral_of_isPSL_odd hK hp hp3 he h
  · exact F4411.perfCentral_of_isSU3 h

end CFSG.Quasithin.H13.Ch4.E443
