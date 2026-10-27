module

public import CFSG.Quasithin.H13.A5S136h
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

namespace CFSG.Quasithin.H13.A5

theorem notQS1367_holds :
    NotQS1367 := by
  intro X _ hq F _ _ hF
  exact ⟨fun ⟨e⟩ => CFSG.Quasithin.R3c2.not_isQuasisimple_statedSp_two hF e hq,
    fun ⟨e⟩ => CFSG.Quasithin.R3c2.not_isQuasisimple_quasithinG2_two hF e hq⟩

end CFSG.Quasithin.H13.A5
