module

public import CFSG.RankThree.PartOne.K159.AutTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Sporadic.Schreier.Tits

theorem autWitness_of_isoLie_tits
    {S : Type} [Group S] (h : IsoLie S .tits) : AutWitness 5 S := by
  obtain ⟨e⟩ := titsModelEquiv S 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits h)
  exact AutWitness.of_mulEquiv e.symm autWitness_titsD

end CFSG.RankThree.PartOne.K159
