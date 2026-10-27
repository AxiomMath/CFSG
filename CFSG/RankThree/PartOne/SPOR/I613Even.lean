module

public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem evenLieType_of_seitzBridge (hS : CTP.SeitzBridge) {X : Type} [Group X]
    {d : TauCeti.LieTypeIndex} (h : IsoLie X d) (hd : d.characteristic = 2) :
    CFSG.Blueprint.EvenLieType X := by
  obtain ⟨t, n, r, f, hadm, hmodel, hr, -, -⟩ := hS X d h
  obtain rfl : r = 2 := hr.trans hd
  exact ⟨t, n, f, hadm, hmodel⟩

theorem evenExceptionalBridge_of_seitzBridge (hS : CTP.SeitzBridge) : EvenExceptionalBridge := by
  intro X _ _ h
  rcases h with ⟨q, hq, hG | hT⟩ | ⟨m, hR⟩ | hT | ⟨q, hq, -, hF⟩
  · exact evenLieType_of_seitzBridge hS hG (by simpa using hq)
  · exact evenLieType_of_seitzBridge hS hT (by simpa using hq)
  · exact evenLieType_of_seitzBridge hS hR (by simp)
  · exact evenLieType_of_seitzBridge hS hT (by simp)
  · exact evenLieType_of_seitzBridge hS hF (by simpa using hq)

theorem evenExceptionalBridge_holds :
    EvenExceptionalBridge :=
  evenExceptionalBridge_of_seitzBridge CTP.seitzBridge

end CFSG.RankThree.PartOne.SPOR
