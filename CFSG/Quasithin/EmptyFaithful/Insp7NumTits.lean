module


import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.Insp7NumA
public import CFSG.Quasithin.EmptyFaithful.Insp7NumB

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace Insp7

theorem numFactAt_tits
    : NumFactAt (fun L _ => ReeTitsModel L .Tits 2 1) := by
  refine numFactAt_of_big (fun L _ _ hq hmodel => ?_)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1 hmodel
  have hs := (CFSG.LieType.Simplicity.fam_tits_simplicity L 2 1 hmodel).2
  have hcard : Nat.card L = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact bigDvd_of_simple hq hs (by rw [hcard]; norm_num)

end Insp7

end CFSG.Quasithin
