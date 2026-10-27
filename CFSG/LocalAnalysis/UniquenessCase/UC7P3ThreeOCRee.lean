module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.RankOne
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowRee

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

open CFSG.RankThree.PartOne.Census3 (IsoLie)



theorem good_of_isoLie_reeG2 {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 3 X = ⊥)
    {N : Subgroup X} (hN : IsStronglyPEmbedded 3 N) {m : ℕ}
    (hI : IsoLie ↥(CFSG.generalizedFitting X) (.reeG2 m)) : SEFive.Good 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hv, ⟨e⟩⟩ := hI
  have hd : IsReeGTwoIndex 3 ⟨.reeG2 m, hv⟩ := ⟨rfl, m, rfl⟩
  refine SEFive.good_of_rankOne hO hN (kFactReeBorelMaximal _ _ hd ⟨e⟩) (fun T => ?_)
    (fun T α hα => kFactReeCenterCentralizer _ _ hd ⟨e⟩ T α fun z hz => hα z hz.1)
  obtain ⟨hT, hcount⟩ := KFactProofs.OneLieSylow.card_sylow_ree hd ⟨e⟩ T
  rw [hcount, hT]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
