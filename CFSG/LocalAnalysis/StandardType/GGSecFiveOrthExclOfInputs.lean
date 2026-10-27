module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCaseA3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCaseA4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCaseA5
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCaseD4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti CFSG.StandardType.OrthF3

theorem ggSecFiveOrthExclInput_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input) (hRQ : GGReflRealizedQFourNbrInput)
    (hTBJ : GGSecFiveTBJTypeD4Input) (hKSL : GGSecFiveOrthKSLInput)
    (hD4 : GGSecFiveOrthD4ExclInput) : GGSecFiveOrthExclInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit hC hp3 V _ _ Q hQ _ ι hd hA
  subst hp3
  by_cases hplus : Module.finrank (ZMod 3) V = 4 ∧ ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0
  · exact ggWeylReflectionGroup_of_orth_plus Q hQ rfl hplus.1 hplus.2 ι _ hA
  · exfalso
    have S : GGOrthSetup B Bs x L D J 𝒦 Q ι := ⟨hcfg, hsplit, hC, hQ, hd, hA⟩
    rcases S.typeAL hFix with ⟨hd4, hA3⟩ | ⟨hd5, hA4, -, hx, hQx⟩ | ⟨hd5, hA5⟩ | ⟨hd5, hD, hpres⟩
    · exact ggOrth_caseA3 S hL hP hPump hFix hJA2 hd4 (fun h => hplus ⟨hd4, h⟩) hA3
    · exact ggOrth_caseA4 S hFix hd5 hA4 hx hQx
    · exact ggOrth_caseA5 S hL hP hPump hFix hd5 hA5
    · exact ggOrth_caseD4 S hL hP hPump hFix hRQ hTBJ hKSL hD4 hd5 hD hpres

end CFSG.StandardType

end
