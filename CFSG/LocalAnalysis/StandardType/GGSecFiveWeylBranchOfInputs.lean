module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFourLeRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarInput
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCR3OfPump
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchOrth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchCR
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs
import CFSG.LocalAnalysis.StandardType.GGZSMonWit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveWeylBranchInput_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hPump : GGSecFivePumpReadInput) (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput) (hJr : GGSecFiveJrInput) (hCR : GGSecFiveCRInput)
    (hCR3 : GGSecFiveCR3Input) (hOrth : GGSecFiveOrthExclInput) :
    GGSecFiveWeylBranchInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit hC
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs_ea, hxBs, hLx, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs_ea
  obtain ⟨U, Abar, ρ, hD⟩ :=
    ggSecFiveBarInput_holds hL hP hPump hFix hJA2 G p B Bs x L D J 𝒦 hcfg hsplit hC V ι
  have h3 : 3 ≤ Module.finrank (ZMod p) U := hD.1
  have hRG : ZS.ReflGen p Abar := hD.2.1
  have hAI : ZS.AbsIrred p Abar := hD.2.2.1
  have : Finite V := Finite.of_injective (ι.symm : V → Additive ↥Bs) ι.symm.injective
  have : Finite ↥U := Finite.of_injective (Subtype.val : ↥U → V) Subtype.val_injective
  have : Module.Finite (ZMod p) U := Module.Finite.of_finite
  have hFam : ZS.Family p Abar := hUse p U Abar hp2 h3 hRG hAI
  rcases hWit p U Abar hp2 h3 hRG hAI hFam with hW | hM | hN | hO | hC'
  · exact ggSecFive_weyl_of_linWeyl hD hW
  · exact (ggSecFive_not_cr_branch hJA2 hJr hCR hCR3 hD hcfg hsplit fun r hr hrefl =>
      Or.inr (ZS.witL51_of_witMON hp2 hRG hAI hM hr hrefl)).elim
  · exact absurd hN (ggSecFive_not_witNEG3 hD (ggSecFive_four_le_finrank hconf ι))
  · exact ggSecFive_weyl_of_witORTH hOrth hD hcfg hsplit hC hO
  · exact absurd hC' (ggSecFive_not_cr_branch hJA2 hJr hCR hCR3 hD hcfg hsplit)

end CFSG.StandardType

end
