module

public import CFSG.LocalAnalysis.StandardType.GGResJOneReflSylow
public import CFSG.LocalAnalysis.StandardType.GGResJOneReflLabelTwE6
import CFSG.LocalAnalysis.StandardType.GGResJOneReflLabelCfg
import CFSG.LocalAnalysis.StandardType.GGResJOneReflLabelNine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Certificates


theorem ggResJOneReflLabelInput_holds : GGResJOneReflLabelInput := by
  intro p _ hp2 lab hlab hS
  have hp : p.Prime := Fact.out
  by_cases hcfg : CFSG.LocalAnalysis.GLTheoremA.K155X.L154OutdiagCfg p lab
  · obtain ⟨rfl, h⟩ := ggResJOneReflLabel_cfg hp hp2 hlab hS hcfg
    have hnc : LargeEvenLabelAll lab fun R _ _ _ =>
        ∃ F : Subgroup R, IsPGroup 3 F ∧ ¬ IsCyclic F := by
      obtain ⟨t, l, n⟩ := lab
      rcases h with ⟨ht, hl, h3⟩ | ⟨ht, hl, h3⟩ | ⟨ht, h3⟩ <;> dsimp only at ht <;> subst ht
      · dsimp only at hl
        subst hl
        exact largeEvenLabelAll_noncyclic_three_A2 h3
      · exact largeEvenLabelAll_noncyclic_three_twA hlab hl h3
      · exact largeEvenLabelAll_noncyclic_three_twE6 hlab.1 h3
    exact hnc.mono fun _ _ _ _ h _ _ _ _ _ _ => h
  · exact (CFSG.LocalAnalysis.GLTheoremA.K155X.l154_outdiagPrime_legacy hp hp2 hlab hcfg).mono
      fun _ _ _ _ h hs hna E hEI hE hcard =>
        exists_noncyclic_of_outdiagPrime (@center_eq_bot_of_simple_nonabelian _ _ hs hna)
          (h hs hna) E hEI hE hcard

theorem ggResJOneReflInput_holds : GGResJOneReflInput :=
  ggResJOneReflInput_of_labelInput ggResJOneReflLabelInput_holds

end Certificates

end CFSG.StandardType

end
