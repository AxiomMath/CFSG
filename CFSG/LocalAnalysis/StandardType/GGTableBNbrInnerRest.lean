module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestSC
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac
public import CFSG.LocalAnalysis.StandardType.GGAssemblySixDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBNbrInnerRound9Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound6Label p lab ∧ ¬ GGUnitaryCoprimeLabel p lab ∧
    ¬ GGSpNonsplitLabel p lab ∧ ¬ GGTableBNbrInnerExcSplitLabel p lab ∧
    ¬ GGTableBNbrInnerVacLabel p lab

section Round9


theorem ggTableBNbrInnerInputOn_round6_of_round9
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound9Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label :=
  ((((ggTableBNbrInnerInputOn_unitary.or ggTableBNbrInnerInputOn_spNonsplit).or
      ggTableBNbrInnerInputOn_excSplit).or ggTableBNbrInnerInputOn_vac).or h).mono
    fun p lab h6 => by
      by_cases h1 : GGUnitaryCoprimeLabel p lab
      · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
      · by_cases h2 : GGSpNonsplitLabel p lab
        · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
        · by_cases h3 : GGTableBNbrInnerExcSplitLabel p lab
          · exact Or.inl (Or.inl (Or.inr h3))
          · by_cases h4 : GGTableBNbrInnerVacLabel p lab
            · exact Or.inl (Or.inr h4)
            · exact Or.inr ⟨h6, h1, h2, h3, h4⟩

theorem ggTableBNbrInnerInput_of_round9
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound9Label) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_round6 (ggTableBNbrInnerInputOn_round6_of_round9 h)

end Round9

theorem ggTableBNbrInnerInputOn_round9_of_round6
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound9Label :=
  h.mono fun _ _ h9 => h9.1

end CFSG.StandardType

end
