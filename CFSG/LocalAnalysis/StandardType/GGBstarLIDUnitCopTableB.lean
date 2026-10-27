module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitCopField
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGUnitCopFieldLabel.toUnitaryCoprime {p : ℕ} {lab : LargeEvenLabel}
    (h : GGUnitCopFieldLabel p lab) : GGUnitaryCoprimeLabel p lab :=
  Or.inl h.unitaryCoprime

section TableB


theorem ggTableBIrredInputOn_unitCopField : GGTableBIrredInputOn GGUnitCopFieldLabel :=
  ggTableBIrredInputOn_unitary.mono fun _ _ h => h.toUnitaryCoprime

theorem ggTableBCxInputOn_unitCopField_holds : GGTableBCxInputOn GGUnitCopFieldLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_unitCopField_holds
    ggTableBIrredInputOn_unitCopField

theorem ggTableBModuleInputOn_unitCopField_holds : GGTableBModuleInputOn GGUnitCopFieldLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_unitCopField_holds
    ggTableBIrredInputOn_unitCopField

theorem ggTableBActionInputOn_unitCopField_holds : GGTableBActionInputOn GGUnitCopFieldLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_unitCopField_holds
    ggTableBIrredInputOn_unitCopField

theorem ggTableBCxInputOn_of_not_unitCopField {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGUnitCopFieldLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_unitCopField_holds.or h).mono fun p lab hS => by
    by_cases h1 : GGUnitCopFieldLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hS, h1⟩

theorem ggTableBModuleInputOn_of_not_unitCopField {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGUnitCopFieldLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_unitCopField_holds.or h).mono fun p lab hS => by
    by_cases h1 : GGUnitCopFieldLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hS, h1⟩

theorem ggTableBActionInputOn_of_not_unitCopField {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGUnitCopFieldLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_unitCopField_holds.or h).mono fun p lab hS => by
    by_cases h1 : GGUnitCopFieldLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hS, h1⟩

end TableB

end CFSG.StandardType
