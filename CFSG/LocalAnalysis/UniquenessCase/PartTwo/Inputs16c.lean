module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_3 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L → Concl163 D V₀ V hV L

@[expose] def R16_4 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    Conc4_136 D V₀ V hV L → 1 < s15 D.M V₀ V hV L → Concl164 D V₀ V hV L

@[expose] def R16_5 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L → IsOmegaPlus ↥(lBar V₀ V hV L) 4 3 →
      D.sig = {3} ∧ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)

@[expose] def R16_7 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L →
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧ barSub V₀ V hV L' ≠ ⊥ ∧
      Conc4_136 D V₀ V hV L' ∧ Concl167 D V₀ V hV L'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
