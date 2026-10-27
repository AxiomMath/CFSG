module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_28_r (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L → ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V

@[expose] def R16_28_m (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L → MBarGT D.M V₀ V 1

theorem sixteen_twentyEight_of (D : Data G) (hr : R16_28_r D) (hm : R16_28_m D) : R16_28 D := by
  intro V₀ V L hV hS h8
  refine ⟨hr V₀ V L hV hS h8, ?_⟩
  have h := succ_le_deltaInf_of_mBarGT D hS.setting.hyp16.hyp125 (hm V₀ V L hV hS h8)
  exact lt_of_lt_of_le (by norm_num) h

@[expose] def R16_58_r (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_7 D V₀ V hV L → ((mSub V₀ + 3 : ℕ) : ℕ∞) ≤ rMV D.M V

@[expose] def R16_58_m (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_7 D V₀ V hV L → MBarGT D.M V₀ V 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
