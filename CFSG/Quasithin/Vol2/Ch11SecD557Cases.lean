module

public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Stmt11_5_7SL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KindSL3 L (fsuV T I) n →
      IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

@[expose] def Stmt11_5_7Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KindSp4 L (fsuV T I) n →
      IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

theorem stmt11_5_7_of_cases (h1151 : Stmt11_5_1) (hSL3 : Stmt11_5_7SL3)
    (hSp4 : Stmt11_5_7Sp4) : Stmt11_5_7 := by
  intro G _ _ T L I n V₁ h hV₁
  rcases h1151 G T L I n h with hk | hk
  · exact hSL3 G T L I n V₁ h hV₁ hk
  · exact hSp4 G T L I n V₁ h hV₁ hk

end CFSG.Quasithin.Vol2.Ch11.SecD
