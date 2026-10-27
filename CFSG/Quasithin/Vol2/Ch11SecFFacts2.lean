module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def FactSp4VL1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → ⁅fsuV T I, LOf L V₁⁆ ≤ V₃

@[expose] def FactSp4V3R1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → ⁅V₃, pCoreOf 2 (LOf L V₁)⁆ ≠ ⊥

@[expose] def FactSp4ZCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → ∀ P : Subgroup G, P ≤ ROf T L V₁ → ⁅V₃, P⁆ = ⊥ →
      ⁅P, LOf L V₁⁆ ≤ Subgroup.centralizer (fsuV T I : Set G)

end CFSG.Quasithin.Vol2.Ch11.SecF
