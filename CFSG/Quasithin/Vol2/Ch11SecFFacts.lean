module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def FactSp4CartanFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (X : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsCartanX T L X →
      ⁅fsuV T I, X⁆ = fsuV T I

@[expose] def FactSp4Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → ∀ P : Subgroup G, P ≤ ROf T L V₁ → ⁅V₃, P⁆ = ⊥ →
      ⁅fsuV T I, P⁆ ≤ V₁

@[expose] def FactSp4RadLine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 2 V₂ → IsVi T L I n 3 V₃ → ∀ P : Subgroup G, P ≤ ROf T L V₁ →
    ⁅fsuV T I, P⁆ ≤ Subgroup.centralizer (P : Set G) → ⁅V₃, P⁆ ≠ ⊥ →
      ∃ l ∈ LOf L V₁, fsuV T I ⊓ Subgroup.centralizer (P : Set G) = conjSubgroup V₂ l ∧
        ⁅fsuV T I, P⁆ = conjSubgroup V₂ l

@[expose] def FactSp4VL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₂ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 2 V₂ →
      ⁅fsuV T I, LOf L V₂⁆ = fsuV T I

@[expose] def FactSp4L2Rad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 2 V₂ → ∀ P : Subgroup G, P ≤ ROf T L V₁ →
    LOf L V₂ ≤ Subgroup.normalizer (P : Set G) → ⁅P, LOf L V₂⁆ = P → ⁅fsuV T I, P⁆ = ⊥

structure Sp4Facts : Prop where
  cartanFree : FactSp4CartanFree
  z : FactSp4Z
  radLine : FactSp4RadLine
  vL2 : FactSp4VL2
  l2Rad : FactSp4L2Rad

end CFSG.Quasithin.Vol2.Ch11.SecF
