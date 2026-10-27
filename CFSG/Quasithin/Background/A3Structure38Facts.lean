
module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def A134Types (X : Type) [Group X] : Prop :=
  (∃ n, IsPSL 2 2 n X) ∨ (∃ n, IsSz n X) ∨ IsSporadic .J1 X ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e X)

@[expose] def A134TypesCentral (X : Type) [Group X] : Prop :=
  A134Types (X ⧸ Subgroup.center X)

@[expose] def A134Fact : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsQuasithin H → CFSG.SectionRank.IsKGroupCat H →
    ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
      Nonempty (↥L₁ ≃* ↥L₂) →
      (∀ L : Subgroup H, CFSG.IsComponent L → Nonempty (↥L ≃* ↥L₁) → L = L₁ ∨ L = L₂) ∧
      (A134TypesCentral ↥L₁ ∨ (IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3))

@[expose] def Mult2Fact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → A134TypesCentral X →
    IsPGroup 2 (Subgroup.center X)

@[expose] def OutSolvable (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, derivedSeries (MulAut X) n ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def SchreierFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → CFSG.SectionRank.IsKGroupCat X → OutSolvable X

structure A38Facts : Prop where
  a134 : A134Fact
  mult2 : Mult2Fact

abbrev A39Facts : Prop := SchreierFact

end CFSG.Quasithin
