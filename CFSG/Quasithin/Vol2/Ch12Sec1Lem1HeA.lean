module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.KGFactH91B
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

@[expose] def HeInspCfg (X : Type) [Group X] (m : ℕ) : Prop :=
  ∃ (Y W₁ W₂ : Subgroup X) (C₁ : KGH91.NatCoord Y W₁ m) (C₂ : KGH91.NatCoord Y W₂ m)
    (τ : MulAut X), W₁ ⊔ W₂ ≤ Y ∧ W₁ ⊓ W₂ = ⊥ ∧ IsElemAbelian 2 (W₁ ⊔ W₂) ∧
    IsPGroup 2 C₁.ρ.ker ∧ (∀ y, C₂.ρ y = slGraphAut m (ZMod 2) (C₁.ρ y)) ∧
    Y.map τ.toMonoidHom = Y ∧ (∀ w ∈ W₁, τ w ∈ W₂) ∧
    (m = 3 → ∃ R : Subgroup X, IsSylowTwoOf R ⊤ ∧ R ≤ Subgroup.normalizer (Y : Set X))

@[expose] def TwoRankLtSix (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E < 2 ^ 6

@[expose] def TwoRankLtEight (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E < 2 ^ 8

@[expose] def HeInspRankAlt : Prop :=
  (∀ n : ℕ, 5 ≤ n → n ≤ 8 → TwoRankLtSix (alternatingGroup (Fin n))) ∧
    ∀ (X : Type) [Group X] [Finite X],
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 4 2 1 → TwoRankLtSix X

@[expose] def HeInspRankOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p f) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 p 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 p 1) → TwoRankLtSix X

@[expose] def HeInspRankSpor : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨
    s = .HS) → TwoRankLtSix (NativeSporadic.Carrier s)

@[expose] def HeInspRankEight : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1 → TwoRankLtEight X) ∧
    TwoRankLtEight (NativeSporadic.Carrier .M24) ∧ TwoRankLtEight (NativeSporadic.Carrier .He) ∧
    TwoRankLtEight (NativeSporadic.Carrier .Ru)

@[expose] def HeInspE64 : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1 → ¬ HeInspCfg X 3) ∧
    ¬ HeInspCfg (NativeSporadic.Carrier .M24) 3 ∧ ¬ HeInspCfg (NativeSporadic.Carrier .He) 3

@[expose] def HeInspRu : Prop := ¬ HeInspCfg (NativeSporadic.Carrier .Ru) 3

@[expose] def HeInspJ4 : Prop :=
  ¬ HeInspCfg (NativeSporadic.Carrier .J4) 3 ∧ ¬ HeInspCfg (NativeSporadic.Carrier .J4) 4

end CFSG.Quasithin.H13
