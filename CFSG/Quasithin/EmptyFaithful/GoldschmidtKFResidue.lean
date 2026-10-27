module

public import CFSG.Quasithin.EmptyFaithful.SBd18Out
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.Quasithin

@[expose] def Input15338Rank1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L₁ B : Subgroup Y), CFSG.IsQuasisimple ↥L₁ →
    A23List (↥L₁ ⧸ Subgroup.center ↥L₁) → CFSG.Open.pRank 3 L₁ = 1 →
    B ≤ Subgroup.normalizer (L₁ : Set Y) → IsPOnePlusTwo 3 ↥B →
    3 ≤ CFSG.Open.pRank 3 (L₁ ⊔ B)

@[expose] def Input15338CenterRank : Prop :=
  ∀ (C : Type) [Group C] [Finite C], CFSG.IsQuasisimple C → SQTKGroup C →
    ∀ F : Subgroup C, F ≤ Subgroup.center C → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 3

@[expose] def Input15338Ident : Prop :=
  ∀ (L₂ : Type) [Group L₂] [Finite L₂], CFSG.IsQuasisimple L₂ →
    A23List (L₂ ⧸ Subgroup.center L₂) → CFSG.Open.pRank 3 (⊤ : Subgroup L₂) = 2 →
    ∀ v : MulAut L₂, v * v = 1 →
      (∃ Lf : Subgroup L₂, Lf ∈ cComp (SBd18.fixedSub v) ∧ CFSG.IsQuasisimple ↥Lf ∧
        Subgroup.center ↥Lf = ⊥ ∧ IsPSL 3 2 1 (↥Lf ⧸ Subgroup.center ↥Lf)) →
      IsPSL 3 2 2 (L₂ ⧸ Subgroup.center L₂) ∨ IsSporadic .J2 (L₂ ⧸ Subgroup.center L₂) ∨
        IsPSL 3 7 1 (L₂ ⧸ Subgroup.center L₂)

@[expose] def Input15338NonsolvJ : Prop :=
  ∀ (L₂ : Type) [Group L₂] [Finite L₂], CFSG.IsQuasisimple L₂ →
    (IsSporadic .J2 (L₂ ⧸ Subgroup.center L₂) ∨ IsPSL 3 7 1 (L₂ ⧸ Subgroup.center L₂)) →
    ∀ u : MulAut L₂, u * u = 1 → ¬ Group.IsSolvable ↥(SBd18.fixedSub u)

@[expose] def Input15338FinalL34 : Prop :=
  ∀ (L₂ : Type) [Group L₂] [Finite L₂], CFSG.IsQuasisimple L₂ →
    IsPSL 3 2 2 (L₂ ⧸ Subgroup.center L₂) →
    ∀ U : Subgroup (MulAut L₂), Nat.card U = 4 → CFSG.Assembly.IsElemAbelian 2 U →
      (∃ y ∈ Subgroup.normalizer (U : Set (MulAut L₂)), orderOf y = 3 ∧
        ∃ u ∈ U, y * u * y⁻¹ ≠ u) →
      ∀ u ∈ U, u ≠ 1 → ∀ M : Subgroup L₂, M ≤ SBd18.fixedSub u → IsPGroup 3 ↥M →
        (M.subgroupOf (SBd18.fixedSub u)).Normal →
        ∀ x : MulAut L₂, orderOf x = 3 → (∀ w ∈ U, x * w = w * x) →
          (∀ d ∈ SBd18.fixedSub u, x d * d⁻¹ ∈ M) → False

end CFSG.Quasithin.SBd19F
