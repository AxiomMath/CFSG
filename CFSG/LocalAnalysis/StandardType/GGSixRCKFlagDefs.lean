module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open

@[expose] def FlagCentU {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (B : Option ((ι → F) → (ι → F) → F)) : Prop :=
  ∀ (R' : Subgroup U) (W H : Submodule F (ι → F)), W ≤ H →
    (∀ v ∈ R', v ≠ 1 →
      LinearMap.range (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = H) →
    (∀ b ∈ B, (∀ v ∈ R', ∀ m : ι → F, b m (((j v : Matrix ι ι F) - 1).mulVec m) = 0) ∨
      Module.finrank F W = 1) →
    ∀ r ∈ R', r ≠ 1 → pCoreOf 2 (Subgroup.centralizer ({r} : Set U)) ≤
      Subgroup.centralizer (R' : Set U)

@[expose] def FlagIrredW {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (B : Option ((ι → F) → (ι → F) → F)) : Prop :=
  ∀ (R' : Subgroup U) (W H : Submodule F (ι → F)), W ≤ H →
    (∀ v ∈ R', v ≠ 1 →
      LinearMap.range (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = H) →
    (∀ b ∈ B, (∀ v ∈ R', ∀ m : ι → F, b m (((j v : Matrix ι ι F) - 1).mulVec m) = 0) ∨
      Module.finrank F W = 1) →
    ∀ r ∈ R', r ≠ 1 → ∀ P : Submodule F (ι → F), P ≤ W →
      (∀ c ∈ Subgroup.centralizer ({r} : Set U), ∀ x ∈ P, (j c : Matrix ι ι F).mulVec x ∈ P) →
      P = ⊥ ∨ P = W

@[expose] def OddCenterOf {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (_ : U →* GL ι F) : Prop :=
  Odd (Nat.card (Subgroup.center U))

end CFSG.StandardType.RCKFlag
