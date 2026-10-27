module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp193 (D : Data G) (V₀ : Subgroup G) (p : ℕ) (X : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  isPGroup : IsPGroup p X
  noncyclic : ¬ IsCyclic X
  exponent : ∀ x ∈ X, x ^ p = 1
  inf_eq_bot : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥
  uniqueMax : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → UniqueMax D.M Y
  perm : (X : Set G) * (D.T : Set G) = (D.T : Set G) * (X : Set G)
  le_M : X ⊔ D.T ≤ D.M
  fstar : Fstar (X ⊔ D.T) = pCoreOf 2 (X ⊔ D.T)

@[expose] def Concl193 (D : Data G) (V : Subgroup G) : Prop :=
  normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
    normalizer (omegaOneCenterOf (E3.wClos V 1 D.T) : Set G) ≤ D.M

@[expose] def Z193 (D : Data G) (V : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (E3.wClos V 1 D.T)

structure MinCex193 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (X : Subgroup G) : Prop where
  setting : WeakClosureSetting D V₀ V
  ne_bot : V₀ ≠ ⊥
  mbar : MBarGT D.M V₀ V 2
  gamma : rankThreeGamma 1 2 (centerOf D.T) ≤ D.M
  hyp : Hyp193 D V₀ p X
  fail : ¬ Concl193 D V
  cyclic : ∀ L : Subgroup G, D.T ≤ L → L < X ⊔ D.T →
    ∀ P : Subgroup G, P ≤ L → IsPGroup p P → IsCyclic P

@[expose] def K0193 (D : Data G) (X A K : Subgroup G) : Subgroup G :=
  (⨆ k ∈ K, conjSubgroup A k) ⊔ pCoreOf 2 (X ⊔ D.T)

@[expose] def J193 (D : Data G) (X A K : Subgroup G) : Subgroup G :=
  (X ⊔ D.T) ⊓ normalizer (K0193 D X A K : Set G)

@[expose] def E193 (D : Data G) (V X A K : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (E3.wClos V 1 (pCoreOf 2 (K0193 D X A K)))

end CFSG.LocalAnalysis.WeakClosure81
