module

public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def GL3ExclR3 : Prop :=
  ∀ (r p : ℕ) [Fact r.Prime], p.Prime → 11 ≤ p → 7 ≤ r →
    ∀ W H : Subgroup (GL (Fin 3) (ZMod r)), IsIrreducibleMatrixRep W.subtype → H ≤ W →
      IsStronglyPEmbedded p (H.subgroupOf W) → ¬ r ∣ Nat.card H →
      (∀ g ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ Pi.single 0 1 ∈
        Submodule.span (ZMod r) {(Pi.single 0 1 : Fin 3 → ZMod r)} → g ∈ H) →
      ∀ t₁ ∈ H, (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1] →
      ∀ t₂ ∈ H, (t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![1, -1, 1] →
      ∀ y ∈ H, y ^ p = 1 → ∀ α : Fin 3 → ZMod r,
        (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α → (∃ i j, α i ≠ α j) → False

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
