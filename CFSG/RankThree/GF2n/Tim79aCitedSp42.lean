module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix

@[expose] def Sp42CoverLiftStatement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* StatedSp 2 (GaloisField 2 1)),
    Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ →
    Nat.card φ.ker = 2 →
    ∀ (t s : Γ) (v w : Fin 2 ⊕ Fin 2 → GaloisField 2 1), v ≠ 0 → w ≠ 0 → v ≠ w →
      v ⬝ᵥ ((fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) *ᵥ w) = 0 →
      ((φ t : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) =
        1 + vecMulVec v (v ᵥ* (fromBlocks 0 1 (-1) 0 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 1))) →
      ((φ s : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) =
        1 + vecMulVec w (w ᵥ* (fromBlocks 0 1 (-1) 0 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 1))) →
      t * t = 1 → s * s = 1 → t * s ≠ s * t

end CFSG.RankThree.GF2n.Tim79a
