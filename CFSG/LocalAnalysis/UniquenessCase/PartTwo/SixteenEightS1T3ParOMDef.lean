module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin

@[expose] def s16t3MinusCuts (r : ℕ) : Fin ((r + 1) / 2 + 1) → ℕ :=
  fun i => min (2 * (i : ℕ)) r

@[expose] noncomputable def s16t3MinusParab (K : Type) [Field K] (r : ℕ) :
    Subgroup (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
  (orthParab r (minusTailForm K 1 1) (s16t3MinusCuts r)).map
    (orthElementaryGroup (quadTail r (minusTailForm K 1 1))).subtype

@[expose] noncomputable def S16t3MinusCensus (K : Type) [Field K] (r : ℕ) : Prop :=
  Nat.card ↥(s16t3MinusParab K r) = 3 ^ ((r + 2) / 2) *
      2 ^ (Nat.card ↥(orthElementaryGroup (quadTail r (minusTailForm K 1 1)))).factorization 2 ∧
    ∀ p ∈ s16t3MinusParab K r, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
