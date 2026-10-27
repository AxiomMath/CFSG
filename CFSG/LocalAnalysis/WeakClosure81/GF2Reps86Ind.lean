module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv

@[expose] def T86 (n : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin n)), Function.Injective ψ →
      alternatingGroup (Fin n) ≤ ψ.range →
      ∀ t : ↥H, t ^ 2 = 1 → ψ t ≠ 1 → ¬ (ψ t).IsSwap →
        (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8 →
        NatVia ψ (commV H) ∨ (n = 7 ∧ ψ.range = alternatingGroup (Fin n))

@[expose] def NoFpf (n : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin n)), Function.Injective ψ →
      alternatingGroup (Fin n) ≤ ψ.range →
      ∀ t : ↥H, t ^ 2 = 1 → (∀ i, ψ t i ≠ i) →
        (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8 → False

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
