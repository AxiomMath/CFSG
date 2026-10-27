module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.Walter.Bender1970.S1.FixedPointFreeAlgClosed
import CFSG.Walter.Bender1970.S1.FixedPointFreeBaseChange

public section

namespace CFSG.Walter

open Module
open scoped TensorProduct

theorem bender1970_1_5_finrank_eq
    {F V Γ : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Group Γ] [Finite Γ] (ρ : Representation F Γ V) (N R : Subgroup Γ)
    (hN : IsMulCommutative N) (hRN : R ≤ Subgroup.normalizer (N : Set Γ))
    (hfpf : ∀ x ∈ R, x ≠ 1 → ∀ n ∈ N, x * n * x⁻¹ = n → n = 1)
    (hNchar : ((Nat.card N : ℕ) : F) ≠ 0)
    (hCN : ∀ v : V, (∀ n ∈ N, ρ n v = v) → v = 0) :
    finrank F V = Nat.card R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  let K := AlgebraicClosure F
  let ρK := Theory.Representation.extendScalars K ρ
  have hNcharK : ((Nat.card N : ℕ) : K) ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).mpr hNchar
  have hCNK (w : K ⊗[F] V) (hw : ∀ n ∈ N, ρK n w = w) : w = 0 := by
    have h0 : Representation.invariants (ρ.comp N.subtype) = ⊥ :=
      (Submodule.eq_bot_iff _).mpr fun v hv => hCN v fun n hn => hv ⟨n, hn⟩
    have h1 := finrank_invariants_extendScalars (K := K) (ρ.comp N.subtype)
    rw [h0, finrank_bot, Submodule.finrank_eq_zero] at h1
    have hw' : w ∈ Representation.invariants
        (Theory.Representation.extendScalars K (ρ.comp N.subtype)) := fun n => hw n n.2
    rwa [h1] at hw'
  have key := bender1970_1_5_finrank_eq_of_isAlgClosed ρK N R hN hRN hfpf hNcharK hCNK
  rw [Module.finrank_baseChange] at key
  rw [key, ← finrank_invariants_extendScalars (K := K) (ρ.comp R.subtype)]
  rfl

end CFSG.Walter
