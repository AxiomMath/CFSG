module

public import CFSG.LieType.Steinberg.Adjoint.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


theorem orderOf_xPar {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) [CharP K p] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {c : K} (hc : c ≠ 0) :
    orderOf (xPar F γ c) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ n : ℕ, xPar F γ c ^ n = xPar F γ ((n : K) * c) := by
    intro n
    induction n with
    | zero => simp [xPar_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← xPar_add]
      congr 1
      push_cast
      ring
  apply orderOf_eq_prime
  · rw [hpow, CharP.cast_eq_zero, zero_mul, xPar_zero]
  · intro h
    apply hc
    apply xPar_injective (F := F) hγ
    rw [h, xPar_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
