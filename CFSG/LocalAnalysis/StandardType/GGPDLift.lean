module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPD_normalizer_lift {K : Type} [Field K] {d : ℕ}
    {A : Subgroup (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))}
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥A ≃+ V}
    {φ : Γ → MulAut ↥A} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α) (i : Γ) :
    ∃ g : Matrix.GeneralLinearGroup (Fin d) K,
      ∀ (y : Matrix.GeneralLinearGroup (Fin d) K) (a : ↥A),
        QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) y = (a : _) →
          QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
            (g * y * g⁻¹) = ((φ i a : ↥A) : _) := by
  obtain ⟨g', -, -, hconj⟩ := hD.mem i
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) g'
  refine ⟨g, fun y a hy => ?_⟩
  have hπ : QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
        (g * y * g⁻¹)
      = g' * QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) y
          * g'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg]
  rw [hπ, hy, ← hconj a]

end CFSG.StandardType

end
