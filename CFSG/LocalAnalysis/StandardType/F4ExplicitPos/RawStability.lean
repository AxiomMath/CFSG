module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UF4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart5
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeInner

@[expose] public section

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes CFSG.StandardType.LieCore
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.F4ExplicitPos.RawStability

theorem ratOrbit_eq_of_image_eq
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    {ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)}
    (heq : ρ '' Ψ = Ψ) : ratOrbit ρ Ψ = Ψ := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k generalizing δ with
    | zero => simpa using hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [← heq]
      exact ⟨(ρ^[k]) δ, ih δ hδ, rfl⟩
  · intro hγ
    exact ⟨0, γ, hγ, by simp⟩

end CFSG.StandardType.F4ExplicitPos.RawStability

end

end
