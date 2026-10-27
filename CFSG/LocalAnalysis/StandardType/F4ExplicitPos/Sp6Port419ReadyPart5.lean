module

public import CFSG.GroupTheory.MulAutCongr
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG7
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart4

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.F4ExplicitPos.RankOrbit

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem finrank_span_eq_compRank {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : Ψ.Finite) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ := by
  let g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun v i => (v i : ℚ)
  let f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℚ) :=
    { toFun := g
      map_add' := by intro a b; funext i; simp [g]
      map_smul' := by intro a b; funext i; simp [g] }
  have hfinj : Function.Injective f := by
    intro a b h
    funext i
    have h' := congrFun h i
    exact Int.cast_injective h'
  have : Module.Finite ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Module.Finite.span_of_finite ℤ (hΨ.image f)
  have hmap : (Submodule.span ℤ Ψ).map f = Submodule.span ℤ (f '' Ψ) := by
    rw [Submodule.map_span]
  have heq : Module.finrank ℤ (Submodule.span ℤ Ψ) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) := by
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfinj (Submodule.span ℤ Ψ))
  have hM : Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Submodule.finrank_span_eq_finrank_span ℤ ℚ (f '' Ψ)
  have hcomp : compRank Ψ = Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) := by
    rw [compRank]
    rfl
  rw [hcomp, hM]
  exact heq

end CFSG.StandardType.F4ExplicitPos.RankOrbit

end
end
end
end
end
end
end
end
end
end
end

end
