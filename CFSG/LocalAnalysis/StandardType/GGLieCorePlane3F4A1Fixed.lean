module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Descent
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4A1Alg

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

attribute [local instance] ZMod.algebra algebraicClosure.isAlgClosure IsAlgClosure.isAlgClosed

theorem ggLieF4A1_fixedGroup
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 1 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 2)
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i) :
    GGLieSL2Model ↥(rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  obtain ⟨b₁, b₂, D₀, j, hq₀, h₀, hΨ, ⟨e⟩⟩ := ggLieF4Plane_descent h i
  have : CharP ↥(algebraicClosure (ZMod 2) L) 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) ↥(algebraicClosure (ZMod 2) L)) 2
      (by norm_num)
  have : Algebra.IsAlgebraic (ZMod 2) ↥(algebraicClosure (ZMod 2) L) :=
    algebraicClosure.isAlgebraic (ZMod 2) L
  rw [← hΨ] at hshape hρΨ
  exact GGLieSL2Model.congr e (ggLieF4A1_fixedGroup_alg h₀ hf (hq₀.trans hqf) j hshape hρΨ)

end CFSG.StandardType.LieCore
