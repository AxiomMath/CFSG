module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4A2inFixed
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4A2inDerived
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Gamma

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4Plane_recogA2in
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 2 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 6)
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hin : twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u)) :
    Group.IsSolvable ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ∨
      LieModel (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
        Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) .PSL 3 2 f := by
  have hmodel := ggLieF4A2in_fixedGroup h hf hqf i hshape hρΨ hin
  have hΓ := ggLieF4_gamma_eq_model D h.finite h.hq
  exact ggLieF4A2in_derived h hf hqf i hρΨ hΓ hmodel

end CFSG.StandardType.LieCore
