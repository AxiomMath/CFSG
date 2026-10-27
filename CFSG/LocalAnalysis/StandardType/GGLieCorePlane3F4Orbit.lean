module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4Plane_image_eq
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i := by
  exact CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.f4_joint_componentRoots_image_eq_of_odd D ρ
    h.frob a₁ a₂ h.mem₁ h.mem₂ (p := 3) (by decide)
    (fun γ _ => CFSG.StandardType.TableCRes.rootChar_pow_eq_one_of_forall
      (pow_eq_one_of_rootDiagUnit_pow h.pow₁) γ)
    (fun γ _ => CFSG.StandardType.TableCRes.rootChar_pow_eq_one_of_forall
      (pow_eq_one_of_rootDiagUnit_pow h.pow₂) γ) i

end CFSG.StandardType.LieCore
