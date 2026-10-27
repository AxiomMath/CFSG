module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def RationalLabelIs
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (lab : LargeEvenLabel) : Prop :=
  LargeEvenInLambda2 lab ∧
    GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

end CFSG.StandardType.TablePThreeKG

end
