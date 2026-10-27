module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSkew

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Transport

variable {τ : Tag} {S : TcrSys}

@[expose] noncomputable def tcrWEnd (τ : Tag) (g : WeylGroup τ) :
    AddMonoid.End (Fin τ.rank → ℤ) :=
  DistribMulAction.toAddMonoidEnd (WeylGroup τ) (Fin τ.rank → ℤ) g

theorem tcrWEnd_apply (g : WeylGroup τ) (x : Fin τ.rank → ℤ) : tcrWEnd τ g x = g • x := rfl

end Transport

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Transport3

variable {τ : Tag} {S : TcrSys}

theorem tcrWEnd_iform
    (g : WeylGroup τ) (x y : Fin τ.rank → ℤ) : iform (tcrWEnd τ g x) (tcrWEnd τ g y) = iform x y :=
  iform_smul g x y

end Transport3

end CFSG.StandardType.TableCRes

end
