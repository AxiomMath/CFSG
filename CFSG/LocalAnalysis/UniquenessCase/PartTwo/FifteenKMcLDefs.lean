module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

structure McRep {W : Type} [CommGroup W] (J : Subgroup (MulAut W)) (R : Subgroup W) where
  V : Type
  [addComm : AddCommGroup V]
  [module : Module (ZMod 2) V]
  [fin : Finite V]
  e : ↥R ≃* Multiplicative V
  ρ : ↥J →* LinearMap.GeneralLinearGroup (ZMod 2) V
  stable : StableUnder J R
  hρ : ∀ (j : ↥J) (r : ↥R) (hr : (j : MulAut W) (r : W) ∈ R),
    e ⟨(j : MulAut W) (r : W), hr⟩ =
      Multiplicative.ofAdd ((ρ j : V →ₗ[ZMod 2] V) (Multiplicative.toAdd (e r)))
  inj : Function.Injective ρ

attribute [instance] McRep.addComm McRep.module McRep.fin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
