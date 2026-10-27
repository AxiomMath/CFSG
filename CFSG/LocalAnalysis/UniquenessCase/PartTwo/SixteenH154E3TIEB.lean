module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16h_ra1b_barSub_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ stabTil V₀ V) (h₂ : X₂ ≤ stabTil V₀ V) :
    barSub V₀ V hV (X₁ ⊔ X₂) = barSub V₀ V hV X₁ ⊔ barSub V₀ V hV X₂ := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem s16h_isCyclic_of_map_subtype {S : Type*} [Group S] {H : Subgroup S}
    {P : Subgroup H} (hc : IsCyclic ↥(P.map H.subtype)) : IsCyclic ↥P :=
  isCyclic_of_surjective
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.toMonoidHom
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.surjective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
