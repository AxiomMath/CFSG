module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section EmbDefs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

abbrev embTau (φ : L ≃* antiSp K) (i : Axis) : G := w φ i.swap * w φ i * w φ i.swap

abbrev embVw (φ : L ≃* antiSp K) (t : G) (i : Axis) : Subgroup G :=
  (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom

@[expose] def EmbE1Concl (φ : L ≃* antiSp K) (i : Axis) : Prop := embTau φ i ∈ Sk φ i

@[expose] def EmbGenConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  Ytor φ i = Vtor φ t i i ⊔ (Vtor φ t i i).map (MulAut.conj (embTau φ i)⁻¹).toMonoidHom

@[expose] def EmbE5Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  Mhat φ t i i ⊓ embVw φ t i = ⊥

end EmbDefs

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
