module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesCover
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Norm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem sporadicThreePermuting_J3_of_card_center_three
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.Blueprint.NativeSporadic.J3) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  let f : ↥K →* ↥CFSG.Sporadic.Schreier.j3P :=
    (e.trans CFSG.Sporadic.Schreier.j3PermEquiv).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥K))
  have hf : Function.Surjective f :=
    (e.trans CFSG.Sporadic.Schreier.j3PermEquiv).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center ↥K := by
    ext x
    simp [f, MonoidHom.mem_ker]
  exact exists_permutes_of_normalizer_cover CFSG.QuasithinUnique.Ch1.SporLat.J3K.S_sylow
    CFSG.QuasithinUnique.Ch1.SporLat.J3K.card_normalizer_S
    CFSG.QuasithinUnique.Ch1.SporLat.J3K.n3_mem_normalizer
    CFSG.QuasithinUnique.Ch1.SporLat.J3K.n3_ne_one CFSG.QuasithinUnique.Ch1.SporLat.J3K.n3_pow_three
    CFSG.QuasithinUnique.Ch1.SporLat.J3K.n3inv_conj f hf hker hZ hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
