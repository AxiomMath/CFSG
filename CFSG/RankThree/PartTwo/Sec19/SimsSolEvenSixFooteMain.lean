module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitFooteMain

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.OddStandard.HigherRank.YamadaG23 (StrothSigma6 FooteMainL6 LitStrothType IsQuotIso)
open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn normIn centIn)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)

theorem inCatalog_of_litStrothType_footeMain
    (hFM : FooteMainL6) (hCIT : ClassicalInvolutionTheoremModels) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (h : LitStrothType S) : CFSG.Assembly.InCatalog S := by
  rcases h with h | (⟨p, f, -, -, -, h⟩ | ⟨p, f, -, -, -, h⟩) | h
  · exact CFSG.RankThree.GF2n.sporadicBridge_HS S h
  · exact inCatalog_of_lieModel_classical h (by decide)
  · exact inCatalog_of_lieModel_classical h (by decide)
  · exact CFSG.OddStandard.HigherRank.YamadaG23.inCatalog_of_hasPSL6Sylow hFM hCIT hs h

theorem inCatalog_of_strothSigma6_footeMain
    (hStroth : StrothSigma6) (hFM : FooteMainL6) (hCIT : ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) {A : Subgroup G} (hA : IsE 4 ↥A)
    (hN : IsQuotIso (Subgroup.normalizer (A : Set G)) (Subgroup.centralizer (A : Set G))
      (Equiv.Perm (Fin 6)))
    (hSyl : IsSylowIn 2 (Subgroup.centralizer (A : Set G)) A) : CFSG.Assembly.InCatalog G := by
  haveI := hs
  have hN' : IsQuotIso (normIn ⊤ A) (centIn ⊤ A) (Equiv.Perm (Fin 6)) := by
    simp only [normIn, centIn, top_inf_eq]
    exact hN
  have hSyl' : IsSylowIn 2 (centIn ⊤ A) A := by
    simp only [centIn, top_inf_eq]
    exact hSyl
  exact inCatalog_of_top (inCatalog_of_litStrothType_footeMain hFM hCIT
    Subgroup.topEquiv.isSimpleGroup
    (hStroth G ⊤ A Subgroup.topEquiv.isSimpleGroup le_top hA hN' hSyl'))

end CFSG.RankThree.PartTwo.Sec19.SolEven
