module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDARefute
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAOrthModel
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDASpUnitary
import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLabels
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggInndiagOnCompAt_classical {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 4 ≤ lab.rank))
    (h3 : 3 ∣ 2 ^ lab.n + 1) (P : ℕ → LargeEvenLabel → Prop) : GGInndiagOnCompAt lab P := by
  obtain ⟨tag, r, g⟩ := lab
  obtain ⟨-, hrank⟩ := hlab
  dsimp only at htag h3
  unfold GGInndiagOnCompAt LargeEvenLabelAll
  intro Q hQ
  rcases htag with rfl | rfl | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
  · dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ hrank ⊢
    obtain ⟨K, _, _, hK, hQK⟩ := hQ
    haveI := CFSG.StandardType.charP_two_of_card hK
    exact ⟨K, inferInstance, inferInstance, hK, hQK,
      fun hR hna hfin s t _ hs3 hs1 ht3 hst hsI htI _ J₁ hJ₁ hM =>
        ggInndiagOnCompBody_of_comps
          (fun φ hφ => (MonoidHom.mem_range).1 (matConjImage_gsp_subset_inn (K := K) r hφ))
          hR hna hfin (ggInnerOrUnitaryOnComps_statedSp hK h3 hrank.1) s t hs3 hs1 ht3 hst
          hsI htI J₁ hJ₁ hM⟩
  · dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ hrank ⊢
    obtain ⟨K, _, _, hK, hQK⟩ := hQ
    haveI := CFSG.StandardType.charP_two_of_card hK
    exact ⟨K, inferInstance, inferInstance, hK, hQK,
      fun hR hna hfin s t _ hs3 hs1 ht3 hst hsI htI _ J₁ hJ₁ hM =>
        ggInndiagOnCompBody_of_comps
          (fun φ hφ => (MonoidHom.mem_range).1 (matConjImage_gsp_subset_inn (K := K) r hφ))
          hR hna hfin (ggInnerOrUnitaryOnComps_statedSp hK h3 hrank.1) s t hs3 hs1 ht3 hst
          hsI htI J₁ hJ₁ hM⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by omega)] at hQ ⊢
    dsimp only [LargeEvenRecipeOmegaPlus] at hQ ⊢
    obtain ⟨K, _, _, hK, hQK⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQK,
      fun hR hna hfin s t _ hs3 hs1 ht3 hst hsI htI _ J₁ hJ₁ hM =>
        ggInndiagOnCompBody_of_comps subset_rfl hR hna hfin
          (ggInnerOrUnitaryOnComps_omegaPlus hK h3 hr) s t hs3 hs1 ht3 hst hsI htI J₁ hJ₁ hM⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by omega), if_neg (by omega)] at hQ ⊢
    dsimp only [LargeEvenRecipeOmegaMinus] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hQK⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQK,
      fun hR hna hfin s t _ hs3 hs1 ht3 hst hsI htI _ J₁ hJ₁ hM =>
        ggInndiagOnCompBody_of_comps subset_rfl hR hna hfin
          (ggInnerOrUnitaryOnComps_omegaMinus hK h3 (by omega) hbc) s t hs3 hs1 ht3 hst hsI
          htI J₁ hJ₁ hM⟩

theorem ggInndiagOnCompAt_pairs_classical {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 4 ≤ lab.rank))
    (h3 : 3 ∣ 2 ^ lab.n + 1) :
    (GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩) ∧
      GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ :=
  ⟨ggInndiagOnCompAt_classical hlab htag h3 _, ggInndiagOnCompAt_classical hlab htag h3 _⟩

end CFSG.StandardType.SCFourCover

end
