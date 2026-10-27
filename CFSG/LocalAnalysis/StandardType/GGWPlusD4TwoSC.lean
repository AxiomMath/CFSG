module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoNo27

public section

namespace CFSG.StandardType

open Module CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem ggOmegaPlusEight_sc_card {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {E : Subgroup (Om8 K)} (hE : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set (Om8 K)), g ^ 3 = 1 → g ∈ E) (h27 : 27 ≤ Nat.card E) :
    81 ≤ Nat.card E := by
  classical
  obtain ⟨r, ι₁, hr4, hinj, hrange, -, -⟩ := OrdPTri.exists_frame hE hSC
  have hcard : Nat.card E = 3 ^ r := OrdPTri.card_eq_of_frame hinj hrange
  have hr3 : 3 ≤ r := by
    have h27' : (3 : ℕ) ^ 3 ≤ 3 ^ r := by
      rw [hcard] at h27
      norm_num
      exact h27
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h27'
  have hr : r = 3 ∨ r = 4 := by omega
  rcases hr with h3 | h4
  · exfalso
    have hEcard : Nat.card E = 27 := by rw [hcard, h3]; norm_num
    obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
    let A : Subgroup (GL (Fin (2 * 4)) K) :=
      (E.comap (MonoidHom.id _)).map (matrixDerived (coordinateQuadPlus 4 K)).subtype
    have hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A :=
      genMax_of_orth hnd hT Nat.prime_three (by norm_num) hE hSC (MonoidHom.id _)
        Function.injective_id (fun x _ => ⟨x, rfl⟩)
    have hAcard : Nat.card A = 27 := by
      dsimp only [A]
      rw [Subgroup.card_map_of_injective
          (Subgroup.subtype_injective (matrixDerived (coordinateQuadPlus 4 K))),
        Subgroup.comap_id, hEcard]
    exact absurd hAcard (genMax_card_ne_27 hK hA)
  · rw [hcard, h4]
    norm_num

end CFSG.StandardType
