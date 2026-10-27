module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition
public import CFSG.StronglyEmbedded.BenderNormalSeries

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem elementary_hull_native_odd_quotient_model (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    fusionIsBenderGroup (G ⧸ oddCore G) := by
  have hcore := involutionCore_eq_top_of_elementary_hull V hV hgen
  have hrank : TwoRankAtLeastTwo G :=
    (twoRankAtLeastTwo_of_elementary_card_ge_four V hV hcard).map_of_injective
      V.subtype V.subtype_injective
  have hcoreRank : TwoRankAtLeastTwo (involutionCore G) :=
    twoRankAtLeastTwo_involutionCore_iff.mpr hrank
  have hSE := theorem_SE H hH.to_native
  rcases hSE with hlow | hmodel
  · exact (hlow hcoreRank).elim
  · let L : Subgroup G := involutionCore G
    let e : L ≃* G := (MulEquiv.subgroupCongr hcore).trans Subgroup.topEquiv
    have hmap : (twoPrimeCore L).map e.toMonoidHom = oddCore G := by
      rw [oddCore_eq_twoPrimeCore]
      simpa only [twoPrimeCore] using pPrimeCore_map_iso 2 e
    let q : (L ⧸ twoPrimeCore L) ≃* (G ⧸ oddCore G) :=
      QuotientGroup.congr (twoPrimeCore L) (oddCore G) e hmap
    exact fusionIsBenderGroup_of_isSimpleBenderGroup (hmodel.1.map_mulEquiv q)

theorem normal_elementary_hull_native_recognition (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hVH : V ≤ H)
    (hVnormal : (V.subgroupOf H).Normal) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    IsQuasisimple G ∧ Subgroup.center G = oddCore G ∧
      Odd (Nat.card (Subgroup.center G)) ∧
        fusionIsBenderGroup (G ⧸ Subgroup.center G) := by
  obtain ⟨hquasi, hcenter, hodd⟩ := normal_elementary_hull_quasisimple H V
    hH hVH hVnormal hV hcard hgen
  exact ⟨hquasi, hcenter, hodd,
    rankOneModel_of_equiv (QuotientGroup.quotientMulEquivOfEq hcenter)
      (elementary_hull_native_odd_quotient_model H V hH hV hcard hgen)⟩

theorem normal_elementary_hull_native_explicit_recognition
    (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hVH : V ≤ H)
    (hVnormal : (V.subgroupOf H).Normal) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    IsQuasisimple G ∧ Subgroup.center G = oddCore G ∧
      Odd (Nat.card (Subgroup.center G)) ∧
        ExplicitRankOneModel (G ⧸ Subgroup.center G) := by
  obtain ⟨hquasi, hcenter, hodd, hmodel⟩ :=
    normal_elementary_hull_native_recognition H V hH hVH hVnormal hV hcard hgen
  exact ⟨hquasi, hcenter, hodd,
    (explicitRankOneModel_iff_fusionIsBenderGroup _).mpr hmodel⟩

end CFSG.ShultStronglyClosedTI
