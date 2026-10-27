module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitCard
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial

theorem ggNbrLSideSp_center {ℓ n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) :
    Subgroup.center (LargeEvenProj (LargeEvenSpGroup K ℓ)) = ⊥ := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) :=
    CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_proj_injective (CharP.cast_eq_zero K 2)
  let e : ↥(LargeEvenSpGroup K ℓ) ≃* LargeEvenProj (LargeEvenSpGroup K ℓ) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K ℓ))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  rw [← Subgroup.map_center_eq e,
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.center_statedSp_eq_bot ℓ,
    Subgroup.map_bot]

theorem ggNbrLSideSp_b2der {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (lab : LargeEvenLabel) :
    GGNbrLSideDich lab (LargeEvenMatConjImage
      (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) (LargeEvenGSpSet K 2)) := by
  intro _ _ _ _ _ _ _ _ J _ Q hQ4 _ hF α _
  exfalso
  obtain ⟨F, _, _, hFQ, ⟨e⟩⟩ := hF
  have h1 : 720 < Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rw [Nat.card_congr e.toEquiv]
    exact ggNbrLSidePSL3_card_gt (by omega)
  have hle : ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≤ LargeEvenSpGroup K 2 :=
    Subgroup.commutator_le_self _
  have h2 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ 720 := by
    calc Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥J :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) :=
          Nat.card_le_card_of_injective J.subtype Subtype.val_injective
      _ ≤ Nat.card ↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ ≤ Nat.card ↥(LargeEvenSpGroup K 2) := Subgroup.card_le_of_le hle
      _ = 720 := by
          rw [SymplecticFlag.card_statedSp_two, hK]
          norm_num
  omega

end CFSG.StandardType
