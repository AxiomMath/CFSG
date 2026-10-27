module

public import CFSG.RankThree.PartOne.K1320X.U4Model
public import CFSG.RankThree.PartOne.K1320X.Row6Img
public import CFSG.RankThree.PartOne.K1320.UThree
public import CFSG.RankThree.PartOne.S13K.KFLiftRows
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.K1320.RowDistinct
public import CFSG.RankThree.PartOne.KF.ClsPSLBig
public import CFSG.RankThree.PartOne.KF.ClsPSUBig
public import CFSG.RankThree.PartOne.KFOUT3.Cocycle
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KF132
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LocalCores

theorem statedModel_psu_four_of_cover
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {p : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 5 hK)) {Y : Subgroup G} (hYL : Y ≤ L) (hYperf : Group.IsPerfect ↥Y)
    (himg : (Y.subgroupOf L).map ε =
      (su4Emb (unitaryInvolution K 2 f)).range.map (suQ 5 hK)) :
    StatedClassicalModel ↥Y .PSU 4 2 f := by
  classical
  set Kc := Y.subgroupOf L with hKc
  obtain ⟨-, hQqs, hQmodel⟩ := su4_block_facts hK hf hq
  have eY : ↥Y ≃* ↥Kc := (Subgroup.subgroupOfEquivOfLe hYL).symm
  have hKcperf : Group.IsPerfect ↥Kc := by
    have := hYperf
    exact Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  have hsurj := ε.subgroupMap_surjective Kc
  have hker := ker_subgroupMap_le_center hε Kc
  have hQ' : IsQuasisimple ↥(Kc.map ε) := by
    rw [himg]
    exact hQqs
  have hKcqs : IsQuasisimple ↥Kc :=
    (isQuasisimple_iff_of_surjective hKcperf (ε.subgroupMap Kc) hsurj hker).2 hQ'
  obtain ⟨e₁⟩ := centerQuotientEquiv_of_surjective hKcperf (ε.subgroupMap Kc) hsurj hker
  obtain ⟨e₂⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr himg)
  have hKcmodel : StatedClassicalModel (↥Kc ⧸ Subgroup.center ↥Kc) .PSU 4 2 f :=
    Equivariance.statedClassicalModel_of_mulEquiv (e₁.trans e₂).symm hQmodel
  have hZKc : Subgroup.center ↥Kc = ⊥ :=
    psuFourEvenCenterTrivial_of_multipliers hGA ↥Kc f hf hKcqs hKcmodel
  exact Equivariance.statedClassicalModel_of_mulEquiv eY.symm
    (Equivariance.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZKc).trans QuotientGroup.quotientBot) hKcmodel)

theorem isPerfect_sup_two {G : Type} [Group G] {H₁ H₂ : Subgroup G} (h₁ : Group.IsPerfect ↥H₁)
    (h₂ : Group.IsPerfect ↥H₂) : Group.IsPerfect ↥(H₁ ⊔ H₂) := by
  have := K1320.isPerfect_sup_three h₁ h₂ h₂
  rwa [sup_assoc, sup_idem] at this

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem row6_sup_model (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF13 : Sec13Facts G p A c L E) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 5 hK)) {r₀ r₁ : MulAut E} {Kt : Subgroup G}
    (hr₀s : r₀ ∈ reflectionSet p E) (hr₀L : r₀ ∈ torusImage E L) (hr₁s : r₁ ∈ reflectionSet p E)
    (hr₁L : r₁ ∈ torusImage E L) (hKF₁ : KFAt p E (2 * f) r₁) (hKt : KFKt p E f r₀ Kt)
    (himgKt : (Kt.subgroupOf L).map ε = (su2Emb (unitaryInvolution K 2 f)).range.map (suQ 5 hK))
    (himg₁ : ((kZero p E r₁).subgroupOf L).map ε =
      (suBlock6 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
        (suQ 5 hK)) :
    StatedClassicalModel ↥(kZero p E r₁ ⊔ Kt) .PSU 4 2 f := by
  have hKtL : Kt ≤ L := hF13.kt_le L hF13.inZeroStar r₀ hr₀s hr₀L Kt hKt.1
  have hK1L : kZero p E r₁ ≤ L :=
    hF13.kt_le L hF13.inZeroStar r₁ hr₁s hr₁L _ (K1320.kfKt_of_kfAt hKF₁).1
  have hperf : Group.IsPerfect ↥(kZero p E r₁ ⊔ Kt) :=
    isPerfect_sup_two (S13K.isQuasisimple_of_model_psl_two hKF₁.2.1).1
      (S13K.isQuasisimple_of_model_psl_two hKt.2.2.1).1
  refine statedModel_psu_four_of_cover hGA hK hf ε hε hq (sup_le hK1L hKtL) hperf ?_
  rw [Subgroup.subgroupOf_sup hK1L hKtL, Subgroup.map_sup, himg₁, himgKt, sup_comm,
    ← Subgroup.map_sup, range_su2Emb_sup_suBlock6 hK (by omega)]

end CFSG.RankThree.PartOne.K1320X
