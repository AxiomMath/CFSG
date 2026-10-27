module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoWitt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoInvol
public import CFSG.ClassicalGroups.Orthogonal.Simple

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap

private def omSevenGM_Induced {K : Type} [Field K]
    (A : Matrix.GeneralLinearGroup OmegaSevenIdx K)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))) : Prop :=
  ∀ x : StatedOmega (StatedQuadOdd 3 K), ∃ y : StatedOmega (StatedQuadOdd 3 K),
    (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
        A * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * A⁻¹ ∧
      β (QuotientGroup.mk x) = QuotientGroup.mk y

private lemma omSevenGM_ext {K : Type} [Field K]
    {β₁ β₂ : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))}
    (h : ∀ x : StatedOmega (StatedQuadOdd 3 K),
      β₁ (QuotientGroup.mk x) = β₂ (QuotientGroup.mk x)) : β₁ = β₂ := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  exact h x

private lemma omSevenGM_induced_mul {K : Type} [Field K]
    {A₁ A₂ : Matrix.GeneralLinearGroup OmegaSevenIdx K}
    {β₁ β₂ : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))}
    (h₁ : omSevenGM_Induced A₁ β₁) (h₂ : omSevenGM_Induced A₂ β₂) :
    omSevenGM_Induced (A₁ * A₂) (β₁ * β₂) := by
  intro x
  obtain ⟨y₁, hy₁, hβ₁⟩ := h₂ x
  obtain ⟨y₂, hy₂, hβ₂⟩ := h₁ y₁
  refine ⟨y₂, ?_, ?_⟩
  · rw [hy₂, hy₁]; group
  · show β₁ (β₂ (QuotientGroup.mk x)) = QuotientGroup.mk y₂
    rw [hβ₁, hβ₂]

private lemma omSevenGM_induced_eq {K : Type} [Field K]
    {B₁ B₂ : Matrix.GeneralLinearGroup OmegaSevenIdx K}
    {β₁ β₂ : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))}
    (hB : B₁ = B₂) (h₁ : omSevenGM_Induced B₁ β₁) (h₂ : omSevenGM_Induced B₂ β₂) :
    β₁ = β₂ := by
  apply omSevenGM_ext
  intro x
  obtain ⟨y₁, hy₁, hβ₁⟩ := h₁ x
  obtain ⟨y₂, hy₂, hβ₂⟩ := h₂ x
  rw [hβ₁, hβ₂]
  have hy : y₁ = y₂ := Subtype.ext (by rw [hy₁, hy₂, hB])
  rw [hy]

private lemma omSevenGM_congr_conj {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (g : G) : MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private lemma omSevenGM_congr_symm {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (φ : MulAut G) (y : H) :
    φ (e.symm y) = e.symm ((MulAut.congr e φ) y) := by
  rw [MulAut.congr_apply]
  simp

private lemma omSevenGM_conj_mk {K : Type} [Field K]
    (gΩ x : StatedOmega (StatedQuadOdd 3 K)) :
    MulAut.conj (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadOdd 3 K)))
        (QuotientGroup.mk x : StatedProj (StatedOmega (StatedQuadOdd 3 K))) =
      (QuotientGroup.mk (gΩ * x * gΩ⁻¹) :
        StatedProj (StatedOmega (StatedQuadOdd 3 K))) := by
  rw [MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]

private lemma omSevenGM_induced_conj {K : Type} [Field K]
    (B : Matrix.GeneralLinearGroup OmegaSevenIdx K)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K))))
    (gΩ : StatedOmega (StatedQuadOdd 3 K)) (hβ : omSevenGM_Induced B β) :
    omSevenGM_Induced
      ((gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K) * B *
        (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K)⁻¹)
      (MulAut.conj (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadOdd 3 K))) * β *
        (MulAut.conj (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadOdd 3 K))))⁻¹) := by
  intro x
  obtain ⟨y, hy, hβy⟩ := hβ (gΩ⁻¹ * x * gΩ)
  refine ⟨⟨(gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
      (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
      (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K)⁻¹, ?_⟩, ?_, ?_⟩
  · exact (StatedOmega (StatedQuadOdd 3 K)).mul_mem
      ((StatedOmega (StatedQuadOdd 3 K)).mul_mem gΩ.2 y.2)
      ((StatedOmega (StatedQuadOdd 3 K)).inv_mem gΩ.2)
  · change (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
        (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
        (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K)⁻¹ =
      (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K) * B *
        (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K)⁻¹ *
        (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
        ((gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K) * B *
          (gΩ : Matrix.GeneralLinearGroup OmegaSevenIdx K)⁻¹)⁻¹
    rw [hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · have h1 : (MulAut.conj (QuotientGroup.mk gΩ :
          StatedProj (StatedOmega (StatedQuadOdd 3 K))))⁻¹
        (QuotientGroup.mk x : StatedProj (StatedOmega (StatedQuadOdd 3 K))) =
        (QuotientGroup.mk (gΩ⁻¹ * x * gΩ) :
          StatedProj (StatedOmega (StatedQuadOdd 3 K))) := by
      rw [← map_inv MulAut.conj (QuotientGroup.mk gΩ :
            StatedProj (StatedOmega (StatedQuadOdd 3 K)))]
      rw [← QuotientGroup.mk_inv, omSevenGM_conj_mk gΩ⁻¹ x, inv_inv]
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, hβy, omSevenGM_conj_mk gΩ y]
    rfl

private lemma omSevenGM_map_eichlerProj {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {A : Matrix.GeneralLinearGroup OmegaSevenIdx K}
    (hA : ∀ v, quadOdd 3 K (A.val.mulVec v) = quadOdd 3 K v)
    {β : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))}
    (hβ : omSevenGM_Induced A β) (u w : OmegaSevenIdx → K) :
    β (eichlerProj h2 u w) = eichlerProj h2 (A.val.mulVec u) (A.val.mulVec w) :=
  map_eichlerProj_of_isometry h2 hA hβ u w

private lemma omSevenGM_orderOf_eichlerProj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0) {u w : OmegaSevenIdx → K}
    (h : OmegaSevenShortPair u w) : orderOf (eichlerProj h2 u w) = 3 :=
  orderOf_eichlerProj hK h2 h.1 h.2.1 h.2.2.1 (by rw [h.2.2.2]; exact one_ne_zero)

private lemma omSevenGM_liftsConjugate_eichlerProj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0) {u w : OmegaSevenIdx → K}
    (h : OmegaSevenShortPair u w) : LiftsConjugate (eichlerProj h2 u w) := by
  obtain ⟨u₀, w₀, h₀, hlc⟩ := exists_liftsConjugate_eichlerProj hK h2
  obtain ⟨g, hg⟩ := exists_inner_conj_eichlerProj hK h2 h₀ h
  have hmap := LiftsConjugate.map (MulAut.conj g) hlc
  rw [MulAut.conj_apply, hg] at hmap
  exact hmap

theorem omegaSevenInvolData_holds : OmegaSevenInvolData := by
  intro S _ _ hm σ hσ
  have hmodel := hm.statedClassicalModel (by decide)
  obtain ⟨hadm, K, hField, hFinite, hKcard, hE⟩ := hmodel
  letI : Field K := hField
  letI : Finite K := hFinite
  obtain ⟨e⟩ := hE
  have hK : Nat.card K = 3 := by rw [hKcard, pow_one]
  letI : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : CharP K 3 := charP_of_card_eq_prime hFcard
  have h2 : (2 : K) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime K (p := 3) (q := 2) (by decide) (by decide)
  let P := StatedProj (StatedOmega (StatedQuadOdd 3 K))
  let σP : MulAut P := MulAut.congr e σ
  have hσP : orderOf σP = 2 := by rw [MulEquiv.orderOf_eq]; exact hσ
  obtain ⟨A, hAiso, hA2, hAneScalar, hβ⟩ := exists_isometry_of_involution hK σP hσP
  have hσP_ind : omSevenGM_Induced A σP := hβ
  let T : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) := (toLinEquiv OmegaSevenIdx K) A
  have hA_mv : ∀ v, A.val.mulVec v = T v := fun v => (toLinEquiv_apply A v).symm
  have hTmem : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [show T v = A.val.mulVec v from toLinEquiv_apply A v]
    exact hAiso v
  have hT2 : T * T = 1 := by
    change (toLinEquiv OmegaSevenIdx K) A * (toLinEquiv OmegaSevenIdx K) A = 1
    rw [← map_mul, hA2, map_one]
  have hT1 : T ≠ 1 := by
    intro h
    apply hAneScalar
    have hA1 : A = 1 := (toLinEquiv OmegaSevenIdx K).injective (by
      rw [show (toLinEquiv OmegaSevenIdx K) A = T from rfl, h, map_one])
    rw [hA1]
    exact Subgroup.one_mem _
  have hneg_scalar : (LinearEquiv.neg K : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K)) ∈
      CFSG.ClassicalGroups.Orthogonal.scalars K (OmegaSevenIdx → K) :=
    CFSG.ClassicalGroups.Orthogonal.mem_scalars.mpr ⟨-1, fun v => by
      rw [LinearEquiv.neg_apply]; simp⟩
  have hTneg : T ≠ LinearEquiv.neg K := by
    intro h
    apply hAneScalar
    refine (CFSG.ClassicalGroups.Orthogonal.mem_statedScalars_iff A).mpr ?_
    rw [show (toLinEquiv OmegaSevenIdx K) A = T from rfl, h]
    exact hneg_scalar
  have hgeo := involution_geometry hK T hTmem hT2 hT1 hTneg
  rcases hgeo with hcase1 | hcase2
  ·
    left
    obtain ⟨u, w, hShort, hmap⟩ := hcase1
    have hσP_x : σP (eichlerProj h2 u w) = (eichlerProj h2 u w)⁻¹ := by
      rw [omSevenGM_map_eichlerProj h2 hAiso hσP_ind u w, hA_mv u, hA_mv w]
      rcases hmap with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · rw [hu, hw, eichlerProj_inv h2 hShort.1 hShort.2.2.1]
      · rw [hu, hw, eichlerProj_neg_left, eichlerProj_inv h2 hShort.1 hShort.2.2.1]
    refine ⟨e.symm (eichlerProj h2 u w), ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq e.symm, omSevenGM_orderOf_eichlerProj hK h2 hShort]
    · rw [omSevenGM_congr_symm e σ, hσP_x, map_inv]
    · exact LiftsConjugate.map e.symm (omSevenGM_liftsConjugate_eichlerProj hK h2 hShort)
  ·
    right
    obtain ⟨g, hg, hcomm, hpair_exists, hsep⟩ := hcase2
    let gMat : Matrix.GeneralLinearGroup OmegaSevenIdx K := (toLinEquiv OmegaSevenIdx K).symm g
    have hgMat : (toLinEquiv OmegaSevenIdx K) gMat = g := MulEquiv.apply_symm_apply _ g
    have hgOmega : gMat ∈ StatedOmega (StatedQuadOdd 3 K) := by
      rw [statedOmega_quadOdd_eq_map h2 (by norm_num : 3 ≤ 3)]
      exact Subgroup.mem_map_of_mem _ hg
    let gΩ : StatedOmega (StatedQuadOdd 3 K) := ⟨gMat, hgOmega⟩
    let gP : P := QuotientGroup.mk gΩ
    let gS : S := e.symm gP
    have hgS : e gS = gP := e.apply_symm_apply gP
    let B : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) := g * T * g⁻¹
    let A' : Matrix.GeneralLinearGroup OmegaSevenIdx K := gMat * A * gMat⁻¹
    let τ : MulAut S := MulAut.conj gS * σ * (MulAut.conj gS)⁻¹
    let τP : MulAut P := MulAut.congr e τ
    have hg_orth : ∀ v, quadOdd 3 K (g v) = quadOdd 3 K v :=
      fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (elementaryGroup_le_orthogonalGroup (quadOdd 3 K) hg)) v
    have hg_inv_orth : ∀ v, quadOdd 3 K (g⁻¹ v) = quadOdd 3 K v :=
      fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (elementaryGroup_le_orthogonalGroup (quadOdd 3 K)
          ((elementaryGroup (quadOdd 3 K)).inv_mem hg))) v
    have hT_orth : ∀ v, quadOdd 3 K (T v) = quadOdd 3 K v := fun v => by
      rw [show T v = A.val.mulVec v from toLinEquiv_apply A v]
      exact hAiso v
    have hτP_congr : τP = MulAut.conj gP * σP * (MulAut.conj gP)⁻¹ := by
      show MulAut.congr e (MulAut.conj gS * σ * (MulAut.conj gS)⁻¹) =
        MulAut.conj gP * σP * (MulAut.conj gP)⁻¹
      rw [map_mul, map_mul, map_inv, omSevenGM_congr_conj e gS, hgS]
    have hτP_ind : omSevenGM_Induced A' τP := by
      rw [hτP_congr]
      exact omSevenGM_induced_conj A σP gΩ hσP_ind
    have htoA' : (toLinEquiv OmegaSevenIdx K) A' = B := by
      show (toLinEquiv OmegaSevenIdx K) (gMat * A * gMat⁻¹) = g * T * g⁻¹
      rw [map_mul, map_mul, map_inv, hgMat]
    have hA'_mv : ∀ v, A'.val.mulVec v = B v := by
      intro v
      rw [← toLinEquiv_apply, htoA']
    have hA'iso : ∀ v, quadOdd 3 K (A'.val.mulVec v) = quadOdd 3 K v := by
      intro v
      rw [hA'_mv v]
      show quadOdd 3 K (g (T (g⁻¹ v))) = quadOdd 3 K v
      rw [hg_orth, hT_orth, hg_inv_orth]
    have hA'A_comm : A' * A = A * A' := by
      apply (toLinEquiv OmegaSevenIdx K).injective
      simp only [map_mul]
      rw [htoA']
      exact hcomm.symm
    have hτσP_comm : τP * σP = σP * τP :=
      omSevenGM_induced_eq hA'A_comm (omSevenGM_induced_mul hτP_ind hσP_ind)
        (omSevenGM_induced_mul hσP_ind hτP_ind)
    have hτσ_comm : τ * σ = σ * τ := by
      apply (MulAut.congr e).injective
      simpa only [map_mul, τP, σP] using hτσP_comm
    obtain ⟨u₂, w₂, hu₂, hu₂0, huw₂, hQw₂, hsep_map, hsepB_u, hsepB_w⟩ := hsep
    have hσP_z : σP (eichlerProj h2 u₂ w₂) = (eichlerProj h2 u₂ w₂)⁻¹ := by
      rw [omSevenGM_map_eichlerProj h2 hAiso hσP_ind u₂ w₂, hA_mv u₂, hA_mv w₂]
      rcases hsep_map with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · rw [hu, hw, eichlerProj_inv h2 hu₂ huw₂, eichlerProj_neg_left]
      · rw [hu, hw, eichlerProj_inv h2 hu₂ huw₂]
    have hτP_z : τP (eichlerProj h2 u₂ w₂) = eichlerProj h2 u₂ w₂ := by
      rw [omSevenGM_map_eichlerProj h2 hA'iso hτP_ind u₂ w₂, hA'_mv u₂, hA'_mv w₂]
      rcases hsep_map with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · rw [hsepB_u, hsepB_w, hu, hw]
        rw [eichlerProj_neg_left h2 u₂ (-w₂), neg_neg]
      · rw [hsepB_u, hsepB_w, hu, hw, neg_neg]
    have hz_ne : eichlerProj h2 u₂ w₂ ≠ (eichlerProj h2 u₂ w₂)⁻¹ := by
      intro h
      have hz2 : eichlerProj h2 u₂ w₂ * eichlerProj h2 u₂ w₂ = 1 := by
        rw [show eichlerProj h2 u₂ w₂ * eichlerProj h2 u₂ w₂ =
          eichlerProj h2 u₂ w₂ * (eichlerProj h2 u₂ w₂)⁻¹ from
          congrArg (fun t => eichlerProj h2 u₂ w₂ * t) h]
        group
      have hdvd : orderOf (eichlerProj h2 u₂ w₂) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
      rw [orderOf_eichlerProj hK h2 hu₂ hu₂0 huw₂ hQw₂] at hdvd
      norm_num at hdvd
    have hτP_ne : τP ≠ σP := by
      intro h
      apply hz_ne
      calc eichlerProj h2 u₂ w₂ = τP (eichlerProj h2 u₂ w₂) := hτP_z.symm
        _ = σP (eichlerProj h2 u₂ w₂) := by rw [h]
        _ = (eichlerProj h2 u₂ w₂)⁻¹ := hσP_z
    have hτ_ne : τ ≠ σ := by
      intro h
      apply hτP_ne
      show MulAut.congr e τ = MulAut.congr e σ
      rw [h]
    obtain ⟨u, w, hShort, hmapTB⟩ := hpair_exists
    have htoAA' : (toLinEquiv OmegaSevenIdx K) (A * A') = T * B := by
      rw [map_mul, htoA']
    have hAA'_mv : ∀ v, (A * A').val.mulVec v = (T * B) v := by
      intro v
      rw [← toLinEquiv_apply, htoAA']
    have hAA'iso : ∀ v, quadOdd 3 K ((A * A').val.mulVec v) = quadOdd 3 K v := by
      intro v
      rw [hAA'_mv v]
      show quadOdd 3 K (T (B v)) = quadOdd 3 K v
      rw [hT_orth]
      show quadOdd 3 K (g (T (g⁻¹ v))) = quadOdd 3 K v
      rw [hg_orth, hT_orth, hg_inv_orth]
    have hxP_inv : (σP * τP) (eichlerProj h2 u w) = (eichlerProj h2 u w)⁻¹ := by
      rw [omSevenGM_map_eichlerProj h2 hAA'iso
        (omSevenGM_induced_mul hσP_ind hτP_ind) u w, hAA'_mv u, hAA'_mv w]
      rcases hmapTB with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · rw [hu, hw, eichlerProj_inv h2 hShort.1 hShort.2.2.1]
      · rw [hu, hw, eichlerProj_neg_left, eichlerProj_inv h2 hShort.1 hShort.2.2.1]
    refine ⟨gS, τ, rfl, hτσ_comm, hτ_ne, e.symm (eichlerProj h2 u w), ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq e.symm, omSevenGM_orderOf_eichlerProj hK h2 hShort]
    · have hcongr : MulAut.congr e (σ * τ) = σP * τP := by rw [map_mul]
      rw [omSevenGM_congr_symm e (σ * τ), hcongr, hxP_inv, map_inv]
    · exact LiftsConjugate.map e.symm (omSevenGM_liftsConjugate_eichlerProj hK h2 hShort)

theorem omegaSevenCover_holds : OmegaSevenCover :=
  omegaSevenCover_of_data omegaSevenInvolData_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
