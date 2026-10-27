module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusAut
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusAutFour
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusConj
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusStep
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusStepFour
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmCent
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmCentFour
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFrame
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour
import CFSG.LieType.Universal.Spin.Datum
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem
open QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace KGOm

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pCoreOf_le_range_of_longRoot_five {n : ℕ} (hn5 : 5 ≤ n) {G : Type} [Group G]
    {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer
      {ψ ((plusFrame n K (by omega)).longRoot (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
        (by simp) true true (.ofAdd 1))}) ≤ ψ.range := by
  have hn : 3 ≤ n := by omega
  intro a ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := (GGRootNorm.pCoreOf_le _ ha).1
  obtain ⟨γ, c, ε, τ, hconj, hcA⟩ := exists_conj_plusSemi_of_mem_normalizer hn5 hψ ha_norm
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have h10 : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp
  have h20 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp
  have hc0 := c_longRoot_of_plusSemi hn hcA h12 h10 h20 true true 1
  rw [show τ (1 : K) = 1 from map_one τ] at hc0
  have hOE : CFSG.RankThree.Classical2.orthDerived (quadPlus n K) ≤
      elementaryGroup (quadPlus n K) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn]
  obtain ⟨hCx, hLQ, hdisj, hQ⟩ := centralizer_decomp_hypFrame_five (plusFrame n K hn)
    (nondegenerate_polarBilin_quadPlus n K)
    (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE (k := ⟨3, by omega⟩)
    (l := ⟨4, by omega⟩) (m := ⟨0, by omega⟩) h12 (by simp) (by simp) h10 (by simp) (by simp)
    h20 (by simp) (by simp) (by simp) true true one_ne_zero
    RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus hn)
    (RootCentOmega.spinAction_longRoot_eq_eichler _ h12 true true 1)
  obtain ⟨h, hh, hkey⟩ := KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha hc0 hconj
  obtain ⟨-, -, hcid⟩ := eq_self_of_plusLevi_conj hn5 hcA h12 h10 h20 true true hh hkey
  exact KGRig.mem_range_of_conj_eq hC ha_norm (g := γ) fun k => by rw [hconj, hcid]

theorem pCoreOf_le_range_of_longRoot_four {G : Type} [Group G]
    {ψ : spinGroup (quadPlus 4 K) →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hK : 4 ≤ Nat.card K) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer
      {ψ ((plusFrame 4 K Triality.three_le_four).longRoot (i := ⟨1, by omega⟩)
        (j := ⟨2, by omega⟩) (by simp) true true (.ofAdd 1))}) ≤ ψ.range := by
  intro a ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := (GGRootNorm.pCoreOf_le _ ha).1
  obtain ⟨γ, c, k, ε, τ, hconj, hcA⟩ := exists_conj_tri_of_mem_normalizer hψ ha_norm
  have hc0 := c_longRoot_highest_of_tri hcA
  have hOE : CFSG.RankThree.Classical2.orthDerived (quadPlus 4 K) ≤
      elementaryGroup (quadPlus 4 K) := by
    rw [CFSG.RankThree.Classical2.orthDerived,
      commutator_orthogonalGroup_quadPlus Triality.three_le_four]
  obtain ⟨hCx, hLQ, hdisj, hQ, hsplit⟩ := centralizer_decomp_frame_four
    (nondegenerate_polarBilin_quadPlus 4 K)
    (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup Triality.three_le_four) hOE
    (plusFrame 4 K Triality.three_le_four)
    (fun x hx => RootCentOmega.eq_zero_of_polar_plusVec hx) (i := ⟨1, by omega⟩)
    (j := ⟨2, by omega⟩) (k := ⟨3, by omega⟩) (l := ⟨0, by omega⟩) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) true true one_ne_zero hK
    RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus Triality.three_le_four)
    (RootCentOmega.spinAction_longRoot_eq_eichler _ (by simp) true true 1)
  rw [hsplit] at hCx hLQ hdisj
  obtain ⟨h, hh, hkey⟩ := KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha hc0 hconj
  have hcid := eq_self_of_plusLeviFour_conj hcA hh hkey
  exact KGRig.mem_range_of_conj_eq hC ha_norm (g := γ) fun z => by rw [hconj, hcid]

theorem isSolvable_range_inf_centralizer_four_two {G : Type} [Group G]
    {ψ : spinGroup (quadPlus 4 K) →* G} (hψ : Function.Injective ψ) (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer
      {ψ ((plusFrame 4 K Triality.three_le_four).longRoot (i := ⟨1, by omega⟩)
        (j := ⟨2, by omega⟩) (by simp) true true (.ofAdd 1))}) := by
  rw [RCSTSp.range_inf_centralizer_of_injective hψ]
  haveI := isSolvable_centralizer_frame_four_two (nondegenerate_polarBilin_quadPlus 4 K)
    (plusFrame 4 K Triality.three_le_four)
    (fun x hx => RootCentOmega.eq_zero_of_polar_plusVec hx) (i := ⟨1, by omega⟩)
    (j := ⟨2, by omega⟩) (k := ⟨3, by omega⟩) (l := ⟨0, by omega⟩) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) true true one_ne_zero hK
    RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus Triality.three_le_four)
    (RootCentOmega.spinAction_longRoot_eq_eichler _ (by simp) true true 1)
  exact solvable_of_surjective (MonoidHom.subgroupMap_surjective ψ _)

end KGOm

section Tags

private theorem pCoreOf_le_range_POmegaPlus {G : Type} [Group G] {n f : ℕ} (hn4 : 4 ≤ n)
    {ψ : (ggU .POmegaPlus n f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {r : G}
    (hr : GGRootInvolution (ggU .POmegaPlus n f).D .POmegaPlus ψ r)
    (hnsolv : ¬ Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer {r})) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {r}) ≤ ψ.range := by
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hC hr hnsolv
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn).le
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 hnsolv ⊢
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  have hx' : x ∈ ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := hX ▸ hx
  obtain ⟨c₀, rfl⟩ := hx'
  have hc : Multiplicative.toAdd c₀ ≠ 0 := by
    intro h0
    have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
    rw [hc₀, map_one, mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨w, hw⟩ := KGOm.exists_conj_longRoot_std hn hij s t hc
  rw [ofAdd_toAdd] at hw
  let ψ' : spinGroup (quadPlus n (GaloisField 2 f)) →* G :=
    ψ.comp (MulAut.conj (u * w)).toMonoidHom
  have hψ' : Function.Injective ψ' := RCSTSp.comp_conj_injective hinj (u * w)
  have hrange : ψ'.range = ψ.range := RCSTSp.range_comp_conj ψ (u * w)
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  have hx₀ : ψ' ((plusFrame n (GaloisField 2 f) hn).longRoot (i := ⟨1, by omega⟩)
      (j := ⟨2, by omega⟩) (by simp) true true (.ofAdd 1)) =
      ψ (u * (plusFrame n (GaloisField 2 f) hn).longRoot hij s t c₀ * u⁻¹) := by
    change ψ ((u * w) * _ * (u * w)⁻¹) = _
    rw [show ∀ y : spinGroup (quadPlus n (GaloisField 2 f)),
      (u * w) * y * (u * w)⁻¹ = u * (w * y * w⁻¹) * u⁻¹ from fun y => by group, hw]
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · rcases RCSTOm.card_eq_two_or_four_le (GaloisField 2 f) with hK | hK
    · have h := KGOm.isSolvable_range_inf_centralizer_four_two hψ' hK
      rw [hx₀, hrange] at h
      exact absurd h hnsolv
    · have h := KGOm.pCoreOf_le_range_of_longRoot_four hψ' hC' hK
      rw [hx₀, hrange] at h
      exact h
  · have h := KGOm.pCoreOf_le_range_of_longRoot_five hn5 hψ' hC'
    rw [hx₀, hrange] at h
    exact h

theorem ggRootCentOTwoTag_POmegaPlus : GGRootCentOTwoTag .POmegaPlus := by
  intro G _ _ n f ψ hadm _ hker _ _ hC _ r hr hnsolv
  exact pCoreOf_le_range_POmegaPlus hadm.2.2 hker hC hr hnsolv

end Tags

end CFSG.StandardType
