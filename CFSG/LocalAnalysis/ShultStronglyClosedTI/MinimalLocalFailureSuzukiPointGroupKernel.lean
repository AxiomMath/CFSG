module

import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairPointNormalizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupSetup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiOppositeRootCenter

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem proper_pair_suzuki_structure
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k)) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      1 ≤ m ∧ Nat.card Q = 2 ^ (2 * m + 1) ∧ K ⊓ B = X ∧
      ∃ ψ : K ≃* suzukiGroup m k,
        (H.subgroupOf K).map ψ.toMonoidHom = suzukiB m k ∧
        (B.subgroupOf K).map ψ.toMonoidHom = suzukiT m k ∧
        Nat.card (baseOrbit H K) = Nat.card Q ^ 2 + 1 ∧
        Q ≤ K ∧ (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k ∧
        ∃ T : Subgroup G, T ≤ H ⊓ K ∧ IsPGroup 2 T ∧
          (∀ S : Sylow 2 ↥(H ⊓ K), (S : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype = T) ∧
          Nat.card T = Nat.card Q ^ 2 ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
          Subgroup.normalizer (K : Set G) ⊓ H = T ⊔ B ∧ T ⊓ B = ⊥ ∧
          (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k ∧
          ((rightConjugate T t).subgroupOf K).map ψ.toMonoidHom =
            (suzukiU m k).map (MulAut.conj (suzukiWElt m k)).toMonoidHom ∧
          Q ≤ T ∧ T ≤ Subgroup.centralizer (Q : Set G) ∧ (∀ x ∈ T, x ^ 2 = 1 → x ∈ Q) ∧
          ∃ e : Multiplicative k ≃* Q, ∀ b : k,
            ((e (.ofAdd b) : Q) : G) = (ψ.symm (suzukiSElt m k 0 b) : G) := by
  intro B X K Q
  obtain ⟨T, hTM, hTp, hall, hBT, -, -, -, hNeq, hTB, -, -, hSzc, -⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hTcard, -⟩ := hSzc hSz
  obtain ⟨m, k, _, _, hk, hm, hQ, hKB, ψ, hψ₀, hψB, hψt, hdeg⟩ :=
    proper_pair_suzuki_data h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, hQK, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hinv := proper_pair_point_involutions h hcomm hbeta ht hproper
  have hTU := map_point_sylow_eq_suzukiU hk ψ hψ₀ hTM hTp (by rw [hTcard, hQ, hk])
  have hQZ := map_point_root_eq_suzukiZ0 hk ψ hψ₀ hinv
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  have hTK : T ≤ K := fun x hx => (hTM hx).2
  obtain ⟨hQT, hTQ, hsq⟩ := point_root_le_center_point_sylow hk ψ hTK hQK hTU hQZ
  obtain ⟨e, he⟩ := exists_point_root_coordinates hk ψ hQK hQZ
  exact ⟨m, k, inferInstance, inferInstance, hk, hm, hQ, hKB, ψ, hψ₀, hψB, hdeg, hQK, hQZ, T, hTM,
    hTp, hall, hTcard, hBT, hNeq, hTB, hTU, map_flip_point_sylow_eq hm hk ψ hTU htK hψt, hQT,
    hTQ, hsq, e, he⟩

omit [Finite G] in
theorem map_aligned_conj_eq {K A : Subgroup G} {P : Type*} [Group P] (ψ : K ≃* P) {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hbA : b ∈ Subgroup.normalizer (A : Set G)) :
    ((A.subgroupOf K).map ψ.toMonoidHom).map
        (ψ.symm.trans ((K.normalizerMonoidHom ⟨b, hbK⟩).trans ψ)).toMonoidHom =
      (A.subgroupOf K).map ψ.toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, mem_map_subgroupOf_iff, Subgroup.normalizerMonoidHom_apply_symm_apply_coe,
    Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  have hbA' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbA) (ψ.symm g : G))
  rw [inv_inv] at hbA'
  exact hbA'.symm

omit [Finite G] in
theorem mem_centralizer_hull_of_aligned
    {m : ℕ} {k : Type} [Field k] [Finite k] (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ (2 * m + 1)) {K T Q : Subgroup G} (ψ : K ≃* suzukiGroup m k)
    (hTU : (T.subgroupOf K).map ψ.toMonoidHom = suzukiU m k)
    (hQZ : (Q.subgroupOf K).map ψ.toMonoidHom = suzukiZ0 m k) {t : G}
    (hV : ((rightConjugate T t).subgroupOf K).map ψ.toMonoidHom =
      (suzukiU m k).map (MulAut.conj (suzukiWElt m k)).toMonoidHom)
    {b : G} (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbT : b ∈ Subgroup.normalizer (T : Set G))
    (hbT' : b ∈ Subgroup.normalizer (rightConjugate T t : Set G))
    (hbQ : b ∈ Subgroup.centralizer (Q : Set G)) :
    b ∈ Subgroup.centralizer (K : Set G) := by
  set φ := K.normalizerMonoidHom ⟨b, hbK⟩
  set γ : MulAut (suzukiGroup m k) := ψ.symm.trans (φ.trans ψ) with hγ
  have hγU : (suzukiU m k).map γ.toMonoidHom = suzukiU m k := by
    rw [← hTU]
    exact map_aligned_conj_eq ψ hbK hbT
  have hγV : ((suzukiU m k).map (MulAut.conj (suzukiWElt m k)).toMonoidHom).map γ.toMonoidHom =
      (suzukiU m k).map (MulAut.conj (suzukiWElt m k)).toMonoidHom := by
    rw [← hV]
    exact map_aligned_conj_eq ψ hbK hbT'
  have hγQ : ∀ c : k, γ (suzukiSElt m k 0 c) = suzukiSElt m k 0 c := fun c => by
    have hmem : (ψ.symm (suzukiSElt m k 0 c) : G) ∈ Q := by
      have h0 : suzukiSElt m k 0 c ∈ suzukiZ0 m k := (mem_suzukiZ0_iff hk).2 ⟨c, rfl⟩
      rw [← hQZ, Subgroup.mem_map_equiv] at h0
      exact h0
    have hφ : φ (ψ.symm (suzukiSElt m k 0 c)) = ψ.symm (suzukiSElt m k 0 c) := by
      refine Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change b * _ * b⁻¹ = _
      rw [← Subgroup.mem_centralizer_iff.mp hbQ _ hmem, mul_inv_cancel_right]
    change ψ (φ (ψ.symm (suzukiSElt m k 0 c))) = _
    rw [hφ, MulEquiv.apply_symm_apply]
  have hγ1 := suzuki_opposite_root_center_action_faithful hm hk γ hγU hγV hγQ
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have h1 := congrArg (fun α : MulAut (suzukiGroup m k) => α (ψ ⟨x, hx⟩)) hγ1
  simp only [hγ, MulAut.one_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq] at h1
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  change b * x * b⁻¹ = x at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

omit [Finite G] in
theorem hull_centralizer_le_pair_stabilizer {H : Subgroup G} {z : G}
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta) {u : G}
    (hreg : RegularComplementConclusion H z beta t u) :
    Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) ≤
      pairPointStabilizer H beta := by
  obtain ⟨-, hfix, -, -, -, -, -, hJΔ, -, -⟩ := hreg
  intro c hc
  have hα : rightCosetMk H 1 ∈ rightFixedSet H u := by
    rw [hfix]
    exact ⟨1, Subgroup.one_mem _, rfl⟩
  have hβ : beta ∈ rightFixedSet H u := by
    rw [hfix]
    exact ⟨t, minimalLocalFailureProperPair_flip_mem H z beta t, (flip_coset_eq H ht).symm⟩
  exact ⟨(mem_rightCosetStabilizer_iff H _ c).mpr (hJΔ c hc _ hα),
    (mem_rightCosetStabilizer_iff H _ c).mpr (hJΔ c hc _ hβ)⟩

omit [Finite G] in
theorem pair_stabilizer_le_normalizer_flip {H K T : Subgroup G} {z : G}
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta) (htK : t ∈ K)
    (hBK : pairPointStabilizer H beta ≤ Subgroup.normalizer (K : Set G))
    (hNT : Subgroup.normalizer (K : Set G) ⊓ H ≤ Subgroup.normalizer (T : Set G))
    {b : G} (hb : b ∈ pairPointStabilizer H beta) :
    b ∈ Subgroup.normalizer (rightConjugate T t : Set G) := by
  have hbt : b ∈ rightConjugate H t := by
    have h2 := hb.2
    rwa [flip_coset_eq H ht, rightCosetStabilizer_mk] at h2
  have hc : t * b * t⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    refine hNT ⟨?_, (mem_rightConjugate_iff' H t b).mp hbt⟩
    have htN : t ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer htK
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htN (hBK hb)) (Subgroup.inv_mem _ htN)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  rw [mem_rightConjugate_iff', mem_rightConjugate_iff', Subgroup.mem_normalizer_iff.mp hc]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem hull_centralizer_eq_of_exclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) =
      pairPointStabilizer H beta ⊓
        Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) := by
  obtain ⟨m, k, _, _, hk, hm, -, -, ψ, -, -, -, hQK, hQZ, T, -, -, -, -, hBT, hNeq, -, hTU, hV,
    -, -, -, -⟩ := proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨u, huB, hu⟩ := hBinv
  have hreg := proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht
    hproper hexcl huB hu
  obtain ⟨-, -, -, -, hBK, -, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  have htK := minimalLocalFailureProperPair_flip_mem H z beta t
  have hNT : Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G) ⊓ H ≤
      Subgroup.normalizer (T : Set G) := by
    rw [hNeq]
    exact sup_le Subgroup.le_normalizer hBT
  refine le_antisymm (le_inf (hull_centralizer_le_pair_stabilizer ht hreg)
    (Subgroup.centralizer_le hQK)) fun b hb => ?_
  exact mem_centralizer_hull_of_aligned hm hk ψ hTU hQZ hV (hBK hb.1) (hBT hb.1)
    (pair_stabilizer_le_normalizer_flip ht htK hBK hNT hb.1) hb.2

omit [Finite G] in
theorem point_centralizer_normalizer_eq {H K Q T B : Subgroup G}
    (hNeq : Subgroup.normalizer (K : Set G) ⊓ H = T ⊔ B)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : T ⊓ B = ⊥)
    (hTQ : T ≤ Subgroup.centralizer (Q : Set G)) (hTK : T ≤ K)
    (hJ : Subgroup.centralizer (K : Set G) = B ⊓ Subgroup.centralizer (Q : Set G)) :
    (H ⊓ Subgroup.centralizer (Q : Set G)) ⊓ Subgroup.normalizer (K : Set G) =
        T ⊔ Subgroup.centralizer (K : Set G) ∧
      T ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∧
      T ≤ Subgroup.centralizer (Subgroup.centralizer (K : Set G) : Set G) := by
  have hJB : Subgroup.centralizer (K : Set G) ≤ B := hJ ▸ inf_le_left
  refine ⟨?_, ?_, fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hy x (hTK hx)).symm⟩
  · apply SetLike.coe_injective
    rw [show (H ⊓ Subgroup.centralizer (Q : Set G)) ⊓ Subgroup.normalizer (K : Set G) =
        (Subgroup.normalizer (K : Set G) ⊓ H) ⊓ Subgroup.centralizer (Q : Set G) by
          ext x; simp only [Subgroup.mem_inf]; tauto,
      hNeq, Subgroup.coe_inf, Subgroup.coe_mul_of_right_le_normalizer_left T B hBT,
      ← Subgroup.mul_inf_assoc T B _ hTQ, ← hJ,
      Subgroup.coe_mul_of_right_le_normalizer_left T _ (hJB.trans hBT)]
  · exact eq_bot_iff.mpr ((inf_le_inf_left T hJB).trans hTB.le)

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
