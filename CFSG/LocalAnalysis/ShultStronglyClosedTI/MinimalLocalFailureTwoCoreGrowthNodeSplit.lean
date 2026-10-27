module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthNodeTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_not_normal_index_two {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (D : Subgroup G) [D.Normal]
    (hD : D.index = 2) : False := by
  obtain ⟨hsimple, a, b, hab⟩ := minimalLocalFailure_nonabelian_simple h
  rcases hsimple.eq_bot_or_eq_top_of_normal D with hbot | htop
  · rw [hbot, Subgroup.index_bot] at hD
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsCyclic G := isCyclic_of_prime_card hD
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact hab ((Commute.refl g).zpow_zpow i j).eq
  · rw [htop, Subgroup.index_top] at hD
    omega

theorem false_of_split_two_core {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1)
    (hQclass : (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} =
      conjugacyWithin H z)
    (hInv : ∀ m : G, m ∈ TwoCoreGrowth.pointTwoCoreImage H → orderOf m = 2 →
      m ∈ minimalLocalFailurePairActionPointHull H z)
    (hMB : TwoCoreGrowth.pointTwoCoreImage H ⊔ pairPointStabilizer H beta = H)
    (hBcyc : ∀ P : Subgroup G, P ≤ pairPointStabilizer H beta → IsPGroup 2 P → IsCyclic P)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) : False := by
  let Q := minimalLocalFailurePairActionPointHull H z
  let M := TwoCoreGrowth.pointTwoCoreImage H
  let B := pairPointStabilizer H beta
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have huH : u ∈ H := hBH huB
  have hu1 : u ≠ 1 := (orderOf_eq_prime_iff.mp hu).2
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hzS₀, hzcenter⟩ := h.central_sylow
  have hS₀H : (S₀ : Subgroup G) ≤ H := by
    intro s hs
    apply point_centralizer_le h.local_datum
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzcenter (⟨s, hs⟩ : (S₀ : Subgroup G))))
  have hutwo : IsPGroup 2 (Subgroup.zpowers (⟨u, huH⟩ : H)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hu
  obtain ⟨T, hT⟩ := hutwo.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (S₀.subtype hS₀H) T
  let S : Sylow 2 G := g • S₀
  have hSH : (S : Subgroup G) ≤ H := Sylow.smul_le hS₀H g
  have huS : u ∈ S := by
    have h1 : S.subtype hSH = T := (Sylow.smul_subtype hS₀H g).symm.trans hg
    have h2 : (⟨u, huH⟩ : H) ∈ (T : Subgroup H) := hT (Subgroup.mem_zpowers _)
    rw [← h1, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hMS : M ≤ (S : Subgroup G) := by
    intro m hm
    obtain ⟨mH, hmH, rfl⟩ := Subgroup.mem_map.mp hm
    have hcore : CFSG.pCore 2 H ≤ ((S.subtype hSH : Sylow 2 H) : Subgroup H) :=
      CFSG.pCore_isPGroup.le_sylow_of_normal _
    have hmS := hcore hmH
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmS
    exact hmS
  have hHM : H ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (TwoCoreGrowth.pointTwoCoreImage_le H)).mp
      (TwoCoreGrowth.pointTwoCoreImage_normal H)
  have hcyc : IsCyclic (S ⊓ B : Subgroup G) :=
    hBcyc _ inf_le_right (S.isPGroup'.to_le inf_le_left)
  have havoid : ∀ g : G, g⁻¹ * u * g ∉ M := by
    intro g hgM
    have hord : orderOf (g⁻¹ * u * g) = 2 :=
      (PairInvolutionFixedField.orderOf_conj_eq u g).trans hu
    have hQ' : g⁻¹ * u * g ∈ Q := hInv _ hgM hord
    have hne : g⁻¹ * u * g ≠ 1 := PairInvolutionFixedField.conj_ne_one hu1
    have hcl : g⁻¹ * u * g ∈ conjugacyWithin H z := by
      rw [← hQclass]
      exact ⟨hQ', hne⟩
    obtain ⟨k', hk'⟩ := hcl
    have hpc : g⁻¹ * u * g ∈ involutionPointClass z := ⟨(k' : G), hk'⟩
    have hupc : u ∈ involutionPointClass z := by
      have h1 := PairInvolutionFixedField.conj_mem_pointClass hpc g⁻¹
      have h2 : g⁻¹⁻¹ * (g⁻¹ * u * g) * g⁻¹ = u := by group
      rwa [h2] at h1
    have hα := (PairInvolutionFixedField.translate_base_iff H u).mpr huH
    have hβ := (mem_rightCosetStabilizer_iff H beta u).mp huB.2
    exact hbeta (PairInvolutionFixedField.class_fixed_unique h.local_datum hupc hβ hα)
  obtain ⟨D, hD, hDidx⟩ :=
    exists_normal_index_two_of_split_two_core S hSH hMS hHM hMB hcyc huS hu havoid
  exact minimalLocalFailure_not_normal_index_two h D hDidx

end CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode
