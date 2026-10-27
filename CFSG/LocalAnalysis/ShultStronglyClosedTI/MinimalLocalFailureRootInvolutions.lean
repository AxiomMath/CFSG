module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClass
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingCosets
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement

public section

namespace CFSG.ShultStronglyClosedTI.LinearChain.RootInvolutions

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem exists_coset_mem_fixing_second_point {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {Q : Subgroup G} (hQ : IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, r ∈ involutionPointClass z → s ∈ involutionPointClass z →
      Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, r ∈ involutionPointClass z → s ∈ involutionPointClass z →
      r ≠ s → Commute r s → r * s ∈ involutionPointClass z)
    {w : G} (hwH : w ∈ H) (hw : orderOf w = 2) (hwQ : w ∉ Q) :
    ∃ q ∈ Q, ∃ γ : rightCosetSpace H, γ ≠ rightCosetMk H 1 ∧
      rightCosetTranslate H γ (w * q) = γ := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  have hbase : e (rightCosetMk H 1) = (QuotientGroup.mk 1 : G ⧸ H) := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  have hstab : MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ H) = H := baseCoset_stabilizer H
  have hΩ : 1 < Nat.card (G ⧸ H) := Subgroup.one_lt_index_of_ne_top h.proper
  obtain ⟨q, hq, β, hβ, hfix⟩ :=
    InvolutionCounting.all_class_counting_excludes_single_point_central_involution_cosets
      (MulAction.isPretransitive_quotient G H) hΩ (QuotientGroup.mk 1 : G ⧸ H) hQ
      (by rw [hstab]; exact hQclass) (point_fixed_coset_unique h)
      (fun r s hr hs hrs => heven r s (MixedClass.mem_pointClass_iff_isConj.mpr hr)
        (MixedClass.mem_pointClass_iff_isConj.mpr hs) hrs)
      (fun r s hr hs hne hrs => MixedClass.mem_pointClass_iff_isConj.mp
        (hprod r s (MixedClass.mem_pointClass_iff_isConj.mpr hr)
          (MixedClass.mem_pointClass_iff_isConj.mpr hs) hne hrs))
      (by rw [hstab]; exact hwH) hw hwQ
  refine ⟨q, hq, e.symm β, fun heq => hβ ?_, ?_⟩
  · rw [← e.apply_symm_apply β, heq, hbase]
  · apply (mem_rightCosetStabilizer_iff H _ _).mp
    change (w * q) • e (e.symm β) = e (e.symm β)
    rw [e.apply_symm_apply]
    exact hfix

theorem root_centralizer_involution_two_fixed_and_conj
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {v : G} (hvC : v ∈ H ⊓ Subgroup.centralizer
      (minimalLocalFailurePairActionPointHull H z : Set G))
    (hvQ : v ∉ minimalLocalFailurePairActionPointHull H z) (hv : orderOf v = 2) :
    (∃ ω₁ ω₂ : rightCosetSpace H, ω₁ ≠ ω₂ ∧ rightCosetTranslate H ω₁ v = ω₁ ∧
      rightCosetTranslate H ω₂ v = ω₂) ∧
    ∃ b ∈ pairPointStabilizer H beta, orderOf b = 2 ∧ ∃ k ∈ H, k⁻¹ * v * k = b := by
  obtain ⟨hQ, hQ4, hQclass, -, -, -, -, -, -, -, -, -, -, -, -, -, heven, hprod⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  set Q := minimalLocalFailurePairActionPointHull H z
  have hdatum := h.local_datum
  have htwo := MixedClass.ambient_two_transitive hdatum h.central_sylow hQ hQ4 hQclass
  have hQH : Q ≤ H := point_subgroup_le hdatum.distinguished_mem hQclass
  have hQnorm := point_subgroup_normalized hQclass
  have hsqQ : ∀ a ∈ Q, a * a = 1 := fun a ha => by rw [← sq]; exact hQ.2 a ha
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hvH : v ∈ H := hvC.1
  have hvcent : ∀ x ∈ Q, x * v = v * x := Subgroup.mem_centralizer_iff.mp hvC.2
  obtain ⟨q, hq, γ, hγ, hγfix⟩ :=
    exists_coset_mem_fixing_second_point hdatum hQ hQclass heven hprod hvH hv hvQ
  have haH : v * q ∈ H := H.mul_mem hvH (hQH hq)
  have haQ : ∀ x ∈ Q, x * (v * q) = v * q * x := fun x hx => by
    rw [← mul_assoc, hvcent x hx, mul_assoc, hQab x hx q hq, mul_assoc]
  have ha : orderOf (v * q) = 2 := by
    apply orderOf_eq_prime
    · have hv2 : v * v = 1 := by rw [← sq, ← hv, pow_orderOf_eq_one]
      calc (v * q) ^ 2 = v * (q * v) * q := by rw [sq]; simp only [mul_assoc]
        _ = (v * v) * (q * q) := by rw [hvcent q hq]; group
        _ = 1 := by rw [hv2, hsqQ q hq, one_mul]
    · intro h1
      apply hvQ
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Q.inv_mem hq
  obtain ⟨g, hgH, hgB⟩ := MixedClass.exists_conj_mem_pairPointStabilizer htwo hbeta haH hγ hγfix
  have ha' : orderOf (g * (v * q) * g⁻¹) = 2 := by
    have := orderOf_conj_eq (v * q) g⁻¹
    rwa [inv_inv, ha] at this
  have hQa' : Q ≤ Subgroup.centralizer ({g * (v * q) * g⁻¹} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx' : g⁻¹ * x * g ∈ Q := hQnorm g hgH x hx
    calc x * (g * (v * q) * g⁻¹) = g * ((g⁻¹ * x * g) * (v * q)) * g⁻¹ := by group
      _ = g * ((v * q) * (g⁻¹ * x * g)) * g⁻¹ := by rw [haQ _ hx']
      _ = g * (v * q) * g⁻¹ * x := by group
  have hcoset := MixedClass.coset_subset_class_of_centralizing h hcomm hsmallerR1 hbeta ht
    hproper hgB ha' hQa'
  have hgq : g * q * g⁻¹ ∈ Q := by
    simpa only [inv_inv] using hQnorm g⁻¹ (H.inv_mem hgH) q hq
  have hvclass : v ∈ involutionPointClass (g * (v * q) * g⁻¹) := by
    have h1 := conj_mem_pointClass (hcoset (g * q * g⁻¹) hgq) g
    have h2 : g⁻¹ * (g * (v * q) * g⁻¹ * (g * q * g⁻¹)) * g = v := by
      calc g⁻¹ * (g * (v * q) * g⁻¹ * (g * q * g⁻¹)) * g = v * (q * q) := by group
        _ = v := by rw [hsqQ q hq, mul_one]
    rwa [h2] at h1
  obtain ⟨δ, hδ, hδfix⟩ := MixedClass.exists_second_fixed_of_mem_class hbeta hgB hvclass
  refine ⟨⟨rightCosetMk H 1, δ, hδ.symm, (translate_base_iff H v).mpr hvH, hδfix⟩, ?_⟩
  obtain ⟨k, hkH, hkB⟩ := MixedClass.exists_conj_mem_pairPointStabilizer htwo hbeta hvH hδ hδfix
  refine ⟨k * v * k⁻¹, hkB, ?_, k⁻¹, H.inv_mem hkH, by rw [inv_inv]⟩
  have := orderOf_conj_eq v k⁻¹
  rwa [inv_inv, hv] at this

theorem minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t) :
    FinalChain.RootCentralizerInvolutionsConclusion H z beta t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQM, -, -, -⟩ := hker
  unfold FinalChain.RootCentralizerInvolutionsConclusion
  intro B Q C
  have hfirst : ∀ v ∈ C, v ∉ Q → orderOf v = 2 →
      (∃ ω₁ ω₂ : rightCosetSpace H, ω₁ ≠ ω₂ ∧ rightCosetTranslate H ω₁ v = ω₁ ∧
        rightCosetTranslate H ω₂ v = ω₂) ∧
      ∃ b ∈ B, orderOf b = 2 ∧ ∃ k ∈ H, k⁻¹ * v * k = b := fun v hvC hvQ hv =>
    root_centralizer_involution_two_fixed_and_conj h hcomm hsmallerR1 hbeta ht hproper hvC hvQ hv
  refine ⟨hfirst, fun v hvM hvQ hv => (hfirst v ⟨TwoCoreGrowth.pointTwoCoreImage_le H hvM,
    Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩ hvQ hv).2⟩
  exact (Subgroup.mem_centralizer_iff.mp (hQM hx) v hvM).symm

end CFSG.ShultStronglyClosedTI.LinearChain.RootInvolutions
