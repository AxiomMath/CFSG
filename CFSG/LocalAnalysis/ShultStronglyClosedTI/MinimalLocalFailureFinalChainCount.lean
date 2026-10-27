module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCountBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem card_point (d : FinalHyps H z beta t) :
    Nat.card H = Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 *
      Nat.card (pairPointStabilizer H beta) := by
  obtain ⟨-, -, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hBidx⟩ := d.core_data
  have h := Subgroup.relIndex_mul_card (H := pairPointStabilizer H beta) (K := H)
  rw [inf_eq_left.mpr hBH, hBidx] at h
  exact h.symm

theorem card_point_sup_pair (d : FinalHyps H z beta t) :
    Nat.card (minimalLocalFailurePairActionPointHull H z ⊔ pairPointStabilizer H beta :
      Subgroup G) = Nat.card (minimalLocalFailurePairActionPointHull H z) *
        Nat.card (pairPointStabilizer H beta) := by
  obtain ⟨hQH, hQn, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨-, -, -, -, -, -, -, -, -, hQB, -⟩ := d.core_data
  exact card_eq_mul_of_semidirect rfl hQB (normal_subgroupOf_of_le (sup_le hQH hBH) hQn)

theorem card_conjugacyWithin_J
    (d : FinalHyps H z beta t) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    Nat.card (conjugacyWithin H j) = Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 *
      Nat.card (conjugacyWithin (pairPointStabilizer H beta) j) := by
  obtain ⟨hQH, hQn, -, hQ4, -, hBH, -⟩ := d.point_data
  obtain ⟨-, -, -, -, -, -, -, -, -, hQB, -⟩ := d.core_data
  obtain ⟨hjB, -, -⟩ := d.localHull_J hj hj1
  have h1 := card_conjugacyWithin_mul (H := H) (hBH hjB)
  have h2 := card_conjugacyWithin_mul (H := pairPointStabilizer H beta) hjB
  have hPC := d.point_centralizer_J hj hj1
  have h3 : Nat.card (H ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) *
        Nat.card (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({j} : Set G) :
          Subgroup G) := by
    refine card_eq_mul_of_semidirect hPC ?_ ?_
    · exact le_bot_iff.mp (hQB ▸ inf_le_inf_left _ inf_le_left)
    · exact normal_subgroupOf_of_le inf_le_left hQn
  have h4 := d.card_point
  have hc : 0 < Nat.card (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({j} : Set G) :
      Subgroup G) := Nat.card_pos
  rw [h3] at h1
  generalize Nat.card (minimalLocalFailurePairActionPointHull H z) = q at *
  generalize Nat.card (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({j} : Set G) :
    Subgroup G) = c at *
  generalize Nat.card (conjugacyWithin H j) = a at *
  generalize Nat.card (conjugacyWithin (pairPointStabilizer H beta) j) = b at *
  generalize Nat.card (pairPointStabilizer H beta) = nB at *
  generalize Nat.card H = nH at *
  subst h4 h2
  have hq : 0 < q := by omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hq hc)
  rw [h1]
  ring

theorem card_involutions_outside
    (d : FinalHyps H z beta t) {U : Subgroup G} (hUH : U ≤ H)
    (hUn : (U.subgroupOf H).Normal)
    (hUM : U ≤ TwoCoreGrowth.pointTwoCoreImage H) :
    Nat.card {v : G | v ∈ U ∧ orderOf v = 2 ∧ v ∉ minimalLocalFailurePairActionPointHull H z} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 *
        (Nat.card (U ⊓ Subgroup.centralizer
          (minimalLocalFailureProperPairHull H z beta t : Set G) : Subgroup G) - 1) := by
  classical
  obtain ⟨hQH, hQn, -, hQ4, -, hBH, -⟩ := d.point_data
  obtain ⟨-, hM, -, hJM, hMB, -, hQJ, -, -, hQB, -⟩ := d.core_data
  obtain ⟨-, -, -, hord⟩ := d.J_data
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set J := Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)
    with hJdef
  set T : Subgroup G := U ⊓ J with hTdef
  let S : Set G := {v : G | v ∈ U ∧ orderOf v = 2 ∧ v ∉ Q}
  let Ts : Set G := (T : Set G) \ {1}
  have hUconj : ∀ g ∈ H, ∀ v ∈ U, g⁻¹ * v * g ∈ U := by
    intro g hg v hv
    have := hUn.conj_mem ⟨v, hUH hv⟩ hv ⟨g⁻¹, H.inv_mem hg⟩
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] using
      this
  have hQconj : ∀ g ∈ H, ∀ v ∈ Q, g⁻¹ * v * g ∈ Q := by
    intro g hg v hv
    have := hQn.conj_mem ⟨v, hQH hv⟩ hv ⟨g⁻¹, H.inv_mem hg⟩
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] using
      this
  have hmapS : ∀ (p : H × Ts), ((p.1 : G)⁻¹ * p.2 * p.1) ∈ S := by
    rintro ⟨⟨h, hh⟩, ⟨j, ⟨hjU, hjJ⟩, hj1⟩⟩
    refine ⟨hUconj h hh j hjU, ?_, ?_⟩
    · rw [orderOf_conj_eq]
      exact hord j hjJ hj1
    · intro hQ
      apply hj1
      have hjQ : j ∈ Q := by
        have := hQconj h⁻¹ (H.inv_mem hh) _ hQ
        simpa only [inv_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using this
      have : j ∈ Q ⊓ J := ⟨hjQ, hjJ⟩
      rwa [hQJ, Subgroup.mem_bot] at this
  let Φ : H × Ts → S := fun p => ⟨(p.1 : G)⁻¹ * p.2 * p.1, hmapS p⟩
  have hsurj : ∀ v : S, ∃ p : H × Ts, Φ p = v := by
    rintro ⟨v, hvU, hv2, hvQ⟩
    have hvC : v ∈ H ⊓ Subgroup.centralizer (Q : Set G) := hM ▸ hUM hvU
    obtain ⟨b, hbB, hb2, g, hg, hgb⟩ := (d.inv.1 v hvC hvQ hv2).2
    have hbU : b ∈ U := hgb ▸ hUconj g hg v hvU
    have hbJ : b ∈ J := hMB ▸ ⟨hUM hbU, hbB⟩
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    refine ⟨(⟨g⁻¹, H.inv_mem hg⟩, ⟨b, ⟨hbU, hbJ⟩, hb1⟩), Subtype.ext ?_⟩
    change (g⁻¹)⁻¹ * b * g⁻¹ = v
    rw [← hgb]
    group
  have hfiber : ∀ v : S, Nat.card {p : H × Ts // Φ p = v} =
      Nat.card (Q ⊔ pairPointStabilizer H beta : Subgroup G) := by
    intro v
    obtain ⟨⟨⟨h₀, hh₀⟩, ⟨j₀, ⟨hj₀U, hj₀J⟩, hj₀1⟩⟩, hp₀⟩ := hsurj v
    have hv : (v : G) = h₀⁻¹ * j₀ * h₀ := (congrArg Subtype.val hp₀).symm
    have hj₀1' : j₀ ≠ 1 := hj₀1
    have hfwd : ∀ p : {p : H × Ts // Φ p = v},
        h₀ * (p.1.1 : G)⁻¹ ∈ Q ⊔ pairPointStabilizer H beta := by
      rintro ⟨⟨⟨h, hh⟩, ⟨j, ⟨hjU, hjJ⟩, hj1⟩⟩, hp⟩
      have hpv : h⁻¹ * j * h = (v : G) := congrArg Subtype.val hp
      apply (d.conj_mem_J_iff hj₀J hj₀1' (H.mul_mem hh₀ (H.inv_mem hh))).mp
      have : (h₀ * h⁻¹)⁻¹ * j₀ * (h₀ * h⁻¹) = j := by
        calc (h₀ * h⁻¹)⁻¹ * j₀ * (h₀ * h⁻¹) = h * (h₀⁻¹ * j₀ * h₀) * h⁻¹ := by group
          _ = h * (h⁻¹ * j * h) * h⁻¹ := by rw [← hv, hpv]
          _ = j := by group
      rw [this]
      exact hjJ
    have hbwdH : ∀ g ∈ Q ⊔ pairPointStabilizer H beta, g ∈ H := fun g hg => sup_le hQH hBH hg
    have hbwdT : ∀ g ∈ Q ⊔ pairPointStabilizer H beta, g⁻¹ * j₀ * g ∈ Ts := by
      intro g hg
      refine ⟨⟨hUconj g (hbwdH g hg) j₀ hj₀U,
        (d.conj_mem_J_iff hj₀J hj₀1' (hbwdH g hg)).mpr hg⟩, ?_⟩
      intro h1
      apply hj₀1'
      have h1' : g⁻¹ * j₀ * g = 1 := h1
      calc j₀ = g * (g⁻¹ * j₀ * g) * g⁻¹ := by group
        _ = 1 := by rw [h1']; group
    refine Nat.card_congr
      { toFun := fun p => ⟨h₀ * (p.1.1 : G)⁻¹, hfwd p⟩
        invFun := fun g => ⟨(⟨(g : G)⁻¹ * h₀, H.mul_mem (H.inv_mem (hbwdH g g.2)) hh₀⟩,
            ⟨(g : G)⁻¹ * j₀ * g, hbwdT g g.2⟩), Subtype.ext ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · change ((g : G)⁻¹ * h₀)⁻¹ * ((g : G)⁻¹ * j₀ * g) * ((g : G)⁻¹ * h₀) = v
      rw [hv]
      group
    · rintro ⟨⟨⟨h, hh⟩, ⟨j, hjT⟩⟩, hp⟩
      have hpv : h⁻¹ * j * h = (v : G) := congrArg Subtype.val hp
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change (h₀ * h⁻¹)⁻¹ * h₀ = h
        group
      · apply Subtype.ext
        change (h₀ * h⁻¹)⁻¹ * j₀ * (h₀ * h⁻¹) = j
        calc (h₀ * h⁻¹)⁻¹ * j₀ * (h₀ * h⁻¹) = h * (h₀⁻¹ * j₀ * h₀) * h⁻¹ := by group
          _ = h * (h⁻¹ * j * h) * h⁻¹ := by rw [← hv, hpv]
          _ = j := by group
    · rintro ⟨g, hg⟩
      apply Subtype.ext
      change h₀ * ((g : G)⁻¹ * h₀)⁻¹ = g
      group
  have : Fintype S := Fintype.ofFinite S
  have hsigma : Nat.card (H × Ts) = Nat.card S *
      Nat.card (Q ⊔ pairPointStabilizer H beta : Subgroup G) := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv Φ).symm, Nat.card_sigma]
    simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rw [Nat.card_prod, PairInvolutionFixedField.card_diff_one, d.card_point,
    d.card_point_sup_pair] at hsigma
  have hB : 0 < Nat.card (pairPointStabilizer H beta) := Nat.card_pos
  have hq : 0 < Nat.card Q := by omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hq hB)
  calc Nat.card S * (Nat.card Q * Nat.card (pairPointStabilizer H beta))
      = Nat.card Q ^ 3 * Nat.card (pairPointStabilizer H beta) * (Nat.card T - 1) := hsigma.symm
    _ = Nat.card Q ^ 2 * (Nat.card T - 1) *
        (Nat.card Q * Nat.card (pairPointStabilizer H beta)) := by ring

theorem card_involutions
    (d : FinalHyps H z beta t) {U : Subgroup G} (hUH : U ≤ H)
    (hUn : (U.subgroupOf H).Normal) (hQU : minimalLocalFailurePairActionPointHull H z ≤ U)
    (hUM : U ≤ TwoCoreGrowth.pointTwoCoreImage H) :
    Nat.card {u : U // orderOf u = 2} =
        Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 +
          Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 *
            (Nat.card (U ⊓ Subgroup.centralizer
              (minimalLocalFailureProperPairHull H z beta t : Set G) : Subgroup G) - 1) ∧
      (U ⊓ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) = ⊥ →
        {u : G | u ∈ U ∧ orderOf u = 2} =
          (minimalLocalFailurePairActionPointHull H z : Set G) \ {1}) := by
  obtain ⟨-, -, hQ, -⟩ := d.point_data
  have hout := d.card_involutions_outside hUH hUn hUM
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  let S : Set G := {v : G | v ∈ U ∧ orderOf v = 2 ∧ v ∉ Q}
  have hQinv : ∀ y ∈ Q, y ≠ 1 → orderOf y = 2 := fun y hy hy1 =>
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    orderOf_eq_prime_iff.mpr ⟨hQ.2 y hy, hy1⟩
  have hunion : {u : G | u ∈ U ∧ orderOf u = 2} = ((Q : Set G) \ {1}) ∪ S := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff, S]
    constructor
    · rintro ⟨hvU, hv2⟩
      by_cases hvQ : v ∈ Q
      · refine Or.inl ⟨hvQ, ?_⟩
        rintro rfl
        rw [orderOf_one] at hv2
        exact absurd hv2 (by norm_num)
      · exact Or.inr ⟨hvU, hv2, hvQ⟩
    · rintro (⟨hvQ, hv1⟩ | ⟨hvU, hv2, -⟩)
      · exact ⟨hQU hvQ, hQinv v hvQ hv1⟩
      · exact ⟨hvU, hv2⟩
  have hdisj : Disjoint ((Q : Set G) \ {1}) S := by
    rw [Set.disjoint_left]
    rintro v ⟨hvQ, -⟩ ⟨-, -, hvQ'⟩
    exact hvQ' hvQ
  have hcardU : Nat.card {u : U // orderOf u = 2} = Nat.card {u : G | u ∈ U ∧ orderOf u = 2} :=
    Nat.card_congr
      { toFun := fun u => ⟨u.1, u.1.2, by rw [Subgroup.orderOf_coe]; exact u.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, by rw [← Subgroup.orderOf_coe]; exact v.2.2⟩
        left_inv := fun u => rfl
        right_inv := fun v => rfl }
  have hcardS : Nat.card {u : G | u ∈ U ∧ orderOf u = 2} =
      Nat.card ((Q : Set G) \ {1} : Set G) + Nat.card S := by
    rw [hunion, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  refine ⟨?_, fun hbot => ?_⟩
  · rw [hcardU, hcardS, PairInvolutionFixedField.card_diff_one, hout]
  · have h0 : Nat.card S = 0 := by
      have := hout
      rw [hbot, Subgroup.card_bot, Nat.sub_self, mul_zero] at this
      exact this
    have hS : S = ∅ := by
      have := (Set.ncard_eq_zero (Set.toFinite S)).mp (by rw [← Nat.card_coe_set_eq]; exact h0)
      exact this
    rw [hunion, hS, Set.union_empty]

end FinalHyps

theorem involution_count_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t)
    (hinv : RootCentralizerInvolutionsConclusion H z beta t) :
    InvolutionCountConclusion H z beta t := by
  have d : FinalHyps H z beta t :=
    ⟨h, hcomm, hsmallerR1, hbeta, ht, hproper, hker, hexcl, hroot, hinv⟩
  obtain ⟨-, hM, -, -, hMB, -, hQJ, hJQ, -⟩ := d.core_data
  obtain ⟨-, hEA, hJne, -⟩ := d.J_data
  exact ⟨hM, hJne, hEA, hMB, hQJ, hJQ, fun j hj hj1 => d.two_core_centralizer_J hj hj1,
    fun x hx hx1 => d.two_core_centralizer_X hx hx1,
    fun j hj hj1 k hk _ => d.conjugacyWithin_J_iff hj hj1 hk,
    fun j hj hj1 => d.card_conjugacyWithin_J hj hj1,
    fun U hUH hUn hQU hUM => d.card_involutions hUH hUn hQU hUM⟩

end CFSG.ShultStronglyClosedTI.FinalChain
