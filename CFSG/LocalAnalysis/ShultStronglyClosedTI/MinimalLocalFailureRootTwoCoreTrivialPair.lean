module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingPointKernel

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

theorem pCore_quotient_eq_bot {A : Type*} [Group A] (N : Subgroup A) [N.Normal]
    (hN2 : IsPGroup 2 N) (hcore : CFSG.pCore 2 A ≤ N) : CFSG.pCore 2 (A ⧸ N) = ⊥ := by
  set P := CFSG.pCore 2 (A ⧸ N) with hPdef
  set R := P.comap (QuotientGroup.mk' N) with hRdef
  have hR2 : IsPGroup 2 R := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := A ⧸ N)) ⟨_, hr⟩
    have hra : r ^ (2 ^ a) ∈ N := by
      have h1 : ((QuotientGroup.mk' N r) : A ⧸ N) ^ (2 ^ a) = 1 := by
        simpa using congrArg Subtype.val ha
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨b, hb⟩ := hN2 ⟨_, hra⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 : (r ^ (2 ^ a)) ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at h2
    simpa using h2
  have hRn : R.Normal := Subgroup.Normal.comap inferInstance _
  have hRN : R ≤ N := (show R ≤ CFSG.pCore 2 A from le_sSup ⟨hRn, hR2⟩).trans hcore
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hRN hx

variable {G : Type} [Group G]

theorem mem_pointClass_of_isConj {z r : G} (h : IsConj z r) : r ∈ involutionPointClass z := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by rw [← hc]; simp [rightConjugateElem]⟩

theorem isConj_of_mem_pointClass {z r : G} (h : r ∈ involutionPointClass z) : IsConj z r := by
  obtain ⟨g, rfl⟩ := h
  exact isConj_iff.mpr ⟨g⁻¹, by simp [rightConjugateElem]⟩

variable [Finite G]

theorem minimalLocalFailure_trivial_pair_two_core_forces_root_two_core_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hgrowth : TwoCoreInvolutionGrowthConclusion H z) :
    TrivialPairTwoCoreConclusion H z beta t := by
  unfold TrivialPairTwoCoreConclusion
  intro K Q J C M hJ2
  obtain ⟨-, htwo, -, -, -, hJeq, -, -, hJQ, -, -, -, hQM, -, hCM, -, -⟩ :=
    minimalLocalFailure_linear_point_kernel_and_odd_centralizers_of_conclusions h hcomm
      hsmallerR1 hbeta ht hproper hlin hexcl
  obtain ⟨hQ, -, hQclass, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hevencomm, hprodmem⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hQH, -, hQnormal, -, hQp, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  set B := pairPointStabilizer H beta with hBdef
  have hCM' : TwoCoreGrowth.pointTwoCoreImage C = M := hCM
  have hJeq' : J = B ⊓ Subgroup.centralizer (Q : Set G) := hJeq
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hMH : M ≤ H := TwoCoreGrowth.pointTwoCoreImage_le H
  have hMn := (Subgroup.normal_subgroupOf_iff hMH).mp (TwoCoreGrowth.pointTwoCoreImage_normal H)
  have hM2 : IsPGroup 2 M := TwoCoreGrowth.pointTwoCoreImage_isPGroup H
  have hMC : M ≤ C := by
    rw [← hCM']
    exact TwoCoreGrowth.pointTwoCoreImage_le C
  have hMB : M ⊓ B = ⊥ := by
    have hMBJ : M ⊓ B ≤ J := by
      rw [hJeq']
      exact fun m hm => ⟨hm.2, (hMC hm.1).2⟩
    have hn : ((M ⊓ B).subgroupOf J).Normal := by
      refine (Subgroup.normal_subgroupOf_iff hMBJ).mpr fun m g hm hg => ?_
      have hgB : g ∈ B := by
        rw [hJeq'] at hg
        exact hg.1
      exact ⟨hMn m g hm.1 (hBH hgB), B.mul_mem (B.mul_mem hgB hm.2) (B.inv_mem hgB)⟩
    have h2 : IsPGroup 2 ((M ⊓ B).subgroupOf J) :=
      (hM2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hMBJ).symm
    have hle : (M ⊓ B).subgroupOf J ≤ CFSG.pCore 2 J := le_sSup ⟨hn, h2⟩
    rw [hJ2, le_bot_iff] at hle
    apply le_bot_iff.mp
    intro m hm
    have hm' : (⟨m, hMBJ hm⟩ : J) ∈ (M ⊓ B).subgroupOf J := hm
    rw [hle, Subgroup.mem_bot] at hm'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hm')
  have hfix : ∀ m ∈ M, m ≠ 1 → ∀ g : G, g⁻¹ * m * g ∈ H → g ∈ H := by
    intro m hmM hm1 g hg
    by_contra hgH
    have hγ : rightCosetTranslate H (rightCosetMk H g⁻¹) m = rightCosetMk H g⁻¹ :=
      (translate_mk_fixed_iff H g⁻¹ m).mpr (by simpa only [inv_inv] using hg)
    have hγα : rightCosetMk H g⁻¹ ≠ rightCosetMk H 1 := fun h1 => hgH (by
      have h2 := (rightCosetMk_eq_iff H g⁻¹ 1).mp h1
      simpa only [one_mul, inv_inv] using h2)
    obtain ⟨k, hkα, hkβ⟩ := htwo (rightCosetMk H 1) beta (rightCosetMk H 1)
      (rightCosetMk H g⁻¹) hbeta.symm hγα.symm
    have hkH : k ∈ H := (translate_base_iff H k).mp hkα
    have hkβ' : rightCosetTranslate H beta (k * m * k⁻¹) = beta := by
      rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hkβ, hγ, ← hkβ,
        rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
    have hkm : k * m * k⁻¹ ∈ M ⊓ B :=
      ⟨hMn m k hmM hkH, (mem_rightCosetStabilizer_iff H _ _).mpr ((translate_base_iff H _).mpr
        (H.mul_mem (H.mul_mem hkH (hMH hmM)) (H.inv_mem hkH))),
        (mem_rightCosetStabilizer_iff H beta _).mpr hkβ'⟩
    rw [hMB, Subgroup.mem_bot] at hkm
    exact hm1 (by
      calc m = k⁻¹ * (k * m * k⁻¹) * k := by group
        _ = 1 := by rw [hkm]; group)
  have hstab : MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := MulAction.stabilizer_quotient H
  have hΩ : 1 < Nat.card (G ⧸ H) := Subgroup.one_lt_index_of_ne_top h.local_datum.proper
  have hQz : (Q : Set G) \ {1} = conjugacyWithin (MulAction.stabilizer G ((1 : G) : G ⧸ H)) z := by
    rw [hstab]
    exact hQclass
  have hAfix : ∀ a ∈ M, orderOf a = 2 → ∀ x : G ⧸ H, a • x = x ↔ x = ((1 : G) : G ⧸ H) := by
    intro a ha ha2 x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha2; omega
    have hainv : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha2
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq]
    constructor
    · intro hg
      have hg' : g⁻¹ * a * g ∈ H := by
        simpa only [mul_inv_rev, mul_assoc, hainv] using hg
      simpa using hfix a ha ha1 g hg'
    · intro hg
      have hgH : g ∈ H := by simpa using hg
      simpa only [mul_inv_rev, mul_assoc, hainv] using
        H.mul_mem (H.mul_mem (H.inv_mem hgH) (hMH ha)) hgH
  obtain ⟨hinvM, hcl⟩ :=
    InvolutionCounting.involution_class_counting_captures_point_kernel_involutions
      (MulAction.IsPretransitive.mk fun x y => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        exact ⟨b * a⁻¹, by rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right]⟩)
      hΩ ((1 : G) : G ⧸ H) hQ hQz
      (fun r s hr hs hrs => hevencomm r s (mem_pointClass_of_isConj hr)
        (mem_pointClass_of_isConj hs) hrs)
      (fun r s hr hs hne hrs => isConj_of_mem_pointClass (hprodmem r s
        (mem_pointClass_of_isConj hr) (mem_pointClass_of_isConj hs) hne hrs))
      hQM hAfix
  have hMQ : M = Q := by
    by_contra hne
    obtain ⟨-, m, hmM, hm2, hmQ⟩ := hgrowth (lt_of_le_of_ne hQM (Ne.symm hne))
    have hm : m ∈ {a : G | a ∈ M ∧ orderOf a = 2} := ⟨hmM, hm2⟩
    rw [hinvM] at hm
    exact hmQ hm.1
  refine ⟨hMQ, hcl, ?_⟩
  have hQQ : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hQ.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hQC : Q ≤ C := le_inf hQH hQQ
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  have hQCn : (Q.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (inf_le_left.trans hHQ)
  have h2 : IsPGroup 2 (Q.subgroupOf C) := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  refine ⟨hQCn, pCore_quotient_eq_bot (Q.subgroupOf C) h2 ?_⟩
  intro x hx
  have hxM : (x : G) ∈ TwoCoreGrowth.pointTwoCoreImage C := ⟨x, hx, rfl⟩
  rw [hCM', hMQ] at hxM
  exact hxM

end CFSG.ShultStronglyClosedTI.LinearChain
