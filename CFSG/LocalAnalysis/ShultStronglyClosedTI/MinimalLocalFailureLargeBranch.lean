module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLargeBranchComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCountBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePointIndexTwo

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem large_branch_excluded_of_conclusions
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
    (hinv : RootCentralizerInvolutionsConclusion H z beta t)
    (h2 : CentralSectionConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A)
    (h3 : FourSectionConclusion H z beta t A) (h4 : IndexDichotomyConclusion H z beta t A) :
    LargeBranchExcludedConclusion H z beta t A := by
  intro hidx
  have d : FinalHyps H z beta t :=
    ⟨h, hcomm, hsmallerR1, hbeta, ht, hproper, hker, hexcl, hroot, hinv⟩
  obtain ⟨-, -, -, hq4, ⟨e, hqe⟩, hBH, hXB, hXK, hXcyc, hXcard, -⟩ := d.point_data
  obtain ⟨-, -, hJB, hJM, hMB, -⟩ := d.core_data
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBinv, -, -, -, hsemi, -⟩ := hker
  obtain ⟨u, hu2, hJu, hinvA, -⟩ := h3
  obtain ⟨hAJ, -⟩ := h2.2 A hA
  obtain ⟨hAH, hAn, hQA, hAM, -⟩ := hA
  obtain ⟨-, hHMB, -, hRn, hMsq, -, hreg⟩ := h4.2 hidx
  have hMH := TwoCoreGrowth.pointTwoCoreImage_le H
  have hMn := TwoCoreGrowth.pointTwoCoreImage_normal H
  have huJ : u ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
    rw [← SetLike.mem_coe, hJu]
    exact Or.inr rfl
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have huA : u ∉ A := fun huA' => hu1 (by
    have hmem : u ∈ A ⊓ Subgroup.centralizer
        (minimalLocalFailureProperPairHull H z beta t : Set G) := ⟨huA', huJ⟩
    rwa [hAJ, Subgroup.mem_bot] at hmem)
  have hconj : ∀ v ∈ TwoCoreGrowth.pointTwoCoreImage H,
      v ∉ minimalLocalFailurePairActionPointHull H z → orderOf v = 2 →
        ∃ g ∈ H, g⁻¹ * v * g = u := by
    intro v hv hvQ hv2
    obtain ⟨b, hb, hb2, g, hg, hgv⟩ := hinv.2 v hv hvQ hv2
    have hbJ : b ∈ ((Subgroup.centralizer
        (minimalLocalFailureProperPairHull H z beta t : Set G) : Subgroup G) : Set G) :=
      hBinv b hb hb2
    rw [hJu] at hbJ
    rcases hbJ with rfl | rfl
    · rw [orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    · exact ⟨g, hg, hgv⟩
  have hCu : ∀ m ∈ TwoCoreGrowth.pointTwoCoreImage H, m * u = u * m →
      m ∈ A ⊔ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
    intro m hm hmu
    have hmem : m ∈ TwoCoreGrowth.pointTwoCoreImage H ⊓ Subgroup.centralizer ({u} : Set G) :=
      ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmu⟩
    rw [d.two_core_centralizer_J huJ hu1] at hmem
    exact sup_le_sup_right hQA.le _ hmem
  have hsq := LargeBranch.sq_mem_of_conj_involution hMH hMn hAM hAn hQA.le hJM hJu hu2 hinvA
    hRn hMsq hconj hCu
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := rightInvolutionCommutatorSubgroup t (pairOddCore H beta))
  have hgen : ∀ y ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
      ∃ k : ℕ, y = (g : G) ^ k := by
    intro y hy
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hg ⟨y, hy⟩) :
      (⟨y, hy⟩ : rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) ∈
        Submonoid.powers g)
    have hk' : g ^ k = ⟨y, hy⟩ := hk
    exact ⟨k, by rw [← Subgroup.coe_pow, hk']⟩
  have hq2 : 2 ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) := by
    have he : e ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqe
      omega
    rw [hqe]
    exact dvd_pow_self 2 he
  have hXodd : Odd (Nat.card (rightInvolutionCommutatorSubgroup t (pairOddCore H beta))) := by
    rw [hXcard]
    exact Nat.odd_iff.mpr (by omega)
  have hg1 : (g : G) ≠ 1 := by
    intro hg1
    have hbot : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨k, rfl⟩ := hgen y hy
      rw [hg1, one_pow]
    rw [hbot, Subgroup.card_bot] at hXcard
    omega
  have hgn : (g : G) ^ Nat.card (rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) = 1 :=
    by rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
  have hgu : (g : G) * u = u * g := Subgroup.mem_centralizer_iff.mp huJ g (hXK g.2)
  have hXn : ∀ b ∈ pairPointStabilizer H beta,
      b * (g : G) * b⁻¹ ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta) :=
    fun b hb => LargeBranch.conj_mem_of_normal hXB
      (TwoCoreGrowth.original_pair_commutator_normal h hbeta ht).2 hb g.2
  have hMR : ¬ TwoCoreGrowth.pointTwoCoreImage H ≤
      A ⊔ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
    intro hle
    rw [Subgroup.relIndex_eq_one.mpr hle] at hidx
    omega
  obtain ⟨k₀, _, _, hk₀, -, ι, hιker, -, hιX⟩ := hsemi
  have hk : Odd (Nat.card k₀ˣ) := by
    rw [Nat.card_units, hk₀, ← hXcard]
    exact hXodd
  have hJcard : Nat.card ι.ker = 2 := by
    rw [hιker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJB).toEquiv]
    change Nat.card ((Subgroup.centralizer
      (minimalLocalFailureProperPairHull H z beta t : Set G) : Subgroup G) : Set G) = 2
    rw [hJu, Nat.card_coe_set_eq, Set.ncard_pair hu1.symm]
  have hinl : (SemidirectProduct.inl :
      k₀ˣ →* k₀ˣ ⋊[LocalAnalysis.ComponentInitial.UnitaryHigher.ringAutUnits k₀] RingAut k₀).range ≤
        ι.range := hιX ▸ Subgroup.map_le_range ι _
  obtain ⟨B₀, hB₀⟩ := LargeBranch.exists_index_two_of_semilinear hk ι hJcard hinl
  obtain ⟨K₀, hK₀⟩ := LargeBranch.exists_index_two_of_large_branch hMH hMn hAM hAn hsq hBH
    hHMB.le hJM hJB hMB.le hJu huA hMR hXB g.2 hgen hg1 hXodd hgn hgu hXn hreg hB₀
  exact minimalLocalFailure_point_stabilizer_no_index_two_subgroup h K₀ hK₀

end CFSG.ShultStronglyClosedTI.FinalChain
