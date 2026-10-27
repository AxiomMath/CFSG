module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSectionInversion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSectionCosets
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCountBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearHullOvergroups
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSectionRegular

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.FinalChain.FourSection

variable {G : Type} [Group G] [Finite G]

theorem four_section_of_conclusions
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
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    FourSectionConclusion H z beta t A := by
  have d : FinalHyps H z beta t :=
    ⟨h, hcomm, hsmallerR1, hbeta, ht, hproper, hker, hexcl, hroot, hinv⟩
  obtain ⟨hQH, hQn, -, hQ4, -, hBH, hXB, hXK, -, hXcard, hfixX⟩ := d.point_data
  obtain ⟨-, -, hJB, -, hMB, -, -, hJQ, -⟩ := d.core_data
  obtain ⟨-, hJea, hJne, hJord⟩ := d.J_data
  obtain ⟨hlin, h2tr, -⟩ := hker
  obtain ⟨-, hall⟩ := h2
  obtain ⟨hAJ, hAcard, -, -, hAX, hAJφ, ψ, hψ, hψker, hψsurj, hψX⟩ := hall A hA
  obtain ⟨hAH, hAn, hQA, hAM, -, -, hsqA⟩ := hA
  obtain ⟨-, hXodd, -⟩ :=
    CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity h hcomm hsmallerR1
      hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, hXQu, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨T, -, -, -, -, -, -, -, -, -, -, hTlin, -, -⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  have hΩ := LinearChain.card_rightCosetSpace_of_conclusions h hcomm hsmallerR1 hbeta ht hproper
    hlin hexcl
  have hXH := hXB.trans hBH
  have hJH := hJB.trans hBH
  have htrans : ∀ ω, ω ≠ rightCosetMk H 1 → ∃ g ∈ H, rightCosetTranslate H beta g = ω := by
    intro ω hω
    obtain ⟨g, hg1, hg2⟩ := h2tr (rightCosetMk H 1) beta (rightCosetMk H 1) ω hbeta.symm
      (Ne.symm hω)
    exact ⟨g, (PairInvolutionFixedField.translate_base_iff H g).mp hg1, hg2⟩
  have hAB : A ⊓ pairPointStabilizer H beta = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have haJ : a ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
      rw [← hMB]
      exact ⟨hAM ha.1, ha.2⟩
    have haAJ : a ∈ A ⊓ Subgroup.centralizer
        (minimalLocalFailureProperPairHull H z beta t : Set G) := ⟨ha.1, haJ⟩
    rwa [hAJ] at haAJ
  have hfree : ∀ ω : rightCosetSpace H, ω ≠ rightCosetMk H 1 → ∀ a ∈ A,
      rightCosetTranslate H ω a = ω → a = 1 := fun ω hω a ha hfix =>
    eq_one_of_translate_eq hAH hAn hAB htrans hω ha hfix
  have hΛcard : Nat.card (orbitsOffBase H A) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) := by
    have hmul := card_orbitsOffBase_mul hAH hfree
    rw [hAcard, hΩ, Nat.add_sub_cancel] at hmul
    have hq0 : 0 < Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hq0
    rw [hmul]
    ring
  have hΛne : ∃ O ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta := by
    by_contra hne
    have hsub : orbitsOffBase H A ⊆ {rightOrbit H A beta} := fun O hO => by
      by_contra hO'
      exact hne ⟨O, hO, hO'⟩
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, hΛcard] at hle
    omega
  have hfreeX : ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
      ∀ O ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta → setTranslate H O x = O → x = 1 :=
    fun x hx O hO hOβ hOx => eq_one_of_setTranslate_eq hAH hAn hXH
      (fun x hx hx1 => (hAX x hx hx1).1) hfixX hx hO hOβ hOx
  have hcardΛX : Nat.card (orbitsOffBase H A) =
      Nat.card (rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) + 1 := by
    rw [hΛcard, hXcard]
    omega
  have hreg : ∀ O ∈ orbitsOffBase H A, ∀ O' ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta →
      O' ≠ rightOrbit H A beta →
        ∃! x : rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
          setTranslate H O x = O' :=
    fun O hO O' hO' hOβ hO'β =>
      existsUnique_setTranslate_eq hbeta hAH hAn hXB hfreeX hcardΛX hO hO' hOβ hO'β
  have hreg' : ∀ O ∈ orbitsOffBase H A, ∀ O' ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta →
      O' ≠ rightOrbit H A beta →
        ∃ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
          setTranslate H O x = O' := by
    intro O hO O' hO' hOβ hO'β
    obtain ⟨x, hx, -⟩ := hreg O hO O' hO' hOβ hO'β
    exact ⟨x, x.2, hx⟩
  have hJ2 : ∀ j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G),
      j * j = 1 := fun j hj => by
    rw [← pow_two]
    exact hJea.2 j hj
  have hJΛ : ∀ j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G),
      ∀ O ∈ orbitsOffBase H A, setTranslate H O j = O := fun j hj O hO =>
    setTranslate_eq_of_commute hAH hAn hXodd hfreeX hreg' (hJB hj) (hJ2 j hj)
      (fun x hx => Subgroup.mem_centralizer_iff.mp hj x (hXK hx)) hO
  have hXQ : ∀ a ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1},
      ∀ b ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1},
        ∃ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), x⁻¹ * a * x = b := by
    intro a ha b hb
    obtain ⟨x, hx, -⟩ := hXQu a ha b hb
    exact ⟨x, x.2, hx⟩
  have hJinv : ∀ j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G),
      j ≠ 1 → ∀ a ∈ A, j * a * j⁻¹ = a⁻¹ := by
    intro j hj hj1
    obtain ⟨hjB, hjord, -⟩ := d.localHull_J hj hj1
    obtain ⟨-, hFix, -⟩ := proper_pair_hull_regular_complement_of_conclusions h hcomm
      hsmallerR1 hbeta ht hproper hexcl hjB hjord
    have hcardFix : Nat.card (rightFixedSet H j) =
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by
      rw [hFix]
      exact (hTlin hlin).2
    obtain ⟨-, φ, hφ, hφker, hφsurj, hφX⟩ := hAJφ j hj hj1
    exact inv_of_fixes_orbits hbeta hAH hAn hQA.le hXH hfree hXQ hjB (hJ2 j hj)
      (fun c hc => Subgroup.mem_centralizer_iff.mp (hJQ hj) c hc) (hJΛ j hj) hcardFix hΛne
      φ hφ hφker hφsurj hφX ψ hψ hψker hψX
  obtain ⟨⟨u, huJ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJne
  have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hJset : (Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) :
      Set G) = {1, u} := by
    ext g
    constructor
    · intro hg
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · exact Or.inr (eq_of_ne_one_of_inv hQA hJinv (fun j hj hj1 => (hAJφ j hj hj1).1) hg hg1
          huJ hu1')
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact huJ
  have huinv := hJinv u huJ hu1'
  have hBu : ∀ b ∈ pairPointStabilizer H beta, b⁻¹ * u * b = u := by
    intro b hb
    have hconj := (d.conj_mem_J_iff huJ hu1' (hBH hb)).mpr (Subgroup.mem_sup_right hb)
    have hmem : b⁻¹ * u * b ∈ ((Subgroup.centralizer
        (minimalLocalFailureProperPairHull H z beta t : Set G) : Subgroup G) : Set G) := hconj
    rw [hJset] at hmem
    rcases hmem with h1 | h1
    · exfalso
      apply hu1'
      calc u = b * (b⁻¹ * u * b) * b⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hCu : ∀ g ∈ H, g⁻¹ * u * g = u →
      g ∈ minimalLocalFailurePairActionPointHull H z ⊔ pairPointStabilizer H beta :=
    fun g hg hgu => (d.conj_mem_J_iff huJ hu1' hg).mp (by rw [hgu]; exact huJ)
  have hsurjQ : ∀ y ∈ minimalLocalFailurePairActionPointHull H z, ∃ a ∈ A, a ^ 2 = y := by
    intro y hy
    obtain ⟨a, ha⟩ := hψsurj ⟨y, hy⟩
    exact ⟨a, a.2, (hψ a).symm.trans (congrArg Subtype.val ha)⟩
  have hΔstab : ∀ g ∈ H, conjSet (involutionCoset (minimalLocalFailurePairActionPointHull H z) u)
      g = involutionCoset (minimalLocalFailurePairActionPointHull H z) u ↔
        g ∈ A ⊔ pairPointStabilizer H beta := fun g hg =>
    conjSet_involutionCoset_eq_iff hQH hQn hQA.le hAH hAn hBH huinv hsqA hsurjQ hBu hCu hg
  obtain ⟨f, hbij, hfΔ, hequiv⟩ := exists_bijOn_conjugates hbeta hAH hAn htrans
    (fun g hg => (hΔstab g hg).trans (setTranslate_rightOrbit_eq_iff hAH hAn hg).symm)
  have hθ : ∀ g ∈ H, ∀ D ∈ cosetConjugates H (minimalLocalFailurePairActionPointHull H z) u,
      conjSet D g ∈ cosetConjugates H (minimalLocalFailurePairActionPointHull H z) u := by
    rintro g hg D ⟨h₀, hh₀, rfl⟩
    exact ⟨h₀ * g, H.mul_mem hh₀ hg, conjSet_mul _ _ _⟩
  have hΔθ : involutionCoset (minimalLocalFailurePairActionPointHull H z) u ∈
      cosetConjugates H (minimalLocalFailurePairActionPointHull H z) u :=
    ⟨1, H.one_mem, (conjSet_one _).symm⟩
  unfold FourSectionConclusion
  intro B X K Q J Λ
  refine ⟨u, hJord u huJ hu1', hJset, huinv, hΛcard,
    fun g hg O hO => setTranslate_mem_orbitsOffBase hAH hAn hg hO,
    two_transitive_orbitsOffBase hAH hAn htrans hXB hreg', hJΛ,
    fun x hx => setTranslate_rightOrbit_beta hAH hAn (hXB hx), hreg, ?_,
    (Nat.card_congr (hbij.equiv f)).trans hΛcard, ⟨f, hbij, hfΔ, hequiv⟩,
    fun D hD D' hD' hDΔ hD'Δ =>
      existsUnique_conjSet_eq hbij hfΔ hΔθ hequiv hθ hXH hreg hD hD' hDΔ hD'Δ, ?_⟩
  · ext g
    constructor
    · rintro ⟨hg, hgΔ⟩
      exact (hΔstab g hg).mp hgΔ
    · intro hg
      have hgH : g ∈ H := sup_le hAH hBH hg
      exact ⟨hgH, (hΔstab g hgH).mpr hg⟩
  · intro g hg D hD
    obtain ⟨a, ha, j, hj, rfl⟩ := exists_mul_of_mem_sup hAH hAn hJH hg
    refine conjSet_eq_of_fixes hbij hequiv hθ (H.mul_mem (hAH ha) (hJH hj)) (fun O hO => ?_) hD
    rw [← setTranslate_mul, setTranslate_eq_of_mem_orbitsOffBase hO ha, hJΛ j hj O hO]

end CFSG.ShultStronglyClosedTI.FinalChain
