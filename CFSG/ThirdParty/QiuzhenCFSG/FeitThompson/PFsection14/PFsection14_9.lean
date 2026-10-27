module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_9_Correction

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.9)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.9) -/


public theorem section14_theorem_14_9_late_type_T1_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          section14_theorem_14_9_late_type_T1SourceData η Γ p q v := by
  intro hctx h143 hLateType hNotation hGap
  rcases hGap with
    ⟨_hSupp, _hSuppA0, _hβClass, _hNormβ, _hβτ, _hη01, _hΓ, _hAllK, hΓorth,
      hΓreal, hΓvirt, hΓdecomp, hDecomp⟩
  have hGapForSource :
      section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
        βS₁ βτ Γ X Y η01 p q u :=
    ⟨_hSupp, _hSuppA0, _hβClass, _hNormβ, _hβτ, _hη01, _hΓ, _hAllK, hΓorth,
      hΓreal, hΓvirt, hΓdecomp, hDecomp⟩
  exact section14_theorem_14_9_late_type_T1SourceData_of_imageDeltaSourceData
    Tmax τT hΓvirt hΓreal hΓorth
    (section14_theorem_14_9_late_type_T1_image_delta_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT Lfam RL
      τL τL₁ φ μ01 ν10 βS βT βL ω η μ ν μsum νsum δ δ' σ
      βS₁ βτ Γ X Y η01 p q u v c d hctx h143 hLateType hNotation
      hGapForSource)

public theorem section14_theorem_14_9_late_type_T1Contribution_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          section14_theorem_14_9_late_type_T1ContributionData η Γ p q v := by
  intro hctx h143 hLateType hNotation hGap
  exact section14_theorem_14_9_late_type_T1ContributionData_of_sourceData
    (section14_theorem_14_9_late_type_T1_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT Lfam RL
      τL τL₁ φ μ01 ν10 βS βT βL ω η μ ν μsum νsum δ δ' σ
      βS₁ βτ Γ X Y η01 p q u v c d hctx h143 hLateType hNotation hGap)

public theorem section14_theorem_14_9_late_type_norm_lower_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS₁ : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
            βS₁ βτ Γ X Y η01 p q u →
          ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ Section5.cfNormSq Y := by
  intro hctx h143 hLateType hNotation hGap
  rcases hGap with
    ⟨_hSupp, _hSuppA0, _hβClass, _hNormβ, _hβτ, _hη01, _hΓ, _hAllK, _hΓorth,
      _hΓreal, _hΓvirt, hΓdecomp, hDecomp⟩
  have hGapForSource :
      section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
        βS₁ βτ Γ X Y η01 p q u :=
    ⟨_hSupp, _hSuppA0, _hβClass, _hNormβ, _hβτ, _hη01, _hΓ, _hAllK, _hΓorth,
      _hΓreal, _hΓvirt, hΓdecomp, hDecomp⟩
  rcases hDecomp with ⟨hXspan, _hYeta⟩
  rcases section14_theorem_14_9_late_type_T1Contribution_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      ω η μ ν μsum νsum δ δ' σ βS₁ βτ Γ X Y η01 p q u v c d
      hctx h143 hLateType hNotation hGapForSource with
    ⟨T1, hcard, hself, horthNe, hηorth, hΓcoeff⟩
  have hYcoeff : ∀ χ ∈ T1,
      (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G Y χ) := by
    intro χ hχ
    have hXχ : Section1.scalarProduct G X χ = 0 :=
      section14_eta_span_scalarProduct_left_eq_zero hXspan
        (fun i k hi hk => hηorth χ hχ i k hi hk)
    have hYeq : Section1.scalarProduct G Y χ =
        Section1.scalarProduct G Γ χ := by
      symm
      rw [hΓdecomp, Section1.scalarProduct_add_left, hXχ, zero_add]
    simpa [hYeq] using hΓcoeff χ hχ
  exact hcard.trans
    (section14_finset_orthonormal_coeff_lower_card_le_cfNormSq
      T1 hself horthNe Y hYcoeff)

public theorem section14_theorem_14_9_late_type_ratio_le_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        (Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) →
          ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤
            ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
  intro hctx h143 hLateType
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation,
      _hChoice, _hMin⟩
  rcases hNotation with
    ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ, hNotationFor⟩
  let βS₁ : Section1.ClassFunction Smax :=
    Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1
  let βτ : Section1.ClassFunction G := τS βS₁
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, hqPrime⟩
  have hβhyp : Section13.theorem_13_18_hypothesis Smax P W1 (μ 0 1) βS₁ 1 p := by
    refine ⟨by norm_num, hp.one_lt, ?_⟩
    simp [βS₁, Section7.principalInducedCharacter]
  have hβS₁Class : Section1.IsClassFunction βS₁ := by
    have hprincipalClass :
        Section1.IsClassFunction (Section7.principalInducedCharacter Smax (P ⊔ W1)) := by
      unfold Section7.principalInducedCharacter
      exact Section1.inducedCF_isClassFunction ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
    have hμClass : Section1.IsClassFunction (μ 0 1) := by
      rcases hNotationFor with
        ⟨_hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr,
          _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
          _hμsum, _hνsum⟩
      exact section14_isClassFunction_of_irreducibleCharacterOnGroup
        (hμirr 0 1 hqPrime.pos hp.one_lt)
    intro x g
    simp [βS₁, Pi.sub_apply, hprincipalClass x g, hμClass x g]
  rcases Section13.theorem_13_18
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS₁ βτ 1 p q u v c d
      hctx.1 hNotationFor hβhyp rfl with
    ⟨Γ, X, Y, η01, hSupp, hSuppA0, hNormβ, hη01, hΓ, hAllK,
      hΓorth, hΓreal, hΓvirt, hΓdecomp, hDecomp, hUpper⟩
  have hGap :
      section14_theorem_14_9_bridgeGapData Smax W W1 W2 P τS η
        βS₁ βτ Γ X Y η01 p q u :=
    ⟨hSupp, hSuppA0, hβS₁Class, hNormβ, rfl, hη01, hΓ, hAllK, hΓorth, hΓreal,
      hΓvirt, hΓdecomp, hDecomp⟩
  have hLower :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ Section5.cfNormSq Y :=
    section14_theorem_14_9_late_type_norm_lower_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      ω η μ ν μsum νsum δ δ' σ βS₁ βτ Γ X Y η01 p q u v c d
      hctx h143 hLateType hNotationFor hGap
  exact hLower.trans hUpper

public theorem section14_theorem_14_9_late_type_source_contradiction_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        ¬ section16TypeII Tmax Q →
          (Section8.typeIIIDefinitionData Tmax Q ∨
            Section8.typeIVDefinitionData Tmax Q ∨
              Section8.typeVDefinitionData Tmax Q) →
            False := by
  intro hctx h143 hnotTypeII hLateType
  have _hnotTypeII := hnotTypeII
  have hle :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) :=
    section14_theorem_14_9_late_type_ratio_le_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
      hctx h143 hLateType
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
  have h2q : 2 < q := section14_theorem_14_7_two_lt_q_of_sourceData hctx
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII_of_qp, _hUcomm, _hUfrob, _hPelem,
      _hPcard, hu, _hSfamCoh, _hTI, _hTauS, _hnorm⟩
  rcases section14_theorem_14_4_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨_hcaseB, hv⟩
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    section14_pow_gt_pow_of_prime_lt hp hq h2q hctx.2
  have hgt :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) :=
    section14_ratio_ineq_of_bounds hp hq h2q hctx.2 hu hv hpow
  exact (not_le_of_gt hgt) hle

public theorem section14_theorem_14_9_not_typeII_contradiction_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        ¬ section16TypeII Tmax Q →
          False := by
  intro hctx h143 hnotTypeII
  have hTSourceType :
      Section8.typeIIDefinitionData Tmax Q ∨
        Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q :=
    section14_Tmax_source_type_alternative_of_sourceData hctx.1
  -- Textbook PF `(14.9)` assumes a non-Type-II alternative for `Tmax`,
  -- derives `(v - 1) / p ≤ (u - 1) / q` from the Type III character
  -- argument, and contradicts PF `(14.8)`.
  rcases hTSourceType with hTypeII | hLateType
  · exact section14_theorem_14_9_source_typeII_contradiction hctx hTypeII hnotTypeII
  · exact section14_theorem_14_9_late_type_source_contradiction_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
      hctx h143 hnotTypeII hLateType

public theorem section14_theorem_14_9_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        section16TypeII Tmax Q := by
  intro hctx h143
  by_contra hnotTypeII
  exact section14_theorem_14_9_not_typeII_contradiction_bridge
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
    hctx h143 hnotTypeII


end CFSG.Section14
