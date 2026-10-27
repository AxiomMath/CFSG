module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_9_Delta
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.9), calT construction
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

@[expose] public def section14_theorem_14_9_late_type_T1RawImageDeltaSourceData
    {G : Type u} [Group G] [Finite G]
    (Tmax W : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (p v : ℕ) : Prop :=
  ∃ (T1T : Finset (Section1.ClassFunction Tmax))
    (τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G),
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
      (∀ ζ ∈ T1T, Section1.scalarProduct Tmax ζ ζ = 1) ∧
      (∀ ζ ∈ T1T, ∀ ξ ∈ T1T, ζ ≠ ξ →
        Section1.scalarProduct Tmax ζ ξ = 0) ∧
      Section6.coherentExtension T1T τT τT1 ∧
      (∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
        Section1.IsIrreducibleCharacterOnGroup ξ →
          Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0) ∧
      (∀ ζ ∈ T1T,
        ∃ Δ : Section1.ClassFunction G,
          section14_theorem_14_9_late_type_T1DeltaCorrection Γ (τT1 ζ) Δ)

@[expose] public def section14_theorem_14_9_late_type_T1CalTConstructionData
    {G : Type u} [Group G] [Finite G]
    (Tmax Q V : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p v : ℕ) : Prop :=
  ∃ T1T : Finset (Section1.ClassFunction Tmax),
    Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T ∧
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
      (∀ ζ ∈ T1T, Section1.scalarProduct Tmax ζ ζ = 1) ∧
      (∀ ζ ∈ T1T, ∀ ξ ∈ T1T, ζ ≠ ξ →
        Section1.scalarProduct Tmax ζ ξ = 0) ∧
      Section5.hypothesis_5_2_statement T1T τT ∧
      (∀ ζ ξ : T1T,
        Section1.degree (ζ : Section1.ClassFunction Tmax) =
          Section1.degree (ξ : Section1.ClassFunction Tmax))


@[expose] public def section14_theorem_14_9_late_type_T1CalTSourceData
    {G : Type u} [Group G] [Finite G]
    (Tmax Q V : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p v : ℕ) : Prop :=
  ∃ T0 : Finset (Section1.ClassFunction Tmax),
    Section7.puncturedInducedFamily ((Q ⊔ V).subgroupOf Tmax) T0 ∧
      ∀ T1T : Finset (Section1.ClassFunction Tmax),
        Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
          ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
            (∀ ζ ∈ T1T, Section1.scalarProduct Tmax ζ ζ = 1) ∧
            (∀ ζ ∈ T1T, ∀ ξ ∈ T1T, ζ ≠ ξ →
              Section1.scalarProduct Tmax ζ ξ = 0) ∧
            Section5.hypothesis_5_2_statement T1T τT ∧
            (∀ ζ ξ : T1T,
              Section1.degree (ζ : Section1.ClassFunction Tmax) =
                Section1.degree (ξ : Section1.ClassFunction Tmax))


@[expose] public def section14_theorem_14_9_late_type_T1CalTFactsSourceData
    {G : Type u} [Group G] [Finite G]
    (Tmax Q V : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p v : ℕ) : Prop :=
  ∀ T1T : Finset (Section1.ClassFunction Tmax),
    Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
        T1T.Nonempty ∧
        Section5.hypothesis_5_2_a_statement T1T ∧
        Section5.hypothesis_5_2_b_statement T1T τT ∧
        (∀ ζ ∈ T1T, Section1.IsIrreducibleCharacterOnGroup ζ) ∧
        (∀ ζ ξ : T1T,
          Section1.degree (ζ : Section1.ClassFunction Tmax) =
            Section1.degree (ξ : Section1.ClassFunction Tmax))


@[expose] public def section14_theorem_14_9_late_type_T1CalTCoreSourceData
    {G : Type u} [Group G] [Finite G]
    (Tmax Q V : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p v : ℕ) : Prop :=
  ∀ T1T : Finset (Section1.ClassFunction Tmax),
    Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
        T1T.Nonempty ∧
        Section5.hypothesis_5_2_b_statement T1T τT ∧
        (∀ ζ ∈ T1T, Section1.IsIrreducibleCharacterOnGroup ζ) ∧
        (∀ ζ ξ : T1T,
          Section1.degree (ζ : Section1.ClassFunction Tmax) =
            Section1.degree (ξ : Section1.ClassFunction Tmax))

@[expose] public def section14_theorem_14_9_late_type_T1CoherentExtensionOrthDeltaData
    {G : Type u} [Group G] [Finite G]
    (Tmax W : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (T1T : Finset (Section1.ClassFunction Tmax)) : Prop :=
  (∀ τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G,
    Section6.coherentExtension T1T τT τT1 →
      ∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
        Section1.IsIrreducibleCharacterOnGroup ξ →
          Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0) ∧
    (∀ τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G,
      Section6.coherentExtension T1T τT τT1 →
        ∀ ζ ∈ T1T,
          ∃ Δ : Section1.ClassFunction G,
            section14_theorem_14_9_late_type_T1DeltaCorrection Γ (τT1 ζ) Δ)

@[expose] public def section14_theorem_14_9_late_type_T1PreExtensionSourceData
    {G : Type u} [Group G] [Finite G]
    (Tmax W Q V : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (p v : ℕ) : Prop :=
  ∃ T1T : Finset (Section1.ClassFunction Tmax),
    Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T ∧
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
      (∀ ζ ∈ T1T, Section1.scalarProduct Tmax ζ ζ = 1) ∧
      (∀ ζ ∈ T1T, ∀ ξ ∈ T1T, ζ ≠ ξ →
        Section1.scalarProduct Tmax ζ ξ = 0) ∧
      Section5.hypothesis_5_2_statement T1T τT ∧
      (∀ ζ ξ : T1T,
        Section1.degree (ζ : Section1.ClassFunction Tmax) =
          Section1.degree (ξ : Section1.ClassFunction Tmax)) ∧
      (∀ τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G,
        Section6.coherentExtension T1T τT τT1 →
          ∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
            Section1.IsIrreducibleCharacterOnGroup ξ →
              Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0) ∧
      (∀ τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G,
        Section6.coherentExtension T1T τT τT1 →
          ∀ ζ ∈ T1T,
            ∃ Δ : Section1.ClassFunction G,
              section14_theorem_14_9_late_type_T1DeltaCorrection Γ (τT1 ζ) Δ)

public theorem section14_theorem_14_9_late_type_T1PreExtensionSourceData_of_calt
    {G : Type u} [Group G] [Finite G]
    {Tmax W Q V : Subgroup G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {Γ : Section1.ClassFunction G}
    {p v : ℕ}
    (hcal : section14_theorem_14_9_late_type_T1CalTConstructionData
      Tmax Q V τT p v)
    (hext : ∀ T1T : Finset (Section1.ClassFunction Tmax),
      Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
        Section5.hypothesis_5_2_statement T1T τT →
          (∀ ζ ξ : T1T,
            Section1.degree (ζ : Section1.ClassFunction Tmax) =
              Section1.degree (ξ : Section1.ClassFunction Tmax)) →
        section14_theorem_14_9_late_type_T1CoherentExtensionOrthDeltaData
          Tmax W τT σ Γ T1T) :
    section14_theorem_14_9_late_type_T1PreExtensionSourceData
      Tmax W Q V τT σ Γ p v := by
  rcases hcal with
    ⟨T1T, hCalT1, hcard, hselfT, horthT, h52, hdeg⟩
  rcases hext T1T hCalT1 h52 hdeg with ⟨hσorth, hDelta⟩
  exact ⟨T1T, hCalT1, hcard, hselfT, horthT, h52, hdeg, hσorth, hDelta⟩

public theorem section14_theorem_14_9_late_type_T1_coherentExtension_of_hypothesis_5_2
    {G : Type u} [Group G] [Finite G]
    {Tmax : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement T1T τT)
    (hdeg : ∀ ζ ξ : T1T,
      Section1.degree (ζ : Section1.ClassFunction Tmax) =
        Section1.degree (ξ : Section1.ClassFunction Tmax)) :
    ∃ τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G,
      Section6.coherentExtension T1T τT τT1 := by
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hcoh : Section6.coherentFamily T1T τT := by
    simpa [Section6.coherentFamily] using
      (Section5.theorem_5_7 T1T τT R hsetup h52a h52b h52c h52d h52e hdeg)
  exact Section6.theorem_6_8_coherentExtension_of_coherentFamily hcoh

public theorem section14_theorem_14_9_late_type_T1RawImageDeltaSourceData_of_preExtension
    {G : Type u} [Group G] [Finite G]
    {Tmax W Q V : Subgroup G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {Γ : Section1.ClassFunction G}
    {p v : ℕ}
    (hsrc : section14_theorem_14_9_late_type_T1PreExtensionSourceData
      Tmax W Q V τT σ Γ p v) :
    section14_theorem_14_9_late_type_T1RawImageDeltaSourceData
      Tmax W τT σ Γ p v := by
  classical
  rcases hsrc with
    ⟨T1T, _hCalT1, hcard, hselfT, horthT, h52, hdeg, hσorth, hDelta⟩
  rcases section14_theorem_14_9_late_type_T1_coherentExtension_of_hypothesis_5_2
      h52 hdeg with
    ⟨τT1, hcohT1⟩
  exact ⟨T1T, τT1, hcard, hselfT, horthT, hcohT1,
    hσorth τT1 hcohT1, hDelta τT1 hcohT1⟩

public theorem section14_theorem_14_9_late_type_T1ImageDeltaSourceData_of_raw
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {Γ : Section1.ClassFunction G}
    {p q v : ℕ}
    (hNotation : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (hsrc : section14_theorem_14_9_late_type_T1RawImageDeltaSourceData
      Tmax W τT σ Γ p v) :
    section14_theorem_14_9_late_type_T1ImageDeltaSourceData
      Tmax τT η Γ p q v := by
  classical
  rcases hNotation with
    ⟨hωData, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  rcases hsrc with
    ⟨T1T, τT1, hcard, hselfT, horthT, hcohT1, hσorthT, hDeltaT⟩
  refine ⟨T1T, τT1, hcard, hselfT, horthT, hcohT1, ?_, hDeltaT⟩
  intro ζ hζ i k hi hk
  let fi : Fin q := ⟨i, hi⟩
  let fk : Fin p := ⟨k, hk⟩
  have hηik : η i k = σ (ωFin fi fk) := by
    rw [hη i k hi hk, hωNat i k hi hk]
  rw [hηik]
  exact hσorthT ζ hζ (ωFin fi fk) (hωFin.irreducible fi fk)

public theorem section14_theorem_14_9_Tmax_typePDefinitionData_of_context
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typePDefinitionData Tmax Q V W2 W1 := by
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm,
      _hChoice, _hMin⟩
  exact hTTypeP

public theorem section14_not_subgroupInKernel_top_of_ne_principal
    {H : Type u} [Group H] [Finite H]
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter H) :
    ¬ Section1.subgroupInKernel' θ (⊤ : Subgroup H) := by
  intro hker
  have horth :
      Section1.scalarProduct H θ (Section1.principalCharacter H) = 0 :=
    Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hθirr hθne
  have hspdeg :
      Section1.scalarProduct H θ (Section1.principalCharacter H) =
        Section1.degree θ := by
    unfold Section1.scalarProduct Section1.principalCharacter Section1.degree
    have hsum :
        (∑ g : H, θ g * star (1 : ℂ)) = ∑ _g : H, θ 1 := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      have hg := hker ⟨g, by simp⟩
      simpa [Section1.degree] using hg
    rw [hsum]
    simp
  have hdeg0 : Section1.degree θ = 0 := by
    rw [← hspdeg, horth]
  rcases hθirr with ⟨_n, ρ, hρirr, hθeq⟩
  have hself : Section1.scalarProduct H θ θ = 1 := by
    rw [hθeq]
    exact Section1.scalarProduct_representation_char_self ρ hρirr
  have hself0 : Section1.scalarProduct H θ θ = 0 := by
    unfold Section1.scalarProduct Section1.degree at hdeg0
    unfold Section1.scalarProduct
    have hzero : ∀ g : H, θ g = 0 := by
      intro g
      have hg := hker ⟨g, by simp⟩
      simpa [Section1.degree, hdeg0] using hg
    simp [hzero]
  norm_num [hself0] at hself

public theorem section14_kernelInducedFamily_top_bot_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (M N : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    Section7.puncturedInducedFamily (N.subgroupOf M) S →
      Section9.kernelInducedFamily M N N (⊥ : Subgroup G) S := by
  intro hS
  refine ⟨bot_le, le_rfl, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
    refine ⟨θ, hθirr, ?_, ?_, hχeq⟩
    · have hnotTop :
          ¬ Section1.subgroupInKernel' θ (⊤ : Subgroup (N.subgroupOf M)) :=
        section14_not_subgroupInKernel_top_of_ne_principal hθirr hθne
      intro hker
      apply hnotTop
      intro a
      exact hker ⟨a, by simp⟩
    · intro a
      have ha : (a : N.subgroupOf M) = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        have haBot :
            ((a : N.subgroupOf M) : M) ∈ (⊥ : Subgroup G).subgroupOf M := by
          simpa [Subgroup.mem_subgroupOf] using a.property
        have haG : (((a : N.subgroupOf M) : M) : G) ∈ (⊥ : Subgroup G) := by
          simpa [Subgroup.mem_subgroupOf] using haBot
        simpa [Subgroup.mem_bot] using haG
      simp [ha, Section1.degree]
  · intro hχ
    rcases hχ with ⟨θ, hθirr, hθnotker, _hθbot, hχeq⟩
    rw [hS χ]
    refine ⟨θ, hθirr, ?_, hχeq⟩
    intro hθeq
    apply hθnotker
    rw [hθeq]
    exact Section9.principalCharacter_subgroupInKernel'_sec9
      ((N.subgroupOf M).subgroupOf (N.subgroupOf M))

public theorem section14_late_type_T1_kernelInducedFamily_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (Tmax Q V : Subgroup G)
    (T0 : Finset (Section1.ClassFunction Tmax)) :
    Section7.puncturedInducedFamily ((Q ⊔ V).subgroupOf Tmax) T0 →
      ∃ T1T : Finset (Section1.ClassFunction Tmax),
        Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T := by
  intro hT0
  let T1T : Finset (Section1.ClassFunction Tmax) :=
    Section9.kernelInducedSubfamily_sec9 Tmax (Q ⊔ V) (Q ⊔ V) Q T0
  have hbase :
      Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V)
        (⊥ : Subgroup G) T0 :=
    section14_kernelInducedFamily_top_bot_of_puncturedInducedFamily
      Tmax (Q ⊔ V) T0 hT0
  have hQle : Q ≤ Q ⊔ V := le_sup_left
  have hT1T :
      Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T :=
    Section9.kernelInducedFamily_subfamily_of_le_sec9
      Tmax (Q ⊔ V) (Q ⊔ V) (⊥ : Subgroup G) Q T0
      hQle bot_le hbase
  exact ⟨T1T, hT1T⟩

public theorem section14_scalarProduct_self_eq_one_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨_n, ρ, hρirr, hχeq⟩
  rw [hχeq]
  exact Section1.scalarProduct_representation_char_self ρ hρirr

public theorem section14_hypothesis_5_2_a_of_kernelInducedFamily_self
    {G : Type u} [Group G] [Finite G]
    {M N Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hNnormal : (N.subgroupOf M).Normal)
    (hoddM : Odd (Nat.card M))
    (hS : Section9.kernelInducedFamily M N N Y S) :
    Section5.hypothesis_5_2_a_statement S := by
  classical
  letI : (N.subgroupOf M).Normal := hNnormal
  have hclosed :
      ∀ χ : Section1.ClassFunction M, χ ∈ S →
        Section1.conjugateCharacter χ ∈ S :=
    Section9.kernelInducedFamily_conjugationClosed_sec9 M N N Y S hS
  intro X
  refine ⟨hclosed (X : Section1.ClassFunction M) X.property, ?_⟩
  intro hXreal
  rcases hS with ⟨_hYN, _hNN, hmem⟩
  rcases (hmem (X : Section1.ClassFunction M)).mp X.property with
    ⟨θ, hθirr, hθnotker, _hθker, hXeq⟩
  have hθne_principal : θ ≠ Section1.principalCharacter (N.subgroupOf M) :=
    Section9.ne_principalCharacter_of_not_subgroupInKernel'_sec9 hθnotker
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθrep_ne_principal :
      ρ.character ≠ Section1.principalCharacter (N.subgroupOf M) := by
    intro hρprincipal
    exact hθne_principal (by rw [hθeq, hρprincipal])
  have horth :
      Section1.scalarProduct M
        (Section1.inducedCF (N.subgroupOf M) ρ.character)
        (Section1.conjugateCharacter
          (Section1.inducedCF (N.subgroupOf M) ρ.character)) = 0 := by
    simpa [Section1.orthogonal] using
      (Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        (N.subgroupOf M) ρ hoddM hρirr hθrep_ne_principal)
  have horthX :
      Section1.scalarProduct M (X : Section1.ClassFunction M)
        (Section1.conjugateCharacter (X : Section1.ClassFunction M)) = 0 := by
    simpa [hXeq, hθeq] using horth
  have hzeroX :
      Section1.scalarProduct M (X : Section1.ClassFunction M)
        (X : Section1.ClassFunction M) = 0 := by
    have hconj_eq :
        Section1.conjugateCharacter (X : Section1.ClassFunction M) =
          (X : Section1.ClassFunction M) := hXreal.symm
    simpa [hconj_eq] using horthX
  have hself :
      Section1.scalarProduct M (X : Section1.ClassFunction M)
        (X : Section1.ClassFunction M) =
          ((N.subgroupOf M).relIndex
            (Section1.inertiaSubgroup (N.subgroupOf M) ρ.character) : ℂ) := by
    simpa [hXeq, hθeq] using
      (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        (N.subgroupOf M) ρ hρirr)
  rw [hself] at hzeroX
  have hrel_ne :
      ((N.subgroupOf M).relIndex
        (Section1.inertiaSubgroup (N.subgroupOf M) ρ.character) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Subgroup.index_ne_zero_of_finite
        (H := (N.subgroupOf M).subgroupOf
          (Section1.inertiaSubgroup (N.subgroupOf M) ρ.character)))
  exact hrel_ne hzeroX

public theorem section14_inducedKernelFamily_of_kernelInducedFamily_self
    {G : Type u} [Group G] [Finite G]
    {M N Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : Section9.kernelInducedFamily M N N Y S) :
    Section6.inducedKernelFamily (N.subgroupOf M) (Y.subgroupOf M) S := by
  classical
  rcases hS with ⟨hYN, _hNN, hmem⟩
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hYN hy
  · intro χ
    constructor
    · intro hχ
      rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθnotker, hθker, hχeq⟩
      refine ⟨θ, hθirr, hθker, ?_, hχeq⟩
      exact Section9.ne_principalCharacter_of_not_subgroupInKernel'_sec9 hθnotker
    · intro hχ
      rcases hχ with ⟨θ, hθirr, hθker, hθne, hχeq⟩
      rw [hmem χ]
      refine ⟨θ, hθirr, ?_, hθker, hχeq⟩
      have hnotTop :
          ¬ Section1.subgroupInKernel' θ (⊤ : Subgroup (N.subgroupOf M)) :=
        section14_not_subgroupInKernel_top_of_ne_principal hθirr hθne
      intro hker
      apply hnotTop
      intro n
      exact hker ⟨n, by simp⟩

public theorem section14_typeP_quotient_commutative_of_sup
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V : Subgroup G}
    (hQleT : Q ≤ Tmax)
    (hVleT : V ≤ Tmax)
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hVcomm : IsMulCommutative V) :
    IsMulCommutative
      (((Q ⊔ V).subgroupOf Tmax) ⧸
        (Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax)) := by
  classical
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  let H : Subgroup K := (V.subgroupOf Tmax).subgroupOf K
  haveI : N.Normal := by
    dsimp [N, K]
    exact hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
  have hHcomm : IsMulCommutative H := by
    letI : IsMulCommutative V := hVcomm
    dsimp [H]
    infer_instance
  have hK_eq : K = Q.subgroupOf Tmax ⊔ V.subgroupOf Tmax := by
    dsimp [K]
    rw [Subgroup.subgroupOf_sup hQleT hVleT]
  have hsup : N ⊔ H = ⊤ := by
    dsimp [N, H]
    rw [← Subgroup.subgroupOf_sup (A := Q.subgroupOf Tmax)
      (A' := V.subgroupOf Tmax) (B := K)]
    · exact Subgroup.subgroupOf_eq_top.2 (by
        intro x hx
        simpa [hK_eq] using hx)
    · intro x hx
      have hx' : (x : Tmax) ∈ Q.subgroupOf Tmax ⊔ V.subgroupOf Tmax :=
        Subgroup.mem_sup_left hx
      simpa [← hK_eq, K] using hx'
    · intro x hx
      have hx' : (x : Tmax) ∈ Q.subgroupOf Tmax ⊔ V.subgroupOf Tmax :=
        Subgroup.mem_sup_right hx
      simpa [← hK_eq, K] using hx'
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (N := N) (H := H) hsup hHcomm)

public theorem section14_typeP_quotient_card_eq_card_V_of_sup
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V : Subgroup G}
    (hQleT : Q ≤ Tmax)
    (hVleT : V ≤ Tmax)
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hQVdisj : Disjoint Q V) :
    Nat.card
      (((Q ⊔ V).subgroupOf Tmax) ⧸
        (Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax)) =
      Nat.card V := by
  classical
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let Qsub : Subgroup Tmax := Q.subgroupOf Tmax
  let Vsub : Subgroup Tmax := V.subgroupOf Tmax
  let QK : Subgroup K := Qsub.subgroupOf K
  let VK : Subgroup K := Vsub.subgroupOf K
  have hQsub_le_K : Qsub ≤ K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  have hVsub_le_K : Vsub ≤ K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : V ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  haveI : QK.Normal := by
    dsimp [QK, Qsub, K]
    exact hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
  have hK_eq : K = Qsub ⊔ Vsub := by
    dsimp [K, Qsub, Vsub]
    rw [Subgroup.subgroupOf_sup hQleT hVleT]
  have hdisj : Disjoint QK VK := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxV
    apply Subtype.ext
    have hxQG : ((x : K) : Tmax) ∈ Qsub := by
      simpa [QK, Subgroup.mem_subgroupOf] using hxQ
    have hxVG : ((x : K) : Tmax) ∈ Vsub := by
      simpa [VK, Subgroup.mem_subgroupOf] using hxV
    have hxBot :
        (((x : K) : Tmax) : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hQVdisj)
        (Subgroup.mem_subgroupOf.mp hxQG)
        (Subgroup.mem_subgroupOf.mp hxVG)
    exact Subtype.ext (by simpa using hxBot)
  have hsup : QK ⊔ VK = ⊤ := by
    dsimp [QK, VK]
    rw [← Subgroup.subgroupOf_sup (A := Qsub) (A' := Vsub) (B := K)]
    · exact Subgroup.subgroupOf_eq_top.2 (by
        intro x hx
        simpa [hK_eq] using hx)
    · exact hQsub_le_K
    · exact hVsub_le_K
  have hcomp : QK.IsComplement' VK := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxSup : x ∈ QK ⊔ VK := by
      rw [hsup]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := QK) (t := VK)).1
        hxSup with
      ⟨q0, hq0, v0, hv0, hq0v0⟩
    exact ⟨q0, hq0, v0, hv0, hq0v0⟩
  have hVKcard : Nat.card VK = Nat.card V := by
    calc
      Nat.card VK = Nat.card Vsub :=
        natCard_subgroupOf_eq Vsub K hVsub_le_K
      _ = Nat.card V := natCard_subgroupOf_eq V Tmax hVleT
  calc
    Nat.card (K ⧸ QK) = QK.index :=
      (Subgroup.index_eq_card (H := QK)).symm
    _ = Nat.card VK := (Subgroup.IsComplement'.symm hcomp).index_eq_card
    _ = Nat.card V := hVKcard

public theorem section14_typeP_Q_disjoint_sup_of_frobenius
    {G : Type u} [Group G] [Finite G]
    {Q V W2 : Subgroup G}
    (hQVdisj : Disjoint Q V)
    (hQVW2disj : Disjoint (Q ⊔ V) W2)
    (hfrob : section12FrobeniusJoinWithKernel V W2) :
    Disjoint Q (V ⊔ W2) := by
  classical
  let Sg : Subgroup G := V ⊔ W2
  let Vsub : Subgroup Sg := V.subgroupOf Sg
  let Wsub : Subgroup Sg := W2.subgroupOf Sg
  have hfrobLocal : IsFrobeniusGroupWithKernelComplement Vsub Wsub := by
    simpa [section12FrobeniusJoinWithKernel, Sg, Vsub, Wsub] using hfrob
  rw [Subgroup.disjoint_def]
  intro x hxQ hxS
  let xS : Sg := ⟨x, hxS⟩
  rcases hfrobLocal.isComplement'.existsUnique xS with ⟨⟨vS, wS⟩, hmul, _huniq⟩
  have hx_eq : x = (vS : G) * (wS : G) := by
    simpa [xS] using (congrArg (fun z : Sg => (z : G)) hmul).symm
  have hvV : (vS : G) ∈ V := Subgroup.mem_subgroupOf.mp vS.property
  have hwW2 : (wS : G) ∈ W2 := Subgroup.mem_subgroupOf.mp wS.property
  have hxQV : x ∈ Q ⊔ V := (le_sup_left : Q ≤ Q ⊔ V) hxQ
  have hvQV : (vS : G) ∈ Q ⊔ V := (le_sup_right : V ≤ Q ⊔ V) hvV
  have hw_eq : (wS : G) = (vS : G)⁻¹ * x := by
    rw [hx_eq]
    simp
  have hwQV : (wS : G) ∈ Q ⊔ V := by
    rw [hw_eq]
    exact (Q ⊔ V).mul_mem ((Q ⊔ V).inv_mem hvQV) hxQV
  have hw_one : (wS : G) = 1 :=
    (Subgroup.disjoint_def.mp hQVW2disj) hwQV hwW2
  have hxV : x ∈ V := by
    rw [hx_eq, hw_one, mul_one]
    exact hvV
  exact (Subgroup.disjoint_def.mp hQVdisj) hxQ hxV

public noncomputable def section14_typeP_quotientMulEquiv
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQleT : Q ≤ Tmax) (hVleT : V ≤ Tmax) (hW2leT : W2 ≤ Tmax)
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hQVdisj : Disjoint Q V)
    (hTcomp : section12ComplementIn Tmax (Q ⊔ V) W2)
    (hfrob : section12FrobeniusJoinWithKernel V W2) :
    ↥(V ⊔ W2) ≃* (Tmax ⧸ Q.subgroupOf Tmax) := by
  classical
  let N : Subgroup Tmax := Q.subgroupOf Tmax
  letI : N.Normal := hQnormal
  let qT : Tmax →* Tmax ⧸ N := QuotientGroup.mk' N
  let Sg : Subgroup G := V ⊔ W2
  have hSleT : Sg ≤ Tmax := sup_le hVleT hW2leT
  let φ : Sg →* Tmax ⧸ N :=
    { toFun := fun x => qT ⟨(x : G), hSleT x.property⟩
      map_one' := by
        change qT 1 = 1
        exact map_one qT
      map_mul' := by
        intro x y
        change qT (⟨((x * y : Sg) : G), hSleT (x * y).property⟩ : Tmax) =
          qT (⟨(x : G), hSleT x.property⟩ : Tmax) *
            qT (⟨(y : G), hSleT y.property⟩ : Tmax)
        have hxy : (⟨((x * y : Sg) : G), hSleT (x * y).property⟩ : Tmax) =
            (⟨(x : G), hSleT x.property⟩ : Tmax) *
              (⟨(y : G), hSleT y.property⟩ : Tmax) := by
          rfl
        rw [hxy]
        exact map_mul qT _ _ }
  have hQdisjS : Disjoint Q Sg :=
    section14_typeP_Q_disjoint_sup_of_frobenius hQVdisj hTcomp.2.2.2 hfrob
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have hxyN : ((⟨(x : G), hSleT x.property⟩ : Tmax)⁻¹ *
        (⟨(y : G), hSleT y.property⟩ : Tmax)) ∈ N := by
      exact QuotientGroup.eq.mp hxy
    have hxyQ : (x : G)⁻¹ * (y : G) ∈ Q := by
      simpa [N, Subgroup.mem_subgroupOf] using hxyN
    have hxyS : (x : G)⁻¹ * (y : G) ∈ Sg :=
      Sg.mul_mem (Sg.inv_mem x.property) y.property
    exact inv_mul_eq_one.mp ((Subgroup.disjoint_def.mp hQdisjS) hxyQ hxyS)
  have hφ_surj : Function.Surjective φ := by
    intro z
    rcases QuotientGroup.mk'_surjective (N := N) z with ⟨t, rfl⟩
    let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
    let R : Subgroup Tmax := W2.subgroupOf Tmax
    have hKR : K.IsComplement' R := by
      simpa [K, R] using
        Section12.section12ComplementIn_left_normal_isComplement'
          (G := G) (M := Tmax) (K := Q ⊔ V) (L := W2) hTcomp hKnormal
    rcases hKR.existsUnique t with ⟨⟨kT, rT⟩, hmul, _huniq⟩
    let Qsub : Subgroup Tmax := Q.subgroupOf Tmax
    let VsubT : Subgroup Tmax := V.subgroupOf Tmax
    have hK_eq : K = Qsub ⊔ VsubT := by
      dsimp [K, Qsub, VsubT]
      rw [Subgroup.subgroupOf_sup hQleT hVleT]
    have hk_mem_sup : (kT : Tmax) ∈ Qsub ⊔ VsubT := by
      simpa [hK_eq] using kT.property
    rcases (Subgroup.mem_sup_of_normal_left (x := (kT : Tmax)) (s := Qsub) (t := VsubT)).1
        hk_mem_sup with ⟨q0, hq0Q, v0, hv0V, hk_eq⟩
    have hv0G : (v0 : G) ∈ V := Subgroup.mem_subgroupOf.mp hv0V
    have hrG : (rT : G) ∈ W2 := Subgroup.mem_subgroupOf.mp rT.property
    have hs_mem : (v0 : G) * (rT : G) ∈ Sg :=
      Sg.mul_mem ((le_sup_left : V ≤ Sg) hv0G) ((le_sup_right : W2 ≤ Sg) hrG)
    let s : Sg := ⟨(v0 : G) * (rT : G), hs_mem⟩
    refine ⟨s, ?_⟩
    have ht_eq : t = (kT : Tmax) * (rT : Tmax) := by
      simpa using hmul.symm
    have hk_eq' : (kT : Tmax) = q0 * v0 := by
      simpa using hk_eq.symm
    let sT : Tmax := ⟨(s : G), hSleT s.property⟩
    have hsT_eq : sT = v0 * (rT : Tmax) := by rfl
    change qT sT = qT t
    apply QuotientGroup.eq.mpr
    rw [ht_eq, hk_eq', hsT_eq]
    have hconj : (((v0 * (rT : Tmax))⁻¹ * q0 * (v0 * (rT : Tmax))) : Tmax) ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem q0 hq0Q (v0 * (rT : Tmax))⁻¹
    simpa [mul_assoc] using hconj
  exact MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩

public theorem section14_typeP_quotientMulEquiv_apply
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQleT : Q ≤ Tmax) (hVleT : V ≤ Tmax) (hW2leT : W2 ≤ Tmax)
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hQVdisj : Disjoint Q V)
    (hTcomp : section12ComplementIn Tmax (Q ⊔ V) W2)
    (hfrob : section12FrobeniusJoinWithKernel V W2)
    (x : ↥(V ⊔ W2)) :
    section14_typeP_quotientMulEquiv hQleT hVleT hW2leT hQnormal
        hKnormal hQVdisj hTcomp hfrob x =
      QuotientGroup.mk' (Q.subgroupOf Tmax)
        ⟨(x : G), (sup_le hVleT hW2leT) x.property⟩ := by
  rfl

public theorem section14_typeP_frobeniusQuotientWithKernel_of_frobeniusJoin
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQleT : Q ≤ Tmax) (hVleT : V ≤ Tmax) (hW2leT : W2 ≤ Tmax)
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hQVdisj : Disjoint Q V)
    (hTcomp : section12ComplementIn Tmax (Q ⊔ V) W2)
    (hfrob : section12FrobeniusJoinWithKernel V W2) :
    Section6.frobeniusQuotientWithKernel
      ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) := by
  classical
  let N : Subgroup Tmax := Q.subgroupOf Tmax
  letI : N.Normal := hQnormal
  let qT : Tmax →* Tmax ⧸ N := QuotientGroup.mk' N
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let R : Subgroup Tmax := W2.subgroupOf Tmax
  let Sg : Subgroup G := V ⊔ W2
  let Vsub : Subgroup Sg := V.subgroupOf Sg
  let Wsub : Subgroup Sg := W2.subgroupOf Sg
  let e : Sg ≃* (Tmax ⧸ N) :=
    section14_typeP_quotientMulEquiv hQleT hVleT hW2leT hQnormal
      hKnormal hQVdisj hTcomp hfrob
  have hfrobLocal : IsFrobeniusGroupWithKernelComplement Vsub Wsub := by
    simpa [section12FrobeniusJoinWithKernel, Sg, Vsub, Wsub] using hfrob
  have hfrobMap :
      IsFrobeniusGroupWithKernelComplement
        (Vsub.map e.toMonoidHom) (Wsub.map e.toMonoidHom) :=
    section14_isFrobeniusGroupWithKernelComplement_map_mulEquiv
      (e := e) hfrobLocal
  have hVmap :
      Vsub.map e.toMonoidHom = K.map qT := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨v, hvV, rfl⟩
      have hvG : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hvV
      refine ⟨⟨(v : G), ?_⟩, ?_, ?_⟩
      · exact (sup_le hVleT hW2leT) v.property
      · exact Subgroup.mem_subgroupOf.mpr ((le_sup_right : V ≤ Q ⊔ V) hvG)
      · simpa [e, qT, N] using
          (section14_typeP_quotientMulEquiv_apply hQleT hVleT hW2leT
            hQnormal hKnormal hQVdisj hTcomp hfrob v).symm
    · intro hz
      rcases hz with ⟨k, hkK, rfl⟩
      let Qsub : Subgroup Tmax := Q.subgroupOf Tmax
      let VsubT : Subgroup Tmax := V.subgroupOf Tmax
      have hK_eq : K = Qsub ⊔ VsubT := by
        dsimp [K, Qsub, VsubT]
        rw [Subgroup.subgroupOf_sup hQleT hVleT]
      have hk_mem_sup : k ∈ Qsub ⊔ VsubT := by
        simpa [hK_eq] using hkK
      rcases (Subgroup.mem_sup_of_normal_left (x := k) (s := Qsub) (t := VsubT)).1
          hk_mem_sup with ⟨q0, hq0Q, v0, hv0V, hk_eq⟩
      have hv0G : (v0 : G) ∈ V := Subgroup.mem_subgroupOf.mp hv0V
      have hv0S : (v0 : G) ∈ Sg := (le_sup_left : V ≤ Sg) hv0G
      let vS : Sg := ⟨(v0 : G), hv0S⟩
      have hvS : vS ∈ Vsub := by
        exact Subgroup.mem_subgroupOf.mpr hv0G
      refine ⟨vS, hvS, ?_⟩
      have hk_eq' : k = q0 * v0 := by
        simpa using hk_eq.symm
      rw [hk_eq']
      have hq0_one : qT q0 = 1 := by
        exact (QuotientGroup.eq_one_iff (N := N) q0).2
          (by simpa [N, Qsub, Subgroup.mem_subgroupOf] using hq0Q)
      calc
        e vS = qT v0 := by
          simpa [e, qT, N, vS] using
            section14_typeP_quotientMulEquiv_apply hQleT hVleT hW2leT
              hQnormal hKnormal hQVdisj hTcomp hfrob vS
        _ = qT (q0 * v0) := by
          rw [map_mul, hq0_one, one_mul]
  have hWmap :
      Wsub.map e.toMonoidHom = R.map qT := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hwW, rfl⟩
      have hwG : (w : G) ∈ W2 := Subgroup.mem_subgroupOf.mp hwW
      refine ⟨⟨(w : G), ?_⟩, ?_, ?_⟩
      · exact (sup_le hVleT hW2leT) w.property
      · exact Subgroup.mem_subgroupOf.mpr hwG
      · simpa [e, qT, N] using
          (section14_typeP_quotientMulEquiv_apply hQleT hVleT hW2leT
            hQnormal hKnormal hQVdisj hTcomp hfrob w).symm
    · intro hz
      rcases hz with ⟨w, hwR, rfl⟩
      have hwG : (w : G) ∈ W2 := Subgroup.mem_subgroupOf.mp hwR
      have hwS : (w : G) ∈ Sg := (le_sup_right : W2 ≤ Sg) hwG
      let wS : Sg := ⟨(w : G), hwS⟩
      have hwWsub : wS ∈ Wsub := by
        exact Subgroup.mem_subgroupOf.mpr hwG
      refine ⟨wS, hwWsub, ?_⟩
      simpa [e, qT, N, wS] using
        section14_typeP_quotientMulEquiv_apply hQleT hVleT hW2leT
          hQnormal hKnormal hQVdisj hTcomp hfrob wS
  have hfrobQuot : IsFrobeniusGroupWithKernelComplement (K.map qT) (R.map qT) := by
    rw [← hVmap, ← hWmap]
    exact hfrobMap
  have hQleK : N ≤ K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨hQnormal, hQleK, hKnormal, R.map qT, ?_, ?_, ?_, ?_⟩
  · exact hfrobQuot.isComplement'
  · exact hfrobQuot.kernel_ne_bot
  · exact hfrobQuot.complement_ne_bot
  · have hcent :
        ∀ r : R.map qT, r ≠ 1 →
          elementCentralizerIn (K.map qT) (r : Tmax ⧸ N) = ⊥ :=
      (lemma_3_1 (G := Tmax ⧸ N) (K := K.map qT) (R := R.map qT)
        hfrobQuot.kernel_ne_bot hfrobQuot.complement_ne_bot
        hfrobQuot.normal hfrobQuot.isComplement').1 hfrobQuot
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer, elementCentralizerIn]
      using hcent r hr

public theorem section14_theorem_14_9_late_type_T1CalTFactsSourceData_of_core
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Tmax Q V W1 W2 : Subgroup G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p v : ℕ}
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hcore : section14_theorem_14_9_late_type_T1CalTCoreSourceData
      Tmax Q V τT p v) :
    section14_theorem_14_9_late_type_T1CalTFactsSourceData
      Tmax Q V τT p v := by
  intro T1T hCalT1
  rcases hcore T1T hCalT1 with
    ⟨hcard, hne, h52b, hIrr, hdeg⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  have hNnormal : ((Q ⊔ V).subgroupOf Tmax).Normal := by
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [hDerEq] using hDerNormal
  have hoddT : Odd (Nat.card Tmax) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card Tmax)
  have h52a : Section5.hypothesis_5_2_a_statement T1T :=
    section14_hypothesis_5_2_a_of_kernelInducedFamily_self
      (M := Tmax) (N := Q ⊔ V) (Y := Q) (S := T1T)
      hNnormal hoddT hCalT1
  exact ⟨hcard, hne, h52a, h52b, hIrr, hdeg⟩

public theorem section14_theorem_14_9_late_type_T1CalTSourceData_of_facts
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V : Subgroup G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p v : ℕ}
    (hfacts : section14_theorem_14_9_late_type_T1CalTFactsSourceData
      Tmax Q V τT p v) :
    section14_theorem_14_9_late_type_T1CalTSourceData
      Tmax Q V τT p v := by
  classical
  rcases Section12.exists_puncturedInducedFamily
      ((Q ⊔ V).subgroupOf Tmax) with
    ⟨T0, hT0⟩
  refine ⟨T0, hT0, ?_⟩
  intro T1T hCalT1
  rcases hfacts T1T hCalT1 with
    ⟨hcard, hne, h52a, h52b, hIrr, hdeg⟩
  have h52 : Section5.hypothesis_5_2_statement T1T τT :=
    Section5.theorem_5_3_a hne h52a h52b (fun X => hIrr X X.property)
  have hself :
      ∀ ζ ∈ T1T, Section1.scalarProduct Tmax ζ ζ = 1 := by
    intro ζ hζ
    exact section14_scalarProduct_self_eq_one_of_irreducible (hIrr ζ hζ)
  have horth :
      ∀ ζ ∈ T1T, ∀ ξ ∈ T1T, ζ ≠ ξ →
        Section1.scalarProduct Tmax ζ ξ = 0 := by
    rcases h52 with ⟨_hsetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
    intro ζ hζ ξ hξ hneζξ
    exact h52c hζ hξ hneζξ
  exact ⟨hcard, hself, horth, h52, hdeg⟩

public theorem section14_theorem_14_9_late_type_T1CalTConstructionData_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V : Subgroup G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p v : ℕ}
    (hsrc : section14_theorem_14_9_late_type_T1CalTSourceData
      Tmax Q V τT p v) :
    section14_theorem_14_9_late_type_T1CalTConstructionData
      Tmax Q V τT p v := by
  rcases hsrc with ⟨T0, hT0, hfacts⟩
  rcases section14_late_type_T1_kernelInducedFamily_of_puncturedInducedFamily
      Tmax Q V T0 hT0 with
    ⟨T1T, hCalT1⟩
  rcases hfacts T1T hCalT1 with
    ⟨hcard, hself, horth, h52, hdeg⟩
  exact ⟨T1T, hCalT1, hcard, hself, horth, h52, hdeg⟩

public theorem section14_v_card_eq_of_late_type_context
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Nat.card V = v := by
  intro hctx
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD,
      _hc, _hd, _hUcard, hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hd_one : d = 1 :=
    Section13.theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  rw [hVcard, hd_one, Nat.mul_one]

public theorem section14_theorem_14_9_late_type_T1_calt_nonempty_of_context
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section8.typePDefinitionData Tmax Q V W2 W1 →
        (Q.subgroupOf Tmax).Normal →
          ∀ T1T : Finset (Section1.ClassFunction Tmax),
            Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
              T1T.Nonempty := by
  classical
  intro hctx hTtypeP hQnormal T1T hCalT1
  have hTtypeP0 : Section8.typePDefinitionData Tmax Q V W2 W1 := hTtypeP
  have hT13 :=
    Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  rcases hT13 with
    ⟨_hTmaxMF, _htypeT, _htypeII_of_pq, _hVcomm, hfrobVW2, _hQelem,
      _hQcard, _hv, _hTfamCoh, _hTI, _hTauT, _hnormT⟩
  have hDsolv : Group.IsSolvable (ambientDerivedSubgroup Tmax) :=
    Section9.typePDefinitionData_ambientDerived_solvable_sec9 hTtypeP0
  rcases hTtypeP with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
  have hDleT : ambientDerivedSubgroup Tmax ≤ Tmax :=
    section12_ambientDerivedSubgroup_le
  have hKsolv : Group.IsSolvable ((Q ⊔ V).subgroupOf Tmax) := by
    have hDsolvSub : Group.IsSolvable ((ambientDerivedSubgroup Tmax).subgroupOf Tmax) := by
      let e := Subgroup.subgroupOfEquivOfLe
        (H := ambientDerivedSubgroup Tmax) (K := Tmax) hDleT
      let _ : Group.IsSolvable (ambientDerivedSubgroup Tmax) := hDsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := e.toMonoidHom) e.injective
    rw [hDerEq] at hDsolvSub
    exact hDsolvSub
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hVne : V ≠ ⊥ := by
    let S : Subgroup G := V ⊔ W2
    let Vsub : Subgroup S := V.subgroupOf S
    have hVsub_ne : Vsub ≠ ⊥ := hfrobVW2.kernel_ne_bot
    intro hVbot
    have hVsub_bot : Vsub = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxV : (x : G) ∈ V := by
          simpa [Vsub, Subgroup.mem_subgroupOf] using hx
        have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
          simpa [hVbot] using hxV
        exact Subtype.ext (by simpa using hxbot)
      · intro hx
        have hxone : x = 1 := by simpa using hx
        rw [hxone]
        exact Subgroup.one_mem Vsub
    exact hVsub_ne hVsub_bot
  have hQleK :
      Q.subgroupOf Tmax ≤ (Q ⊔ V).subgroupOf Tmax := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  have hQneK :
      Q.subgroupOf Tmax ≠ (Q ⊔ V).subgroupOf Tmax := by
    intro hEq
    apply hVne
    apply le_antisymm
    · intro x hxV
      have hxT : x ∈ Tmax := hVleT hxV
      have hxK : (⟨x, hxT⟩ : Tmax) ∈ (Q ⊔ V).subgroupOf Tmax :=
        Subgroup.mem_subgroupOf.mpr ((le_sup_right : V ≤ Q ⊔ V) hxV)
      have hxQsub : (⟨x, hxT⟩ : Tmax) ∈ Q.subgroupOf Tmax := by
        simpa [hEq] using hxK
      have hxQ : x ∈ Q := Subgroup.mem_subgroupOf.mp hxQsub
      have hxBot : x ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp hDerComp.2.2.2) hxQ hxV
      exact hxBot
    · exact bot_le
  have hQltK : Q.subgroupOf Tmax < (Q ⊔ V).subgroupOf Tmax :=
    lt_of_le_of_ne hQleK hQneK
  letI : ((Q.subgroupOf Tmax).subgroupOf
      ((Q ⊔ V).subgroupOf Tmax)).Normal :=
    hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
  have hS6 :
      Section6.inducedKernelFamily
        ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) T1T :=
    section14_inducedKernelFamily_of_kernelInducedFamily_self hCalT1
  rcases Section6.inducedKernelFamily_nonempty_of_solvable_proper
      hKsolv hQnormal hQltK hS6 with
    ⟨χ, hχ⟩
  exact ⟨χ, hχ⟩

public theorem section14_theorem_14_9_late_type_T1_section8InducedNonkernel_of_calt
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W1 W2 : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hne : T1T.Nonempty)
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T) :
    Section8.section8InducedNonkernelFamily Tmax (Q ⊔ V) T1T := by
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
        _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
    exact hDerComp.2.2.1
  have hCalT1' :
      Section9.kernelInducedFamily Tmax
        (ambientDerivedSubgroup Tmax) (Q ⊔ V) Q T1T := by
    simpa [hDerEq] using hCalT1
  exact Section9.section8InducedNonkernelFamily_of_kernelInducedFamily_le_nonempty_sec9
    Tmax (Q ⊔ V) (Q ⊔ V) Q T1T le_rfl hCalT1' hne

public theorem section14_linearCharacter_orbit_card_eq_div
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [IsMulCommutative Q] [MulDistribMulAction A Q]
    (hfree : ∀ a : A, a ≠ 1 → ∀ q : Q, a • q = q → q = 1) :
    letI : MulDistribMulAction A (Q →* ℂˣ) :=
      Section10.characterGroupContragredientMulDistribMulAction A Q
    Nat.card (Section10.nonidentityOrbitQuotient A (Q →* ℂˣ)) =
      (Nat.card Q - 1) / Nat.card A := by
  classical
  letI : MulDistribMulAction A (Q →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction A Q
  have hfreeChar :
      ∀ a : A, a ≠ 1 → ∀ χ : Q →* ℂˣ, a • χ = χ → χ = 1 := by
    intro a ha χ hfix
    have hχfix : ∀ q : Q, χ (a⁻¹ • q) = χ q := by
      intro q
      have h := congrFun (congrArg DFunLike.coe hfix) q
      simpa [Section10.characterGroupContragredient_smul_apply] using h
    exact Section10.linearCharacter_eq_one_of_fixed_by_fixedPointFree a⁻¹
      (by
        intro q hq
        exact hfree a⁻¹ (inv_ne_one.mpr ha) q hq)
      χ hχfix
  have horbit := Section10.nonidentityOrbitQuotient_card_eq_div
    (A := A) (G := Q →* ℂˣ) hfreeChar
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  have hchars : Nat.card (Q →* ℂˣ) = Nat.card Q := by
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  rw [hchars] at horbit
  exact horbit

public theorem section14_linearCharacter_orbit_card_mul_eq_sub_one
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [IsMulCommutative Q] [MulDistribMulAction A Q]
    (hfree : ∀ a : A, a ≠ 1 → ∀ q : Q, a • q = q → q = 1) :
    letI : MulDistribMulAction A (Q →* ℂˣ) :=
      Section10.characterGroupContragredientMulDistribMulAction A Q
    Nat.card A *
      Nat.card (Section10.nonidentityOrbitQuotient A (Q →* ℂˣ)) =
        Nat.card Q - 1 := by
  classical
  letI : MulDistribMulAction A (Q →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction A Q
  have hfreeChar :
      ∀ a : A, a ≠ 1 → ∀ χ : Q →* ℂˣ, a • χ = χ → χ = 1 := by
    intro a ha χ hfix
    have hχfix : ∀ q : Q, χ (a⁻¹ • q) = χ q := by
      intro q
      have h := congrFun (congrArg DFunLike.coe hfix) q
      simpa [Section10.characterGroupContragredient_smul_apply] using h
    exact Section10.linearCharacter_eq_one_of_fixed_by_fixedPointFree a⁻¹
      (by
        intro q hq
        exact hfree a⁻¹ (inv_ne_one.mpr ha) q hq)
      χ hχfix
  have horbit := Section10.nonidentityOrbitQuotient_card_mul_eq_sub_one
    (A := A) (G := Q →* ℂˣ) hfreeChar
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  have hchars : Nat.card (Q →* ℂˣ) = Nat.card Q := by
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  rw [hchars] at horbit
  exact horbit

set_option maxHeartbeats 800000 in
public theorem section14_typeP_quotient_fixed_eq_one_of_W2_ne_one
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W1 W2 : Subgroup G}
    (hTtypeP : Section8.typePDefinitionData Tmax Q V W2 W1)
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hfrobVW2 : section12FrobeniusJoinWithKernel V W2)
    (a : W2.subgroupOf Tmax) (ha : a ≠ 1) :
    let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
    let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
    letI : K.Normal := by
      rcases hTtypeP with
        ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer,
          _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
          _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
      have hDerNormal :
          ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
        (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
      simpa [K, hDerComp.2.2.1] using hDerNormal
    letI : N.Normal := hQnormal.subgroupOf K
    let hNinv : IsInvariant (W2.subgroupOf Tmax) K N := by
      have hW2normK : W2.subgroupOf Tmax ≤ Subgroup.normalizer (K : Set Tmax) :=
        Subgroup.le_normalizer_of_normal (H := K)
      have hW2normQ :
          W2.subgroupOf Tmax ≤ Subgroup.normalizer (Q.subgroupOf Tmax : Set Tmax) :=
        Subgroup.le_normalizer_of_normal (H := Q.subgroupOf Tmax)
      have hQleK : Q.subgroupOf Tmax ≤ K := by
        intro x hx
        exact Subgroup.mem_subgroupOf.mpr
          ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
      exact isInvariant_subgroupOf_of_le_normalizer hW2normK hW2normQ hQleK
    letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
      quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
    ∀ q : K ⧸ N, a • q = q → q = 1 := by
  classical
  dsimp only
  rcases hTtypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  have hQleT : Q ≤ Tmax := Section12.section16MFSubgroup_le hQMF
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
  have hQVdisj : Disjoint Q V := hDerComp.2.2.2
  have hKnormal : K.Normal := by
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [K, hDerEq] using hDerNormal
  letI : K.Normal := hKnormal
  let Qsub : Subgroup Tmax := Q.subgroupOf Tmax
  let VsubT : Subgroup Tmax := V.subgroupOf Tmax
  letI : Qsub.Normal := hQnormal
  have hNnormal : N.Normal := hQnormal.subgroupOf K
  letI : N.Normal := hNnormal
  have hW2normK : W2.subgroupOf Tmax ≤ Subgroup.normalizer (K : Set Tmax) :=
    Subgroup.le_normalizer_of_normal (H := K)
  have hW2normQ :
      W2.subgroupOf Tmax ≤ Subgroup.normalizer (Q.subgroupOf Tmax : Set Tmax) :=
    Subgroup.le_normalizer_of_normal (H := Q.subgroupOf Tmax)
  have hQleK : Q.subgroupOf Tmax ≤ K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  have hNinv : IsInvariant (W2.subgroupOf Tmax) K N :=
    isInvariant_subgroupOf_of_le_normalizer hW2normK hW2normQ hQleK
  letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
    quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
  let Sg : Subgroup G := V ⊔ W2
  let VsubS : Subgroup Sg := V.subgroupOf Sg
  let WsubS : Subgroup Sg := W2.subgroupOf Sg
  have hfrobS : IsFrobeniusGroupWithKernelComplement VsubS WsubS := by
    simpa [section12FrobeniusJoinWithKernel, Sg, VsubS, WsubS] using hfrobVW2
  haveI : VsubS.Normal := hfrobS.normal
  have hcentW :
      ∀ r : WsubS, r ≠ 1 → elementCentralizerIn VsubS (r : Sg) = ⊥ :=
    (lemma_3_1 (G := Sg) VsubS WsubS
      hfrobS.kernel_ne_bot hfrobS.complement_ne_bot hfrobS.normal
      hfrobS.isComplement').1 hfrobS
  have haW2G : ((a : Tmax) : G) ∈ W2 :=
    Subgroup.mem_subgroupOf.mp a.property
  have haS_mem : ((a : Tmax) : G) ∈ Sg :=
    (le_sup_right : W2 ≤ Sg) haW2G
  let aS : Sg := ⟨((a : Tmax) : G), haS_mem⟩
  let aR : WsubS := ⟨aS, by
    exact Subgroup.mem_subgroupOf.mpr haW2G⟩
  have haRne : aR ≠ 1 := by
    intro haR
    apply ha
    have haG : ((a : Tmax) : G) = 1 := by
      have hS := congrArg (fun z : WsubS => (z : Sg)) haR
      exact congrArg (fun z : Sg => (z : G)) hS
    exact Subtype.ext (Subtype.ext haG)
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k hfix
  have hK_eq : K = Qsub ⊔ VsubT := by
    dsimp [K, Qsub, VsubT]
    rw [Subgroup.subgroupOf_sup hQleT hVleT]
  have hk_mem_sup : (k : Tmax) ∈ Qsub ⊔ VsubT := by
    simpa [K, hK_eq] using k.property
  rcases (Subgroup.mem_sup_of_normal_left (x := (k : Tmax)) (s := Qsub) (t := VsubT)).1
      hk_mem_sup with
    ⟨q0, hq0Q, v0, hv0V, hk_eq⟩
  have hq0K : q0 ∈ K := by
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hq0Q))
  have hv0K : v0 ∈ K := by
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : V ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hv0V))
  let qK : K := ⟨q0, hq0K⟩
  let vK : K := ⟨v0, hv0K⟩
  have hk_eq_K : k = qK * vK := by
    apply Subtype.ext
    simpa [qK, vK] using hk_eq.symm
  have hqKN : qK ∈ N := by
    simpa [N, Qsub, qK, Subgroup.mem_subgroupOf] using hq0Q
  have hmk_qK : QuotientGroup.mk' N qK = 1 :=
    (QuotientGroup.eq_one_iff (N := N) qK).2 hqKN
  have hmk_k_v : QuotientGroup.mk' N k = QuotientGroup.mk' N vK := by
    rw [hk_eq_K, map_mul, hmk_qK, one_mul]
  have hqeq : QuotientGroup.mk' N (a • k) = QuotientGroup.mk' N k := by
    simpa using hfix
  have haqKN : a • qK ∈ N :=
    (IsInvariant.invariant (A := W2.subgroupOf Tmax) (G := K) (H := N) a qK).1 hqKN
  have hmk_aqK : QuotientGroup.mk' N (a • qK) = 1 :=
    (QuotientGroup.eq_one_iff (N := N) (a • qK)).2 haqKN
  have hsmul_k : a • k = (a • qK) * (a • vK) := by
    rw [hk_eq_K, smul_mul']
  have hmk_ak_av : QuotientGroup.mk' N (a • k) = QuotientGroup.mk' N (a • vK) := by
    rw [hsmul_k, map_mul, hmk_aqK, one_mul]
  have hqeqv : QuotientGroup.mk' N (a • vK) = QuotientGroup.mk' N vK :=
    hmk_ak_av.symm.trans (hqeq.trans hmk_k_v)
  have hdivVN : (a • vK) / vK ∈ N :=
    (QuotientGroup.eq_iff_div_mem).1 hqeqv
  have hdivVQ :
      ((a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹) ∈ Qsub := by
    have htmp : (((a • vK) / vK : K) : Tmax) ∈ Qsub := by
      change ((a • vK) / vK : K) ∈ (Q.subgroupOf Tmax).subgroupOf K at hdivVN
      exact Subgroup.mem_subgroupOf.mp hdivVN
    have hsmul_v :
        ((a • vK : K) : Tmax) = (a : Tmax) * v0 * (a : Tmax)⁻¹ := by
      simp [vK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hdiv_coe :
        (((a • vK) / vK : K) : Tmax) =
          (a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹ := by
      rw [div_eq_mul_inv]
      change ((a • vK : K) : Tmax) * ((vK : K) : Tmax)⁻¹ =
        (a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹
      rw [hsmul_v]
    exact hdiv_coe ▸ htmp
  have hv0G : (v0 : G) ∈ V := Subgroup.mem_subgroupOf.mp hv0V
  have hconjV :
      ((a : Tmax) * v0 * (a : Tmax)⁻¹) ∈ VsubT := by
    have hvS_mem : (v0 : G) ∈ Sg := (le_sup_left : V ≤ Sg) hv0G
    let vS : Sg := ⟨(v0 : G), hvS_mem⟩
    have hvVsub : vS ∈ VsubS := by
      exact Subgroup.mem_subgroupOf.mpr hv0G
    have hconjVsub : aS * vS * aS⁻¹ ∈ VsubS :=
      (inferInstance : VsubS.Normal).conj_mem vS hvVsub aS
    have hconjVG : ((a : Tmax) : G) * (v0 : G) * ((a : Tmax) : G)⁻¹ ∈ V := by
      simpa [VsubS, aS, vS, Subgroup.mem_subgroupOf] using hconjVsub
    exact Subgroup.mem_subgroupOf.mpr hconjVG
  have hdivVV :
      ((a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹) ∈ VsubT :=
    VsubT.mul_mem hconjV (VsubT.inv_mem hv0V)
  have hdiv_one_G :
      (((a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹ : Tmax) : G) = 1 := by
    have hbot :
        (((a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹ : Tmax) : G) ∈
          (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hQVdisj)
        (Subgroup.mem_subgroupOf.mp hdivVQ)
        (Subgroup.mem_subgroupOf.mp hdivVV)
    simpa using hbot
  have hdiv_one_T :
      (a : Tmax) * v0 * (a : Tmax)⁻¹ * v0⁻¹ = 1 :=
    Subtype.ext hdiv_one_G
  have hconj_eq_v : (a : Tmax) * v0 * (a : Tmax)⁻¹ = v0 :=
    mul_inv_eq_one.mp hdiv_one_T
  have hav_comm : (a : Tmax) * v0 = v0 * (a : Tmax) := by
    have h := congrArg (fun x : Tmax => x * (a : Tmax)) hconj_eq_v
    simpa [mul_assoc] using h
  have hv0_one_T : v0 = 1 := by
    have hvS_mem : (v0 : G) ∈ Sg := (le_sup_left : V ≤ Sg) hv0G
    let vS : Sg := ⟨(v0 : G), hvS_mem⟩
    have hvVsub : vS ∈ VsubS := by
      exact Subgroup.mem_subgroupOf.mpr hv0G
    have hvcentral : vS ∈ Subgroup.centralizer ({(aR : Sg)} : Set Sg) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change ((v0 * (a : Tmax) : Tmax) : G) =
        (((a : Tmax) * v0 : Tmax) : G)
      exact congrArg (fun x : Tmax => (x : G)) hav_comm.symm
    have hvCent : vS ∈ elementCentralizerIn VsubS (aR : Sg) :=
      ⟨hvVsub, hvcentral⟩
    have hvBot : vS ∈ (⊥ : Subgroup Sg) := by
      rw [← hcentW aR haRne]
      exact hvCent
    have hvS_one : vS = 1 := by
      change vS = 1 at hvBot
      exact hvBot
    have hvS_one_G : ((vS : Sg) : G) = ((1 : Sg) : G) := by
      exact Subtype.ext_iff.mp hvS_one
    have hvG : (v0 : G) = 1 := by
      change ((vS : Sg) : G) = ((1 : Sg) : G)
      exact hvS_one_G
    exact Subtype.ext hvG
  have hkQ : (k : Tmax) ∈ Qsub := by
    have hk_eq_q : (k : Tmax) = q0 := by
      calc
        (k : Tmax) = q0 * v0 := by simpa using hk_eq.symm
        _ = q0 := by rw [hv0_one_T, mul_one]
    rw [hk_eq_q]
    exact hq0Q
  have hkN : k ∈ N := by
    simpa [N, Qsub, Subgroup.mem_subgroupOf] using hkQ
  exact (QuotientGroup.eq_one_iff (N := N) k).2 hkN

public theorem section14_quotientCharacterInflation_conjugate_kernel_eq
    {M : Type u} [Group M] [Finite M]
    {K H : Subgroup M}
    [K.Normal] [(H.subgroupOf K).Normal]
    [IsMulCommutative (K ⧸ H.subgroupOf K)]
    (k : K)
    (ψ : (K ⧸ H.subgroupOf K) →* ℂˣ) :
    Section1.conjugateOnNormal K
        (Section1.quotientCharacterInflation H K ψ) (k : M) =
      Section1.quotientCharacterInflation H K ψ := by
  classical
  ext x
  let y : K := ⟨(k : M) * (x : M) * (k : M)⁻¹,
    (inferInstance : K.Normal).conj_mem (x : M) x.2 (k : M)⟩
  change ((ψ ((y : K) : K ⧸ H.subgroupOf K) : ℂˣ) : ℂ) =
    ((ψ ((x : K) : K ⧸ H.subgroupOf K) : ℂˣ) : ℂ)
  have hy : y = k * x * k⁻¹ := by
    apply Subtype.ext
    rfl
  have hq : (y : K ⧸ H.subgroupOf K) =
      ((x : K) : K ⧸ H.subgroupOf K) := by
    letI : CommGroup (K ⧸ H.subgroupOf K) := IsMulCommutative.instCommGroup
    rw [hy]
    change QuotientGroup.mk' (H.subgroupOf K) (k * x * k⁻¹) =
      QuotientGroup.mk' (H.subgroupOf K) x
    rw [map_mul, map_mul, map_inv]
    simp [mul_assoc]
  rw [hq]

public theorem section14_typeP_quotientCharacterInflation_smul_eq_conjugateOnNormal
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hNinv : IsInvariant (W2.subgroupOf Tmax)
      ((Q ⊔ V).subgroupOf Tmax)
      ((Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax))) :
    let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
    let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
    letI : K.Normal := hKnormal
    letI : N.Normal := hQnormal.subgroupOf K
    letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
      quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
      Section10.characterGroupContragredientMulDistribMulAction
        (W2.subgroupOf Tmax) (K ⧸ N)
    ∀ a : W2.subgroupOf Tmax,
    ∀ ψ : (K ⧸ N) →* ℂˣ,
      Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K (a • ψ) =
        Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ)
          ((a⁻¹ : W2.subgroupOf Tmax) : Tmax) := by
  classical
  dsimp only
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  letI : K.Normal := hKnormal
  letI : N.Normal := hQnormal.subgroupOf K
  letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
    quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction
      (W2.subgroupOf Tmax) (K ⧸ N)
  intro a ψ
  ext x
  change (((a • ψ) ((x : K) : K ⧸ N) : ℂˣ) : ℂ) =
    ((ψ ((((a⁻¹ : W2.subgroupOf Tmax) • x : K) : K) : K ⧸ N) : ℂˣ) : ℂ)
  have h := Section10.characterGroupContragredient_smul_apply
    (A := W2.subgroupOf Tmax) (Q := K ⧸ N) a ψ ((x : K) : K ⧸ N)
  simpa using congrArg (fun z : ℂˣ => (z : ℂ)) h

public theorem section14_typeP_inducedCF_quotientCharacterInflation_smul_eq
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hNinv : IsInvariant (W2.subgroupOf Tmax)
      ((Q ⊔ V).subgroupOf Tmax)
      ((Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax))) :
    let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
    let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
    letI : K.Normal := hKnormal
    letI : N.Normal := hQnormal.subgroupOf K
    letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
      quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
      Section10.characterGroupContragredientMulDistribMulAction
        (W2.subgroupOf Tmax) (K ⧸ N)
    ∀ a : W2.subgroupOf Tmax,
    ∀ ψ : (K ⧸ N) →* ℂˣ,
      Section1.inducedCF K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K (a • ψ)) =
        Section1.inducedCF K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ) := by
  classical
  dsimp only
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  letI : K.Normal := hKnormal
  letI : N.Normal := hQnormal.subgroupOf K
  letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
    quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction
      (W2.subgroupOf Tmax) (K ⧸ N)
  intro a ψ
  have htheta :=
    section14_typeP_quotientCharacterInflation_smul_eq_conjugateOnNormal
      (Q := Q) (V := V) (W2 := W2) hQnormal hKnormal hNinv a ψ
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (Q.subgroupOf Tmax) K ψ with
    ⟨n, ρ, _hρirr, hρchar⟩
  have hphi :
      Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K (a • ψ) =
        Section1.conjugateOrbitConj K ρ.character
          (Section1.conjugateOrbitFiber K ρ.character
            ((a⁻¹ : W2.subgroupOf Tmax) : Tmax)) := by
    rw [htheta, hρchar]
    rfl
  have hind := Section1.proposition_1_5_c_conjugate_orbit_canonical
    K ρ
    (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K (a • ψ))
    (Section1.conjugateOrbitFiber K ρ.character
      ((a⁻¹ : W2.subgroupOf Tmax) : Tmax)) hphi
  simpa only [← hρchar] using hind

public theorem section14_typeP_inducedCF_quotientCharacterInflation_eq_of_orbitRel
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hNinv : IsInvariant (W2.subgroupOf Tmax)
      ((Q ⊔ V).subgroupOf Tmax)
      ((Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax))) :
    let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
    let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
    letI : K.Normal := hKnormal
    letI : N.Normal := hQnormal.subgroupOf K
    letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
      quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
      Section10.characterGroupContragredientMulDistribMulAction
        (W2.subgroupOf Tmax) (K ⧸ N)
    letI : MulAction (W2.subgroupOf Tmax)
        {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} :=
      Section10.nonidentitySubMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ)
    ∀ ψ η : {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1},
      MulAction.orbitRel (W2.subgroupOf Tmax)
        {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} ψ η →
        Section1.inducedCF K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1) =
        Section1.inducedCF K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1) := by
  classical
  dsimp only
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  letI : K.Normal := hKnormal
  letI : N.Normal := hQnormal.subgroupOf K
  letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
    quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction
      (W2.subgroupOf Tmax) (K ⧸ N)
  letI : MulAction (W2.subgroupOf Tmax)
      {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} :=
    Section10.nonidentitySubMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ)
  intro ψ η hrel
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨a, ha⟩
  rw [← ha]
  have hproj : ((a • η : {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1}).1) = a • η.1 :=
    Section10.nonidentitySubMulAction_val
      (A := W2.subgroupOf Tmax) (G := (K ⧸ N) →* ℂˣ) a η
  rw [hproj]
  exact section14_typeP_inducedCF_quotientCharacterInflation_smul_eq
    (Q := Q) (V := V) (W2 := W2) hQnormal hKnormal hNinv a η.1

public theorem section14_typeP_orbitRel_of_inducedCF_quotientCharacterInflation_eq
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V W2 : Subgroup G}
    (hQnormal : (Q.subgroupOf Tmax).Normal)
    (hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal)
    (hNinv : IsInvariant (W2.subgroupOf Tmax)
      ((Q ⊔ V).subgroupOf Tmax)
      ((Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax)))
    (hTcomp : section12ComplementIn Tmax (Q ⊔ V) W2)
    (hquotComm :
      IsMulCommutative
        (((Q ⊔ V).subgroupOf Tmax) ⧸
          (Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax))) :
    let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
    let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
    letI : K.Normal := hKnormal
    letI : N.Normal := hQnormal.subgroupOf K
    letI : IsMulCommutative (K ⧸ N) := hquotComm
    letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
      quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
    letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
      Section10.characterGroupContragredientMulDistribMulAction
        (W2.subgroupOf Tmax) (K ⧸ N)
    letI : MulAction (W2.subgroupOf Tmax)
        {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} :=
      Section10.nonidentitySubMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ)
    ∀ ψ η : {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1},
      Section1.inducedCF K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1) =
        Section1.inducedCF K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1) →
      MulAction.orbitRel (W2.subgroupOf Tmax)
        {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} ψ η := by
  classical
  dsimp only
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  let R : Subgroup Tmax := W2.subgroupOf Tmax
  have hNnormal : N.Normal := hQnormal.subgroupOf K
  letI : K.Normal := hKnormal
  letI : N.Normal := hNnormal
  letI : IsMulCommutative (K ⧸ N) := hquotComm
  letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
    quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction
      (W2.subgroupOf Tmax) (K ⧸ N)
  letI : MulAction (W2.subgroupOf Tmax)
      {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} :=
    Section10.nonidentitySubMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ)
  intro ψ η hInd
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (Q.subgroupOf Tmax) K ψ.1 with
    ⟨_nψ, ρψ, hρψirr, hρψchar⟩
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (Q.subgroupOf Tmax) K η.1 with
    ⟨_nη, ρη, hρηirr, hρηchar⟩
  have hIndRep : Section1.inducedCF K ρψ.character =
      Section1.inducedCF K ρη.character := by
    have h := hInd
    rw [hρψchar, hρηchar] at h
    exact h
  rcases Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
      K ρψ ρη hρψirr hρηirr hIndRep with ⟨i, hi⟩
  revert hi
  refine Quotient.inductionOn i ?_
  intro g hi
  have hconj :
      Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1 =
        Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1) g := by
    rw [hρψchar, hρηchar]
    simpa [Section1.conjugateOrbitConj, Section1.conjugateOrbitFiber] using hi
  have hKR : K.IsComplement' R := by
    simpa [K, R] using
      Section12.section12ComplementIn_left_normal_isComplement'
        (G := G) (M := Tmax) (K := Q ⊔ V) (L := W2) hTcomp hKnormal
  rcases hKR.existsUnique g with ⟨⟨kT, rT⟩, hmul, _huniq⟩
  let k : K := kT
  let a : W2.subgroupOf Tmax := rT
  have hgka : g = (k : Tmax) * (a : Tmax) := by
    simpa [k, a, R] using hmul.symm
  have hconj_a :
      Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1) g =
        Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1)
          (a : Tmax) := by
    rw [hgka]
    ext x
    let y : K := ⟨(a : Tmax) * (x : Tmax) * (a : Tmax)⁻¹,
      (inferInstance : K.Normal).conj_mem (x : Tmax) x.2 (a : Tmax)⟩
    have htriv := congrFun
      (section14_quotientCharacterInflation_conjugate_kernel_eq
        (M := Tmax) (K := K) (H := Q.subgroupOf Tmax) k η.1) y
    change Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1
        ⟨((k : Tmax) * (a : Tmax)) * (x : Tmax) *
            ((k : Tmax) * (a : Tmax))⁻¹,
          (inferInstance : K.Normal).conj_mem
            (x : Tmax) x.2 ((k : Tmax) * (a : Tmax))⟩ =
      Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1 y
    simpa [Section1.conjugateOnNormal, y, mul_assoc] using htriv
  have hsmul :=
    section14_typeP_quotientCharacterInflation_smul_eq_conjugateOnNormal
      (Q := Q) (V := V) (W2 := W2) hQnormal hKnormal hNinv
      (a⁻¹ : W2.subgroupOf Tmax) η.1
  have hψeq : ψ.1 = (a⁻¹ : W2.subgroupOf Tmax) • η.1 := by
    apply Section6.quotientCharacterInflation_injective (Q.subgroupOf Tmax) K
    change Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1 =
      Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K
        ((a⁻¹ : W2.subgroupOf Tmax) • η.1)
    rw [hconj, hconj_a]
    simpa [inv_inv] using hsmul.symm
  rw [MulAction.orbitRel_apply]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨a⁻¹, ?_⟩
  apply Subtype.ext
  have hproj : ((a⁻¹ • η : {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1}).1) =
      (a⁻¹ : W2.subgroupOf Tmax) • η.1 :=
    Section10.nonidentitySubMulAction_val
      (A := W2.subgroupOf Tmax) (G := (K ⧸ N) →* ℂˣ)
      (a⁻¹ : W2.subgroupOf Tmax) η
  rw [hproj]
  exact hψeq.symm

public theorem section14_theorem_14_9_late_type_T1_calt1_card_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          (hQnormal : (Q.subgroupOf Tmax).Normal) →
            letI : ((Q.subgroupOf Tmax).subgroupOf
                ((Q ⊔ V).subgroupOf Tmax)).Normal :=
              hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
            ∀ T1T : Finset (Section1.ClassFunction Tmax),
              Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
                ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) := by
  classical
  intro hctx hLateType hTtypeP hQnormal T1T hCalT1
  have hVcard :
      Nat.card V = v :=
    section14_v_card_eq_of_late_type_context
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hctx
  have _hLateType := hLateType
  have hTtypeP0 : Section8.typePDefinitionData Tmax Q V W2 W1 := hTtypeP
  have hT13 :=
    Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  rcases hT13 with
    ⟨_hTmaxMF, _htypeT, _htypeII_of_pq, hVcomm, hfrobVW2, _hQelem,
      _hQcard, _hv, _hTfamCoh, _hTI, _hTauT, _hnormT⟩
  rcases hTtypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  have hQleT : Q ≤ Tmax := Section12.section16MFSubgroup_le hQMF
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hW2leT : W2 ≤ Tmax := hTcomp.2.1
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
  have hQVdisj : Disjoint Q V := hDerComp.2.2.2
  have hTcompQV : section12ComplementIn Tmax (Q ⊔ V) W2 := by
    simpa [hDerEq] using hTcomp
  let K : Subgroup Tmax := (Q ⊔ V).subgroupOf Tmax
  let N : Subgroup K := (Q.subgroupOf Tmax).subgroupOf K
  have hKnormal : K.Normal := by
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [K, hDerEq] using hDerNormal
  letI : K.Normal := hKnormal
  have hNnormal : N.Normal := hQnormal.subgroupOf K
  letI : N.Normal := hNnormal
  have hW2normK : W2.subgroupOf Tmax ≤ Subgroup.normalizer (K : Set Tmax) :=
    Subgroup.le_normalizer_of_normal (H := K)
  have hW2normQ :
      W2.subgroupOf Tmax ≤ Subgroup.normalizer (Q.subgroupOf Tmax : Set Tmax) :=
    Subgroup.le_normalizer_of_normal (H := Q.subgroupOf Tmax)
  have hQleK : Q.subgroupOf Tmax ≤ K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  have hNinv : IsInvariant (W2.subgroupOf Tmax) K N :=
    isInvariant_subgroupOf_of_le_normalizer hW2normK hW2normQ hQleK
  letI : IsInvariant (W2.subgroupOf Tmax) K N := hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) (K ⧸ N) :=
    quotientMulDistribMulAction (A := W2.subgroupOf Tmax) (G := K) N hNinv
  letI : MulDistribMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) :=
    Section10.characterGroupContragredientMulDistribMulAction
      (W2.subgroupOf Tmax) (K ⧸ N)
  letI : MulAction (W2.subgroupOf Tmax) {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} :=
    Section10.nonidentitySubMulAction (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ)
  have hquotComm :
      IsMulCommutative (K ⧸ N) := by
    dsimp [K, N]
    exact section14_typeP_quotient_commutative_of_sup hQleT hVleT hQnormal hVcomm
  letI : IsMulCommutative (K ⧸ N) := hquotComm
  have hfree :
      ∀ a : W2.subgroupOf Tmax, a ≠ 1 →
        ∀ x : K ⧸ N, a • x = x → x = 1 := by
    intro a ha x hx
    dsimp [K, N]
    exact section14_typeP_quotient_fixed_eq_one_of_W2_ne_one
      hTtypeP0 hQnormal hfrobVW2 a ha x hx
  have horbit :
      Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
        ((K ⧸ N) →* ℂˣ)) =
        (Nat.card (K ⧸ N) - 1) / Nat.card (W2.subgroupOf Tmax) := by
    exact section14_linearCharacter_orbit_card_eq_div
      (A := W2.subgroupOf Tmax) (Q := K ⧸ N) hfree
  have hquotCard : Nat.card (K ⧸ N) = v := by
    calc
      Nat.card (K ⧸ N) = Nat.card V := by
        dsimp [K, N]
        exact section14_typeP_quotient_card_eq_card_V_of_sup
          hQleT hVleT hQnormal hQVdisj
      _ = v := hVcard
  have hW2card : Nat.card W2 = p :=
    section14_theorem_14_2_a_cardW2_of_sourceData hctx.1
  have hAcard : Nat.card (W2.subgroupOf Tmax) = p :=
    (natCard_subgroupOf_eq W2 Tmax hW2leT).trans hW2card
  have horbit_vp :
      Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
        ((K ⧸ N) →* ℂˣ)) = (v - 1) / p := by
    have hquotCardFintype : Fintype.card (K ⧸ N) = v := by
      rw [← Nat.card_eq_fintype_card]
      exact hquotCard
    have hAcardFintype : Fintype.card (W2.subgroupOf Tmax) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact hAcard
    simpa [hquotCardFintype, hAcardFintype] using horbit
  have hS6 :
      Section6.inducedKernelFamily K (Q.subgroupOf Tmax) T1T := by
    simpa [K] using section14_inducedKernelFamily_of_kernelInducedFamily_self hCalT1
  let β : Type u := {χ : Section1.ClassFunction Tmax // χ ∈ T1T}
  let f :
      Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax) ((K ⧸ N) →* ℂˣ) → β :=
    Quotient.lift
      (fun ψ : {ψ : (K ⧸ N) →* ℂˣ // ψ ≠ 1} =>
        (⟨Section1.inducedCF K
            (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1), by
          exact (hS6.2
            (Section1.inducedCF K
              (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1))).mpr
            ⟨Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1,
              Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
                (Q.subgroupOf Tmax) K ψ.1,
              Section6.subgroupInKernel'_quotientCharacterInflation
                (Q.subgroupOf Tmax) K ψ.1,
              Section6.quotientCharacterInflation_ne_principal_of_ne_one
                (Q.subgroupOf Tmax) K ψ.2,
              rfl⟩⟩ : β))
      (by
        intro ψ η hrel
        apply Subtype.ext
        dsimp
        exact section14_typeP_inducedCF_quotientCharacterInflation_eq_of_orbitRel
          (Q := Q) (V := V) (W2 := W2) hQnormal hKnormal hNinv ψ η hrel)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    revert hxy
    refine Quotient.inductionOn₂ x y ?_
    intro ψ η hψη
    apply Quotient.sound
    apply section14_typeP_orbitRel_of_inducedCF_quotientCharacterInflation_eq
      (Q := Q) (V := V) (W2 := W2) hQnormal hKnormal hNinv hTcompQV hquotComm ψ η
    change Section1.inducedCF K
        (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K ψ.1) =
      Section1.inducedCF K
        (Section1.quotientCharacterInflation (Q.subgroupOf Tmax) K η.1)
    exact congrArg Subtype.val hψη
  have hcard_le :
      Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
        ((K ⧸ N) →* ℂˣ)) ≤ Nat.card β :=
    Nat.card_le_card_of_injective f hf_inj
  have hβcard : Nat.card β = T1T.card := by
    dsimp [β]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe T1T
  have hnat : (v - 1) / p ≤ T1T.card := by
    calc
      (v - 1) / p =
          Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
            ((K ⧸ N) →* ℂˣ)) := horbit_vp.symm
      _ ≤ Nat.card β := hcard_le
      _ = T1T.card := hβcard
  have hdiv_v : p ∣ v - 1 := by
    have horbitMul :
        Nat.card (W2.subgroupOf Tmax) *
          Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
            ((K ⧸ N) →* ℂˣ)) =
          Nat.card (K ⧸ N) - 1 :=
      section14_linearCharacter_orbit_card_mul_eq_sub_one
        (A := W2.subgroupOf Tmax) (Q := K ⧸ N) hfree
    refine ⟨Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
      ((K ⧸ N) →* ℂˣ)), ?_⟩
    have hmul_v :
        p * Nat.card (Section10.nonidentityOrbitQuotient (W2.subgroupOf Tmax)
          ((K ⧸ N) →* ℂˣ)) = v - 1 := by
      have hquotCardFintype : Fintype.card (K ⧸ N) = v := by
        rw [← Nat.card_eq_fintype_card]
        exact hquotCard
      have hAcardFintype : Fintype.card (W2.subgroupOf Tmax) = p := by
        rw [← Nat.card_eq_fintype_card]
        exact hAcard
      simpa [hAcardFintype, hquotCardFintype] using horbitMul
    exact hmul_v.symm
  have hp_pos : 0 < p := by
    rw [← hW2card]
    exact Nat.card_pos
  have hpR_ne : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp_pos.ne'
  have hcastDiv :
      (((v - 1) / p : ℕ) : ℝ) = ((v - 1 : ℕ) : ℝ) / (p : ℝ) := by
    rw [Nat.cast_div hdiv_v hpR_ne]
  rw [← hcastDiv]
  exact_mod_cast hnat

public theorem section14_theorem_14_9_late_type_T1_calt1_hypothesis52_fullData_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          ∃ d52 : Section8.section8Hypothesis52FullData Tmax (Q ⊔ V) W2 W1
              (Section8.section8CentralizerUnion
                (ambientDerivedSubgroup Tmax) (Q ⊔ V)),
            d52.tau = τT ∧
              Section13.typePFourSixSigmaAgreesOnCyclicTI
                Tmax W2 W1 d52.W d52.sigma := by
  intro hctx hLateType hTtypeP
  have _hLateType := hLateType
  have hFourSixT : Section13.typePFourSixTauSourceData Tmax Q V W2 W1 τT := by
    have hsource := hctx.1
    unfold Section13.hypothesis_13_1_sourceData at hsource
    tauto
  rcases Section13.section13_hypothesis52FullData_with_late_book_of_typePFourSix
      hTtypeP hFourSixT with
    ⟨Ms, Abook, d52, _hQle, hd52tau, hSigmaAgree, hLateBook⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := by
    rcases hTtypeP with
      ⟨_hQ, _hW2cyc, _hW2ne, _hW2hall, _hW2comp, _hVleDer, _hVnil,
        _hW2normV, hDerComp, _hQnoncyc, _hSecond, _hFitEq, _hFitLe,
        _hW1le, _hW1cyc, _hW1ne, _hCentralizer, _hHatNorm⟩
    exact hDerComp.2.2.1
  have hBook := hLateBook hLateType
  have hAbook := hBook.1
  have hMs : Ms = Q ⊔ V := hBook.2.trans hDerEq
  subst Ms
  subst Abook
  exact ⟨d52, hd52tau, hSigmaAgree⟩

public theorem section14_theorem_14_9_late_type_T1_calt1_hypothesis_5_2_b_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          (hQnormal : (Q.subgroupOf Tmax).Normal) →
            letI : ((Q.subgroupOf Tmax).subgroupOf
                ((Q ⊔ V).subgroupOf Tmax)).Normal :=
              hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
            ∀ T1T : Finset (Section1.ClassFunction Tmax),
              Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
                T1T.Nonempty →
                  Section5.hypothesis_5_2_b_statement T1T τT := by
  intro hctx hLateType hTtypeP hQnormal T1T hCalT1 hne
  have hSection8 :
      Section8.section8InducedNonkernelFamily Tmax (Q ⊔ V) T1T :=
    section14_theorem_14_9_late_type_T1_section8InducedNonkernel_of_calt
      hTtypeP hne hCalT1
  rcases
    section14_theorem_14_9_late_type_T1_calt1_hypothesis52_fullData_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP with
    ⟨d52, hd52τ, _hSigmaAgree⟩
  have h52 :
      Section5.hypothesis_5_2_statement T1T d52.tau :=
    Section8.theorem_8_15_hypothesis_5_2_of_fullData
      (G := G) (M := Tmax) (Ms := Q ⊔ V) (W1 := W2) (W2 := W1)
      (A := Section8.section8CentralizerUnion
        (ambientDerivedSubgroup Tmax) (Q ⊔ V))
      (S := T1T) (inferInstance : IsMinCE G) d52 hSection8
  rw [hd52τ] at h52
  rcases h52 with ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  have _hQnormal := hQnormal
  exact h52b

public theorem section14_theorem_14_9_late_type_T1_calt_core_source_character_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          (hQnormal : (Q.subgroupOf Tmax).Normal) →
            letI : ((Q.subgroupOf Tmax).subgroupOf
                ((Q ⊔ V).subgroupOf Tmax)).Normal :=
              hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
            ∀ T1T : Finset (Section1.ClassFunction Tmax),
              Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
                ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
                  Section5.hypothesis_5_2_b_statement T1T τT := by
  intro hctx hLateType hTtypeP hQnormal T1T hCalT1
  have hcard :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) :=
    section14_theorem_14_9_late_type_T1_calt1_card_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP hQnormal T1T hCalT1
  have hne : T1T.Nonempty :=
    section14_theorem_14_9_late_type_T1_calt_nonempty_of_context
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hTtypeP hQnormal T1T hCalT1
  have h52b : Section5.hypothesis_5_2_b_statement T1T τT :=
    section14_theorem_14_9_late_type_T1_calt1_hypothesis_5_2_b_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP hQnormal T1T hCalT1 hne
  exact ⟨hcard, h52b⟩

public theorem section14_theorem_14_9_late_type_T1_calt_core_source_remaining_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          (hQnormal : (Q.subgroupOf Tmax).Normal) →
            letI : ((Q.subgroupOf Tmax).subgroupOf
                ((Q ⊔ V).subgroupOf Tmax)).Normal :=
              hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
            ∀ T1T : Finset (Section1.ClassFunction Tmax),
              Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
                ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
                  Section5.hypothesis_5_2_b_statement T1T τT ∧
                  Section6.frobeniusQuotientWithKernel
                    ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) := by
  intro hctx hLateType hTtypeP hQnormal T1T hCalT1
  rcases section14_theorem_14_9_late_type_T1_calt_core_source_character_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP hQnormal T1T hCalT1 with
    ⟨hcard, h52b⟩
  have hT13 :=
    Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  rcases hT13 with
    ⟨_hTmaxMF, _htypeT, _htypeII_of_pq, _hVcomm, hfrobVW2, _hQelem,
      _hQcard, _hv, _hTfamCoh, _hTI, _hTauT, _hnormT⟩
  rcases hTtypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  have hQleT : Q ≤ Tmax := Section12.section16MFSubgroup_le hQMF
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hW2leT : W2 ≤ Tmax := hTcomp.2.1
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
  have hQVdisj : Disjoint Q V := hDerComp.2.2.2
  have hTcompQV : section12ComplementIn Tmax (Q ⊔ V) W2 := by
    simpa [hDerEq] using hTcomp
  have hKnormal : ((Q ⊔ V).subgroupOf Tmax).Normal := by
    have hDerNormal :
        ((ambientDerivedSubgroup Tmax).subgroupOf Tmax).Normal :=
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)).2
    simpa [hDerEq] using hDerNormal
  have hfrobQuot :
      Section6.frobeniusQuotientWithKernel
        ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) :=
    section14_typeP_frobeniusQuotientWithKernel_of_frobeniusJoin
      hQleT hVleT hW2leT hQnormal hKnormal hQVdisj hTcompQV hfrobVW2
  exact ⟨hcard, h52b, hfrobQuot⟩

public theorem section14_theorem_14_9_late_type_T1_calt_core_source_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          (hQnormal : (Q.subgroupOf Tmax).Normal) →
            letI : ((Q.subgroupOf Tmax).subgroupOf
                ((Q ⊔ V).subgroupOf Tmax)).Normal :=
              hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
            ∀ T1T : Finset (Section1.ClassFunction Tmax),
              Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T →
                ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
                  Section5.hypothesis_5_2_b_statement T1T τT ∧
                  IsMulCommutative
                    (((Q ⊔ V).subgroupOf Tmax) ⧸
                      (Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax)) ∧
                  Section6.frobeniusQuotientWithKernel
                    ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) := by
  intro hctx hLateType hTtypeP hQnormal T1T hCalT1
  have hT13 :=
    Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  rcases hT13 with
    ⟨_hTmaxMF, _htypeT, _htypeII_of_pq, hVcomm, _hfrobVW2, _hQelem,
      _hQcard, _hv, _hTfamCoh, _hTI, _hTauT, _hnormT⟩
  rcases hTtypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
      _hVnil, _hW2norm, _hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  have hQleT : Q ≤ Tmax := Section12.section16MFSubgroup_le hQMF
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hquotComm :
      IsMulCommutative
        (((Q ⊔ V).subgroupOf Tmax) ⧸
          (Q.subgroupOf Tmax).subgroupOf ((Q ⊔ V).subgroupOf Tmax)) :=
    section14_typeP_quotient_commutative_of_sup hQleT hVleT hQnormal hVcomm
  rcases section14_theorem_14_9_late_type_T1_calt_core_source_remaining_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType
      (⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
        _hVnil, _hW2norm, _hDerComp, _hQnoncyc, _hSecond, _hFit,
        _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩)
      hQnormal T1T hCalT1 with
    ⟨hcard, h52b, hfrobQuot⟩
  exact ⟨hcard, h52b, hquotComm, hfrobQuot⟩

public theorem section14_theorem_14_9_late_type_T1_calt_core_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          section14_theorem_14_9_late_type_T1CalTCoreSourceData
            Tmax Q V τT p v := by
  classical
  intro hctx hLateType hTtypeP T1T hCalT1
  have hTtypeP0 : Section8.typePDefinitionData Tmax Q V W2 W1 := hTtypeP
  have hT13 :=
    Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  rcases hT13 with
    ⟨_hTmaxMF, _htypeT, _htypeII_of_pq, _hVcomm, hfrobVW2, _hQelem,
      _hQcard, _hv, _hTfamCoh, _hTI, _hTauT, _hnormT⟩
  have hDsolv : Group.IsSolvable (ambientDerivedSubgroup Tmax) :=
    Section9.typePDefinitionData_ambientDerived_solvable_sec9 hTtypeP0
  rcases hTtypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, hVleDer,
      _hVnil, _hW2norm, hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  have hDerEq : ambientDerivedSubgroup Tmax = Q ⊔ V := hDerComp.2.2.1
  have hQnormal : (Q.subgroupOf Tmax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hQMF
  have hDleT : ambientDerivedSubgroup Tmax ≤ Tmax :=
    section12_ambientDerivedSubgroup_le
  have hKsolv : Group.IsSolvable ((Q ⊔ V).subgroupOf Tmax) := by
    have hDsolvSub : Group.IsSolvable ((ambientDerivedSubgroup Tmax).subgroupOf Tmax) := by
      let e := Subgroup.subgroupOfEquivOfLe
        (H := ambientDerivedSubgroup Tmax) (K := Tmax) hDleT
      let _ : Group.IsSolvable (ambientDerivedSubgroup Tmax) := hDsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := e.toMonoidHom) e.injective
    rw [hDerEq] at hDsolvSub
    exact hDsolvSub
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hVne : V ≠ ⊥ := by
    let S : Subgroup G := V ⊔ W2
    let Vsub : Subgroup S := V.subgroupOf S
    have hVsub_ne : Vsub ≠ ⊥ := hfrobVW2.kernel_ne_bot
    intro hVbot
    have hVsub_bot : Vsub = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxV : (x : G) ∈ V := by
          simpa [Vsub, Subgroup.mem_subgroupOf] using hx
        have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
          simpa [hVbot] using hxV
        exact Subtype.ext (by simpa using hxbot)
      · intro hx
        have hxone : x = 1 := by simpa using hx
        rw [hxone]
        exact Subgroup.one_mem Vsub
    exact hVsub_ne hVsub_bot
  have hQleK :
      Q.subgroupOf Tmax ≤ (Q ⊔ V).subgroupOf Tmax := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : Q ≤ Q ⊔ V) (Subgroup.mem_subgroupOf.mp hx))
  have hQneK :
      Q.subgroupOf Tmax ≠ (Q ⊔ V).subgroupOf Tmax := by
    intro hEq
    apply hVne
    apply le_antisymm
    · intro x hxV
      have hxT : x ∈ Tmax := hVleT hxV
      have hxK : (⟨x, hxT⟩ : Tmax) ∈ (Q ⊔ V).subgroupOf Tmax :=
        Subgroup.mem_subgroupOf.mpr ((le_sup_right : V ≤ Q ⊔ V) hxV)
      have hxQsub : (⟨x, hxT⟩ : Tmax) ∈ Q.subgroupOf Tmax := by
        simpa [hEq] using hxK
      have hxQ : x ∈ Q := Subgroup.mem_subgroupOf.mp hxQsub
      have hxBot : x ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp hDerComp.2.2.2) hxQ hxV
      exact hxBot
    · exact bot_le
  have hQltK : Q.subgroupOf Tmax < (Q ⊔ V).subgroupOf Tmax :=
    lt_of_le_of_ne hQleK hQneK
  letI : ((Q.subgroupOf Tmax).subgroupOf
      ((Q ⊔ V).subgroupOf Tmax)).Normal :=
    hQnormal.subgroupOf ((Q ⊔ V).subgroupOf Tmax)
  have hS6 :
      Section6.inducedKernelFamily
        ((Q ⊔ V).subgroupOf Tmax) (Q.subgroupOf Tmax) T1T :=
    section14_inducedKernelFamily_of_kernelInducedFamily_self hCalT1
  rcases section14_theorem_14_9_late_type_T1_calt_core_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP0 hQnormal T1T hCalT1 with
    ⟨hcard, h52b, hquotComm, hfrobQuot⟩
  have hne : T1T.Nonempty := by
    rcases Section6.inducedKernelFamily_nonempty_of_solvable_proper
        hKsolv hQnormal hQltK hS6 with
      ⟨χ, hχ⟩
    exact ⟨χ, hχ⟩
  have hIrr :
      ∀ ζ ∈ T1T, Section1.IsIrreducibleCharacterOnGroup ζ :=
    Section6.theorem_6_8_inducedKernelFamily_irreducible_of_frobeniusQuotient
      hS6 hfrobQuot
  have hdeg :
      ∀ ζ ξ : T1T,
        Section1.degree (ζ : Section1.ClassFunction Tmax) =
          Section1.degree (ξ : Section1.ClassFunction Tmax) := by
    intro ζ ξ
    have hζ :=
      Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
        hS6 hQnormal hquotComm ζ.2
    have hξ :=
      Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
        hS6 hQnormal hquotComm ξ.2
    exact hζ.trans hξ.symm
  exact ⟨hcard, hne, h52b, hIrr, hdeg⟩

public theorem section14_theorem_14_9_late_type_T1_calt_facts_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          section14_theorem_14_9_late_type_T1CalTFactsSourceData
            Tmax Q V τT p v := by
  intro hctx hLateType hTtypeP
  exact section14_theorem_14_9_late_type_T1CalTFactsSourceData_of_core
    hTtypeP
    (section14_theorem_14_9_late_type_T1_calt_core_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP)

public theorem section14_theorem_14_9_late_type_T1_calt_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          section14_theorem_14_9_late_type_T1CalTSourceData
            Tmax Q V τT p v := by
  intro hctx hLateType hTtypeP
  exact section14_theorem_14_9_late_type_T1CalTSourceData_of_facts
    (section14_theorem_14_9_late_type_T1_calt_facts_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP)

public theorem section14_theorem_14_9_late_type_T1_calt_construction_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q) →
        Section8.typePDefinitionData Tmax Q V W2 W1 →
          section14_theorem_14_9_late_type_T1CalTConstructionData
            Tmax Q V τT p v := by
  intro hctx hLateType hTtypeP
  exact section14_theorem_14_9_late_type_T1CalTConstructionData_of_sourceData
    (section14_theorem_14_9_late_type_T1_calt_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hctx hLateType hTtypeP)

public theorem section14_theorem_14_9_late_type_T1_inducedFromNonkernel_of_calt
    {G : Type u} [Group G] [Finite G]
    {Tmax Q V : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    (hCalT1 : Section9.kernelInducedFamily Tmax (Q ⊔ V) (Q ⊔ V) Q T1T) :
    Section5.inducedFromNonkernelFamily_statement
      ((Q ⊔ V).subgroupOf Tmax) ((Q ⊔ V).subgroupOf Tmax) T1T := by
  exact Section9.inducedFromNonkernelFamily_of_kernelInducedFamily_sec9
    Tmax (Q ⊔ V) (Q ⊔ V) Q T1T hCalT1

public theorem section14_theorem_14_9_late_type_T1_sigma_orth_of_53b_extra
    {G : Type u} [Group G] [Finite G]
    {Tmax W : Subgroup G}
    {T1T : Finset (Section1.ClassFunction Tmax)}
    {τT τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {Ω : Finset (Section1.ClassFunction G)}
    (hpack : ∃ R : T1T → Finset (Section1.ClassFunction G),
      Section5.hypothesis_5_2_setup_statement T1T ∧
        Section5.hypothesis_5_2_a_statement T1T ∧
        Section5.hypothesis_5_2_b_statement T1T τT ∧
        Section5.hypothesis_5_2_c_statement T1T ∧
        Section5.hypothesis_5_2_d_statement T1T τT R ∧
        Section5.hypothesis_5_2_e_statement T1T R ∧
        Section5.theorem_5_3_b_extra_statement T1T R Ω)
    (hcoh : Section6.coherentExtension T1T τT τT1)
    (hΩ : ∀ ξ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ξ → σ ξ ∈ Ω)
    (hIrr : ∀ ζ : Section1.ClassFunction Tmax, ζ ∈ T1T →
      Section1.IsIrreducibleCharacterOnGroup ζ) :
    ∀ ζ ∈ T1T, ∀ ξ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ξ →
        Section1.scalarProduct G (σ ξ) (τT1 ζ) = 0 := by
  classical
  letI : Fintype Tmax := Fintype.ofFinite Tmax
  rcases hpack with ⟨R, hsetup, h52a, h52b, h52c, h52d, h52e, hExtra⟩
  intro ζ hζ ξ hξ
  let X : T1T := ⟨ζ, hζ⟩
  have hpairSub :
      ({(X : Section1.ClassFunction Tmax),
        Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)} :
        Finset (Section1.ClassFunction Tmax)) ⊆ T1T := by
    intro χ hχ
    have hχ' :
        χ = (X : Section1.ClassFunction Tmax) ∨
          χ = Section1.conjugateCharacter (X : Section1.ClassFunction Tmax) := by
      simpa using hχ
    rcases hχ' with hχ' | hχ'
    · simpa [X, hχ'] using hζ
    · have hbar : Section1.conjugateCharacter (X : Section1.ClassFunction Tmax) ∈ T1T :=
        (h52a X).1
      simpa [hχ'] using hbar
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction Tmax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)} :
          Finset (Section1.ClassFunction Tmax)) τT1 :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSub hcoh.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction Tmax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)} :
          Finset (Section1.ClassFunction Tmax)) τT1 :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub hcoh.2.1
  have hdiffOn :
      Section5.integerSpanOn T1T Section5.puncturedSet
        ((X : Section1.ClassFunction Tmax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)) := by
    have hXbar :
        Section1.conjugateCharacter (X : Section1.ClassFunction Tmax) ∈ T1T :=
      (h52a X).1
    have hspan :
        Section5.integerSpan T1T
          ((X : Section1.ClassFunction Tmax) -
            Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)) :=
      Section5.integerSpan_sub
        (Section5.integerSpan_of_mem T1T X.property)
        (Section5.integerSpan_of_mem T1T hXbar)
    have hXchar :
        Section1.IsCharacter (X : Section1.ClassFunction Tmax) :=
      hsetup.2 X
    have hdeg :
        Section1.degree
            ((X : Section1.ClassFunction Tmax) -
              Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)) = 0 := by
      change Section1.degree (X : Section1.ClassFunction Tmax) -
        Section1.degree
          (Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hXchar]
      simp
    exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
  have hagree :
      τT1 ((X : Section1.ClassFunction Tmax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)) =
        τT ((X : Section1.ClassFunction Tmax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Tmax)) :=
    hcoh.2.2 _ hdiffOn
  have hsubset : Section5.isSubsetSumOf (R X) (τT1 ζ) := by
    simpa [X] using
      (Section5.theorem_5_5 T1T τT R
        hsetup h52a h52b h52c h52d h52e X τT1
        hIsoPair hVirtPair hagree)
  have horth : Section5.orthogonalToFinset (R X) (σ ξ) := by
    intro ψ hψ
    have hrev : Section1.scalarProduct G ψ (σ ξ) = 0 :=
      hExtra X (hIrr (X : Section1.ClassFunction Tmax) X.property)
        hψ (hΩ ξ hξ)
    simpa [Section1.scalarProduct_star_swap] using congrArg star hrev
  rcases hsubset with ⟨E, hE, hsum⟩
  rw [hsum]
  clear hsum
  revert hE
  induction E using Finset.induction_on with
  | empty =>
      intro _hE
      simp [Section1.scalarProduct]
  | @insert a E ha ih =>
      intro hE
      rw [Finset.sum_insert ha, Section5.scalarProduct_add_right]
      have ha0 : Section1.scalarProduct G (σ ξ) a = 0 :=
        horth (hE (Finset.mem_insert_self a E))
      have hEsub : E ⊆ R X := by
        intro χ hχ
        exact hE (Finset.mem_insert_of_mem hχ)
      have hE0 :
          Section1.scalarProduct G (σ ξ) (Finset.sum E fun χ => χ) = 0 :=
        by simpa using ih hEsub
      simp [ha0, hE0]
end CFSG.Section14
