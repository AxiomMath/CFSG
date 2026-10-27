module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_4

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.5)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.5) -/


public theorem section14_semidirectProduct_of_frobenius_complement
    {G : Type u} [Group G] [Finite G]
    {L H E : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H)
    (hcomp : section12ComplementIn L H E) :
    Section2.IsInternalSemidirectProduct L H E := by
  rcases hfrob with ⟨_hHLf, hHnorm, _hfrob_rest⟩
  rcases hcomp with ⟨hHL, hEL, hsup, hdisj⟩
  refine
    { left_le := hHL
      right_le := hEL
      right_normalizes_left := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro k hk h hh
    let kL : L := ⟨k, hEL hk⟩
    let hL : L := ⟨h, hHL hh⟩
    have hhSub : hL ∈ H.subgroupOf L := hh
    have hconj : kL * hL * kL⁻¹ ∈ H.subgroupOf L :=
      hHnorm.conj_mem hL hhSub kL
    simpa [Section2.conjBy, kL, hL, Subgroup.mem_subgroupOf] using hconj
  · exact disjoint_iff.mp hdisj
  · intro c hc
    let cL : L := ⟨c, hc⟩
    haveI : (H.subgroupOf L).Normal := hHnorm
    have hsupL : H.subgroupOf L ⊔ E.subgroupOf L = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hHL hEL]
      exact Subgroup.subgroupOf_eq_top.mpr (le_of_eq hsup)
    have hcSup : cL ∈ H.subgroupOf L ⊔ E.subgroupOf L := by
      rw [hsupL]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left.mp hcSup) with ⟨hL, hhL, eL, heL, hmul⟩
    refine ⟨(hL : G), hhL, (eL : G), heL, ?_⟩
    exact (congrArg Subtype.val hmul).symm

public theorem section14_semidirect_right_le_normalizer_of_characteristic
    {G : Type u} [Group G] [Finite G]
    {L H U E : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct L H E)
    (hchar : characteristicSubgroupIn U H) :
    E ≤ Subgroup.normalizer (U : Set G) := by
  rcases hchar with ⟨hUH, hUchar⟩
  have hE_norm_H : E ≤ Subgroup.normalizer (H : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem H E ?_
    intro k h hh
    exact hsemi.right_normalizes_left k k.property h hh
  haveI : (U.subgroupOf H).Characteristic := hUchar
  have hnorm_map :
      Subgroup.normalizer (H : Set G) ≤
        Subgroup.normalizer (((U.subgroupOf H).map H.subtype : Subgroup G) : Set G) := by
    classical
    refine subgroup_le_normalizer_of_conj_mem ((U.subgroupOf H).map H.subtype)
      (Subgroup.normalizer (H : Set G)) ?_
    intro g x hx
    rcases Subgroup.mem_map.mp hx with ⟨xH, hxU, rfl⟩
    let gH : Subgroup.normalizer (H : Set G) := ⟨g, g.property⟩
    have hfix :
        Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom (U.subgroupOf H) =
          U.subgroupOf H :=
      (inferInstance : (U.subgroupOf H).Characteristic).fixed
        (Subgroup.normalizerMonoidHom H gH)
    have hxComap :
        xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom
          (U.subgroupOf H) := by
      rw [hfix]
      exact hxU
    exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxComap, by
      simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  have hmap : (U.subgroupOf H).map H.subtype = U :=
    Subgroup.map_subgroupOf_eq_of_le hUH
  rw [hmap] at hnorm_map
  exact hE_norm_H.trans hnorm_map

public theorem section14_theorem_14_5_data_of_conjugate_complement
    {G : Type u} [Group G] [Finite G]
    {L H W1 W2 Q : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H)
    (hcompY : ∃ y : G, y ∈ Q ∧ section12ComplementIn L H (W1 ⊔ W2.conjBy y)) :
    theorem_14_5_data L H W1 W2 Q := by
  rcases hcompY with ⟨y, hyQ, hcomp⟩
  exact ⟨y, hyQ, section14_semidirectProduct_of_frobenius_complement hfrob hcomp⟩

public theorem section14_theorem_14_5_pf13_17_inputs
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    Section8.typeIIDefinitionData Smax P ∧
      Section7.frobeniusWithKernel L H ∧
        U ≤ H ∧
          (section12ComplementIn L H W1 ∨
            ∃ y : G, y ∈ Q ∧
              section12ComplementIn L H (W1 ⊔ W2.conjBy y)) := by
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨hSmaxMF, _htypeS, htypeII_of_qp, _hUcomm, _hUfrob, _hPelem,
      _hPcard, _hu, _hSfamCoh, _hTI, _hTauS⟩
  rcases h143 with
    ⟨hLmax, hNormUleL, hLHMf, _hTypeI, _hDadeL, _hLfam, _hTauL,
      _hTauL₁, _hφfam, _hφirr, _hφdeg, _hβS, _hβT, _hβL,
      _hDadeNotation⟩
  have htypeII : Section8.typeIIDefinitionData Smax P := htypeII_of_qp hctx.2
  rcases Section13.theorem_13_17 Smax Tmax W W1 W2 P Q U V C D L H
      Sfam Tfam τS τT p q u v c d hctx.1 htypeII hLmax hNormUleL hLHMf with
    ⟨hfrobLH, hUH, hcomp⟩
  exact ⟨htypeII, hfrobLH, hUH, hcomp⟩

public theorem section14_theorem_14_5_W1_semidirect_relIndex_eq_q
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hsemiW1 : Section2.IsInternalSemidirectProduct L H W1) :
    H.relIndex L = q := by
  have hrel : H.relIndex L = Nat.card W1 :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemiW1
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  exact hrel.trans hq.symm

public theorem section14_theorem_14_5_pf13_19_first_of_relIndex_eq_q
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {βL βS φ : Section1.ClassFunction G}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {p q u : ℕ}
    (hqp : q < p)
    (hrel : H.relIndex L = q)
    (h1319 :
      Section13.theorem_13_19_alternativeData H βL βS φ ηNat p q u
        (H.relIndex L)) :
    Section13.oddScalarProduct (Section1.scalarProduct G βS φ) ∧
      ((Nat.card H - 1 : ℕ) : ℝ) / (H.relIndex L : ℝ) ≤
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
  rcases h1319 with hfirst | hsecond
  · exact hfirst
  · have hp_le_q : p ≤ q := by
      simpa [hrel] using hsecond.2
    exact False.elim ((not_le_of_gt hqp) hp_le_q)

public theorem section14_theorem_14_5_H_eq_U_of_pf13_19_first
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hUH : U ≤ H)
    (hrel : H.relIndex L = q)
    (hle :
      ((Nat.card H - 1 : ℕ) : ℝ) / (H.relIndex L : ℝ) ≤
        ((u - 1 : ℕ) : ℝ) / (q : ℝ)) :
    H = U := by
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  have hUcard_eq : Nat.card U = u := by
    rw [hUcard, hc_one, Nat.mul_one]
  have hq_pos : 0 < q := by
    exact (section14_context_primes_of_sourceData hctx).2.pos
  have hle_q :
      ((Nat.card H - 1 : ℕ) : ℝ) / (q : ℝ) ≤
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
    simpa [hrel] using hle
  have hle_sub :
      ((Nat.card H - 1 : ℕ) : ℝ) ≤ ((u - 1 : ℕ) : ℝ) := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq_pos
    exact (div_le_div_iff_of_pos_right hqR).mp hle_q
  have hle_sub_nat : Nat.card H - 1 ≤ u - 1 := by
    exact_mod_cast hle_sub
  have hH_pos : 0 < Nat.card H := Nat.card_pos
  have hu_pos : 0 < u := by
    rw [← hUcard_eq]
    exact Nat.card_pos
  have hH_le_u : Nat.card H ≤ u := by omega
  have hcard_ge : Nat.card H ≤ Nat.card U := by
    rw [hUcard_eq]
    exact hH_le_u
  exact (Subgroup.eq_of_le_of_card_ge hUH hcard_ge).symm

public theorem section14_theorem_14_5_pf13_19_alternative_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    ∃ ηNat : ℕ → ℕ → Section1.ClassFunction G,
    ∃ μNat : ℕ → ℕ → Section1.ClassFunction Smax,
      Section13.theorem_13_19_alternativeData H (τL βL)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μNat 0 1))
        (τL₁ φ) ηNat p q u (H.relIndex L) := by
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation, _hChoice, _hMin⟩
  rcases hNotation with
    ⟨ω, ηNat, μ, ν, μsum, νsum, δ, δ', σ, hNotationFor⟩
  rcases h143 with
    ⟨hLmax, _hNorm, hMF, hTypeI, hDade, hLfam, _h52b, hExt,
      hφmem, _hφirr, hφdeg, _hβS, _hβT, hβL, _hDadeNotation⟩
  have hhyp :
      Section13.theorem_13_19_hypothesis L H Smax P W1 Lfam RL τS τL τL₁
        φ (τL₁ φ) (μ 0 1) (τL βL)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (H.relIndex L) := by
    refine ⟨hLmax, hMF, hTypeI, rfl, hDade, hLfam, hExt, hφmem,
      hφdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τL hβL
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam RL
    τS τT τL τL₁ φ (τL βL)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1)) (τL₁ φ)
    ω ηNat μ ν μsum νsum δ δ' σ p q u v c d (H.relIndex L)
    hctx.1 hNotationFor hhyp
  exact ⟨ηNat, μ, h1319.2.2.2⟩

public theorem section14_theorem_14_5_current_typeII_not_normalizer_source_bridge
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_htypeII : Section8.typeIIDefinitionData Smax P) :
    ¬ Subgroup.normalizer (U : Set G) ≤ Smax := by
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII_of_qp, _hUcomm, _hUfrob, _hPelem,
      _hPcard, _hu, _hSfamCoh, _hTI, _hTauS, hnotNormUleS_of_qp⟩
  exact hnotNormUleS_of_qp hctx.2

public theorem section14_theorem_14_5_W1_semidirect_source_consequences_bridge
    {G : Type u} [Group G] [Finite G]
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
        Section8.typeIIDefinitionData Smax P →
          U ≤ H →
            Section2.IsInternalSemidirectProduct L H W1 →
              H = U ∧ ¬ Subgroup.normalizer (U : Set G) ≤ Smax := by
  intro hctx h143 htypeII hUH hsemiW1
  rcases section14_theorem_14_5_pf13_19_alternative_of_hypothesis_14_3
      hctx h143 with
    ⟨_ηNat, _μNat, h1319⟩
  have hrel : H.relIndex L = q :=
    section14_theorem_14_5_W1_semidirect_relIndex_eq_q hctx hsemiW1
  have hfirst :=
    section14_theorem_14_5_pf13_19_first_of_relIndex_eq_q hctx.2 hrel h1319
  have hHU : H = U :=
    section14_theorem_14_5_H_eq_U_of_pf13_19_first hctx hUH hrel hfirst.2
  have hnotNormUleS :
      ¬ Subgroup.normalizer (U : Set G) ≤ Smax :=
    section14_theorem_14_5_current_typeII_not_normalizer_source_bridge
      hctx htypeII
  exact ⟨hHU, hnotNormUleS⟩

public theorem section14_theorem_14_5_no_W1_semidirect_source_bridge
    {G : Type u} [Group G] [Finite G]
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
        Section8.typeIIDefinitionData Smax P →
          U ≤ H →
            Section2.IsInternalSemidirectProduct L H W1 →
              False := by
  intro hctx h143 htypeII hUH hsemiW1
  rcases section14_theorem_14_5_W1_semidirect_source_consequences_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
      hctx h143 htypeII hUH hsemiW1 with
    ⟨hHU, hnotNormUleS⟩
  rcases h143 with
    ⟨_hLmax, hNormUleL, _hLHMf, _hTypeI, _hDadeL, _hLfam, _hTauL,
      _hTauL₁, _hφfam, _hφirr, _hφdeg, _hβS, _hβT, _hβL,
      _hDadeNotation⟩
  rcases hctx.1 with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hSMF, _hW1cyc, _hW1ne, _hW1Hall, hScompW1, hUleDer,
      _hUnil, _hW1norm, _hUcomp, _hPnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hnormalizer⟩
  have hUleS : U ≤ Smax :=
    hUleDer.trans section12_ambientDerivedSubgroup_le
  have hW1leS : W1 ≤ Smax := hScompW1.2.1
  have hLleS : L ≤ Smax := by
    intro g hgL
    rcases hsemiW1.mul_surjective g hgL with ⟨h0, hh0, k0, hk0, hg⟩
    rw [hg]
    exact Smax.mul_mem (hUleS (by simpa [hHU] using hh0)) (hW1leS hk0)
  exact hnotNormUleS (hNormUleL.trans hLleS)

public theorem section14_theorem_14_5_source_bridge
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
        theorem_14_5_data L H W1 W2 Q := by
  intro hctx h143
  rcases section14_theorem_14_5_pf13_17_inputs
      (hctx := hctx) (h143 := h143) with
    ⟨htypeII, hfrobLH, hUH, hcompW1 | hcompY⟩
  · have hsemiW1 : Section2.IsInternalSemidirectProduct L H W1 :=
      section14_semidirectProduct_of_frobenius_complement hfrobLH hcompW1
    have hcontra : False :=
      section14_theorem_14_5_no_W1_semidirect_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
        hctx h143 htypeII hUH hsemiW1
    exact False.elim hcontra
  · rcases hcompY with
      ⟨y, hyQ, hcomp⟩
    exact section14_theorem_14_5_data_of_conjugate_complement hfrobLH
      ⟨y, hyQ, hcomp⟩


end CFSG.Section14
