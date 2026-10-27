module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_16
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2_Field
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.2)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.2) -/

public theorem section14_characteristicSubgroupIn_self
    {G : Type u} [Group G] (U : Subgroup G) :
    characteristicSubgroupIn U U := by
  constructor
  · exact le_rfl
  · have htop : U.subgroupOf U = ⊤ := by
      ext x
      simp
    rw [htop]
    infer_instance

public def section14_theorem_14_2_branchChoiceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W1 W2 P Q U V : Subgroup G) : Prop :=
  ∃ (L H : Subgroup G),
  ∃ (Lfam : Finset (Section1.ClassFunction L)),
  ∃ (RL : G → Subgroup G),
  ∃ (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G),
  ∃ (φ : Section1.ClassFunction L),
  ∃ (μ01 : Section1.ClassFunction Smax),
  ∃ (ν10 : Section1.ClassFunction Tmax),
  ∃ (βS : Section1.ClassFunction Smax),
  ∃ (βT : Section1.ClassFunction Tmax),
  ∃ (βL : Section1.ClassFunction L),
    hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL ∧
      (characteristicSubgroupIn U H ∨
        ∃ (M K : Subgroup G),
        ∃ (Mfam : Finset (Section1.ClassFunction M)),
        ∃ (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
        ∃ (ψ βM : Section1.ClassFunction M),
          hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM ∧
            ((∃ g : G, L.conjBy g = M) ∨
              ∃ h : ℕ, hypothesis_14_13_statement L M H h))

public def section14_theorem_14_2_sourceChoiceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W1 W2 P Q U V : Subgroup G) : Prop :=
  ∃ (L H : Subgroup G),
  ∃ (Lfam : Finset (Section1.ClassFunction L)),
  ∃ (RL : G → Subgroup G),
  ∃ (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G),
  ∃ (φ : Section1.ClassFunction L),
  ∃ (μ01 : Section1.ClassFunction Smax),
  ∃ (ν10 : Section1.ClassFunction Tmax),
  ∃ (βS : Section1.ClassFunction Smax),
  ∃ (βT : Section1.ClassFunction Tmax),
  ∃ (βL : Section1.ClassFunction L),
    hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL ∧
      (characteristicSubgroupIn U H ∨
        ∃ (M K : Subgroup G),
        ∃ (Mfam : Finset (Section1.ClassFunction M)),
        ∃ (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
        ∃ (ψ βM : Section1.ClassFunction M),
          hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)

public theorem section14_theorem_14_2_branchChoiceData_of_sourceChoiceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W1 W2 P Q U V : Subgroup G) :
    section14_theorem_14_2_sourceChoiceData Smax Tmax W1 W2 P Q U V →
      section14_theorem_14_2_branchChoiceData Smax Tmax W1 W2 P Q U V := by
  intro hchoice
  rcases hchoice with
    ⟨L, H, Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL, h143, hbranch⟩
  refine ⟨L, H, Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL, h143, ?_⟩
  rcases hbranch with hchar | hM
  · exact Or.inl hchar
  · rcases hM with ⟨M, K, Mfam, τM, τM₁, ψ, βM, h1410⟩
    refine Or.inr ?_
    refine ⟨M, K, Mfam, τM, τM₁, ψ, βM, h1410, ?_⟩
    by_cases hconj : ∃ g : G, L.conjBy g = M
    · exact Or.inl hconj
    · exact Or.inr ⟨Nat.card H, hconj, rfl⟩

public theorem section14_frobeniusJoin_kernel_ne_bot
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    K ≠ ⊥ := by
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  have hKsub_ne : Ksub ≠ ⊥ := hfrob.kernel_ne_bot
  intro hKbot
  have hKsub_bot : Ksub = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxK : (x : G) ∈ K := by
        simpa [Ksub, Subgroup.mem_subgroupOf] using hx
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hKbot] using hxK
      exact Subtype.ext (by simpa using hxbot)
    · intro hx
      have hxone : x = 1 := by simpa using hx
      rw [hxone]
      exact Subgroup.one_mem Ksub
  exact hKsub_ne hKsub_bot

public theorem section14_theorem_14_2_hypothesis_14_3_maximal_overgroup
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∃ L : Subgroup G, L ∈ section9MaximalSubgroups G ∧
      Subgroup.normalizer (U : Set G) ≤ L := by
  rcases hctx.1 with
    ⟨hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      _hMin⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, _hSMF,
      _hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hStypes, _hTtypes, _hmaxclass⟩
  rcases hSTypeP with
    ⟨_hSMF, _hW1cyc, _hW1ne, _hW1Hall, _hcompW1, hUleDer,
      _hUnil, _hW1norm, _hUcomp, _hPnoncyc, _hSecond, _hFit,
      _hFitLe, _hW2le, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII_of_qp, _hUcomm, hfrobUW1, _hPelem,
      _hPcard, _hu, _hSfamCoh, _hTI, _hTauS, _hnorm⟩
  have hUleS : U ≤ Smax :=
    hUleDer.trans section12_ambientDerivedSubgroup_le
  have hUne : U ≠ ⊥ :=
    section14_frobeniusJoin_kernel_ne_bot hfrobUW1
  have hnormProper : Subgroup.normalizer (U : Set G) ≠ ⊤ :=
    section10_normalizer_ne_top_of_ne_bot_le_maximal hSmax hUleS hUne
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (U : Set G)) hnormProper with
    ⟨L, hL⟩
  exact ⟨L, hL.1, hL.2⟩

public theorem section14_theorem_14_2_hypothesis_14_3_typeI_of_overgroup
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (hMF : section16MFSubgroup L H) :
    Section8.typeIDefinitionData L H := by
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, htypeII_of_qp, _hUcomm, _hUfrob, _hPelem,
      _hPcard, _hu, _hSfamCoh, _hTI, _hTauS⟩
  exact Section13.theorem_13_17_typeIDefinitionData
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
    p q u v c d hctx.1 (htypeII_of_qp hctx.2) hLmax hNormUleL hMF

public theorem section14_theorem_14_2_hypothesis_14_3_dade_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (_ : Section7.puncturedInducedFamily (H.subgroupOf L) Lfam) :
    ∃ (RL : G → Subgroup G),
    ∃ (τL : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G),
      Section12.dadeIsometryRelativeToTypeIASet L H RL τL ∧
        ∃ D tildeA tildeA0 tildeA1 : Set G,
          Section8.notation_8_14_source_data L
            (Section12.typeIASet L H) (Section12.typeIASet L H)
            (Section8.a1Set H) D tildeA tildeA0 tildeA1 RL := by
  classical
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      _hMin⟩
  rcases hChoice L H hLmax hMF (Or.inl hTypeI) with ⟨Ms, hMs⟩
  have hMsEq : Ms = H := Section8.msChoiceSource_eq_mf_of_typeI hMs hTypeI
  have hMsH : Section8.msChoiceSource L H H := by
    simpa [hMsEq] using hMs
  have h810 :
      Section8.notation_8_10_source_data L H H
        (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H) :=
    Section12.notation_8_10_source_data_of_typeI_msChoice L H hLmax hMF hTypeI hMsH
  have hA1X : Section8.a1Set H ⊆ Section12.typeIASet L H := by
    simpa [Section8.a1Set] using
      Section12.nonidentity_kernel_subset_typeIASet L H
        (Section12.section16MFSubgroup_le hMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      L H H (Section12.typeIASet L H) (Section12.typeIASet L H)
      (Section8.a1Set H) (Section12.typeIASet L H)
      (by infer_instance) h810 (Or.inl rfl) hA1X with
    ⟨R, tildeA, tildeA0, tildeA1, h814⟩
  have h815source :
      Section8.theorem_8_15_source_data L H H
        (Section12.typeIASet L H) (Section12.typeIASet L H)
        (Section8.a1Set H) (Section12.typeIASet L H)
        (Section8.section8DSet L (Section12.typeIASet L H))
        tildeA tildeA0 tildeA1 R :=
    ⟨h810, h814, Or.inr (Or.inl rfl)⟩
  have h815 :=
    Section8.theorem_8_15 L H H
      (Section12.typeIASet L H) (Section12.typeIASet L H)
      (Section8.a1Set H) (Section8.section8DSet L (Section12.typeIASet L H))
      tildeA tildeA0 tildeA1 (Section12.typeIASet L H) R Lfam
      (by infer_instance) h815source
  refine ⟨R, Section12.dadeTransformLinear R h815.2.1.subset_L, ?_, ?_⟩
  · exact Section12.dadeIsometryRelativeToTypeIASet_of_hypothesis2 L H R h815.2.1
  · exact ⟨Section8.section8DSet L (Section12.typeIASet L H),
      tildeA, tildeA0, tildeA1, h814⟩

public theorem section14_theorem_14_2_hypothesis_14_3_hypothesis12_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H) :
    ∃ (Lfam : Finset (Section1.ClassFunction L)),
    ∃ (RL : G → Subgroup G),
    ∃ (τL : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G),
      Section12.hypothesis_12_1_data L H Lfam RL τL ∧
        ∃ D tildeA tildeA0 tildeA1 : Set G,
          Section8.notation_8_14_source_data L
            (Section12.typeIASet L H) (Section12.typeIASet L H)
            (Section8.a1Set H) D tildeA tildeA0 tildeA1 RL := by
  rcases Section12.exists_puncturedInducedFamily (H.subgroupOf L) with
    ⟨Lfam, hPunct⟩
  rcases section14_theorem_14_2_hypothesis_14_3_dade_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (Lfam := Lfam) (p := p) (q := q) (u := u) (v := v)
      (c := c) (d := d) hctx hLmax hMF hTypeI hPunct with
    ⟨RL, τL, hDade, hDadeNotation⟩
  exact ⟨Lfam, RL, τL, ⟨hLmax, hMF, hTypeI, hPunct, hDade⟩,
    hDadeNotation⟩

public theorem section14_theorem_14_2_hypothesis_14_3_reference_character
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {L H : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (h12_1 : Section12.hypothesis_12_1_data L H Lfam RL τL) :
    ∃ φ : Section1.ClassFunction L,
      φ ∈ Lfam ∧
      Section1.IsIrreducibleCharacterOnGroup φ ∧
      Section1.degree φ = (H.relIndex L : ℂ) := by
  classical
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hMF hTypeI
  rcases hMF.1 with ⟨hHL, _hnormal, hnil, _hhall⟩
  haveI : Group.IsNilpotent H := hnil
  haveI : IsSolvable H := IsNilpotent.to_isSolvable
  let e : H.subgroupOf L ≃* H := Subgroup.subgroupOfEquivOfLe hHL
  have hKsolv : IsSolvable (H.subgroupOf L) := by
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have hAbot : (⊥ : Subgroup L).Normal := inferInstance
  rcases hTypeI with ⟨U, U1, U0, hF, _hcases⟩
  rcases hF with ⟨_hsolv, _hodd, _hMF, hHbot, _hHltL, _hUne,
    _hcomp, _hU1le, _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
  have hHne : H ≠ ⊥ := hHbot.ne'
  have hsub_ne : H.subgroupOf L ≠ ⊥ := by
    intro hsubbot
    apply hHne
    exact (Subgroup.subgroupOf_eq_bot.mp hsubbot).eq_bot_of_le hHL
  have hAlt : (⊥ : Subgroup L) < H.subgroupOf L :=
    bot_lt_iff_ne_bot.mpr hsub_ne
  have hSbot :
      Section6.inducedKernelFamily (H.subgroupOf L) (⊥ : Subgroup L) Lfam :=
    Section12.theorem_12_6_inducedKernelFamily_bot_of_hypothesis12
      L H Lfam RL τL h12_1
  rcases Section6.inducedKernelFamily_exists_degree_relIndex_of_lt
      hKsolv hAbot hAlt hSbot with ⟨φ, hφmem, hφdegLocal⟩
  have hirrS := (Section12.theorem_12_6 L H Lfam RL τL h12_1 hfrob).1
  have hrel :
      (H.subgroupOf L).relIndex (⊤ : Subgroup L) = H.relIndex L := by
    simpa using (Subgroup.relIndex_subgroupOf (H := H) (K := L) (L := L) le_rfl)
  refine ⟨φ, hφmem, hirrS φ hφmem, ?_⟩
  simpa [hrel] using hφdegLocal

public theorem section14_theorem_14_2_hypothesis_14_3_character_package_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H) :
    ∃ (Lfam : Finset (Section1.ClassFunction L)),
    ∃ (RL : G → Subgroup G),
    ∃ (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G),
    ∃ (φ : Section1.ClassFunction L),
    ∃ (μ01 : Section1.ClassFunction Smax),
    ∃ (ν10 : Section1.ClassFunction Tmax),
    ∃ (βS : Section1.ClassFunction Smax),
    ∃ (βT : Section1.ClassFunction Tmax),
    ∃ (βL : Section1.ClassFunction L),
      Section12.dadeIsometryRelativeToTypeIASet L H RL τL ∧
      Section7.puncturedInducedFamily (H.subgroupOf L) Lfam ∧
      Section5.hypothesis_5_2_b_statement Lfam τL ∧
      Section7.isCoherentExtension Lfam τL τL₁ ∧
      φ ∈ Lfam ∧
      Section1.IsIrreducibleCharacterOnGroup φ ∧
      Section1.degree φ = (H.relIndex L : ℂ) ∧
      βS = Section7.principalInducedCharacter Smax (P ⊔ W1) - μ01 ∧
      βT = Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν10 ∧
      βL = Section7.theorem_7_8_betaInput L H φ ∧
      ∃ D tildeA tildeA0 tildeA1 : Set G,
        Section8.notation_8_14_source_data L
          (Section12.typeIASet L H) (Section12.typeIASet L H)
          (Section8.a1Set H) D tildeA tildeA0 tildeA1 RL := by
  classical
  have _hctx := hctx
  have _hNormUleL := hNormUleL
  rcases section14_theorem_14_2_hypothesis_14_3_hypothesis12_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d)
      hctx hLmax hMF hTypeI with
    ⟨Lfam, RL, τL, h12_1, hDadeNotation⟩
  have hDade : Section12.dadeIsometryRelativeToTypeIASet L H RL τL :=
    h12_1.2.2.2.2
  have hPunct : Section7.puncturedInducedFamily (H.subgroupOf L) Lfam :=
    h12_1.2.2.2.1
  rcases Section12.theorem_12_2_a L H Lfam RL τL h12_1 with ⟨SX, hSX⟩
  have h52b : Section5.hypothesis_5_2_b_statement Lfam τL :=
    Section12.hypothesis_5_2_b_of_hypothesis12_constituentFamilyData
      L H Lfam SX RL τL h12_1 hSX
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hMF hTypeI
  have hcoh : Section6.coherentFamily Lfam τL :=
    (Section12.theorem_12_6 L H Lfam RL τL h12_1 hfrob).2
  rcases hcoh with ⟨_hsrc, _hnonempty, τL₁, hIso, hVirt, hAgree⟩
  have hExt : Section7.isCoherentExtension Lfam τL τL₁ :=
    ⟨hIso, hVirt, hAgree⟩
  rcases section14_theorem_14_2_hypothesis_14_3_reference_character
      hLmax hMF hTypeI h12_1 with
    ⟨φ, hφmem, hφirr, hφdeg⟩
  let μ01 : Section1.ClassFunction Smax := 0
  let ν10 : Section1.ClassFunction Tmax := 0
  let βS : Section1.ClassFunction Smax :=
    Section7.principalInducedCharacter Smax (P ⊔ W1) - μ01
  let βT : Section1.ClassFunction Tmax :=
    Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν10
  let βL : Section1.ClassFunction L := Section7.theorem_7_8_betaInput L H φ
  exact ⟨Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL,
    hDade, hPunct, h52b, hExt, hφmem, hφirr, hφdeg, rfl, rfl, rfl,
    hDadeNotation⟩

public theorem section14_theorem_14_2_hypothesis_14_3_source_choice_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      ∃ (L H : Subgroup G),
      ∃ (Lfam : Finset (Section1.ClassFunction L)),
      ∃ (RL : G → Subgroup G),
      ∃ (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G),
      ∃ (φ : Section1.ClassFunction L),
      ∃ (μ01 : Section1.ClassFunction Smax),
      ∃ (ν10 : Section1.ClassFunction Tmax),
      ∃ (βS : Section1.ClassFunction Smax),
      ∃ (βT : Section1.ClassFunction Tmax),
      ∃ (βL : Section1.ClassFunction L),
        hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
          Lfam RL τL τL₁ φ μ01 ν10 βS βT βL := by
  intro hctx
  rcases section14_theorem_14_2_hypothesis_14_3_maximal_overgroup
      (G := G) (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1)
      (W2 := W2) (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) hctx with
    ⟨L, hLmax, hNormUleL⟩
  rcases section16_exists_mfSubgroup (G := G) L with ⟨H, hMF⟩
  have hTypeI : Section8.typeIDefinitionData L H :=
    section14_theorem_14_2_hypothesis_14_3_typeI_of_overgroup
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam)
      (τS := τS) (τT := τT) (p := p) (q := q) (u := u) (v := v)
      (c := c) (d := d) hctx hLmax hNormUleL hMF
  rcases section14_theorem_14_2_hypothesis_14_3_character_package_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam)
      (τS := τS) (τT := τT) (p := p) (q := q) (u := u) (v := v)
      (c := c) (d := d) hctx hLmax hNormUleL hMF hTypeI with
    ⟨Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL,
      hDade, hPunct, h52b, hExt, hφmem, hφirr, hφdeg, hβS, hβT, hβL,
      hDadeNotation⟩
  exact ⟨L, H, Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL,
    hLmax, hNormUleL, hMF, hTypeI, hDade, hPunct, h52b, hExt,
    hφmem, hφirr, hφdeg, hβS, hβT, hβL, hDadeNotation⟩

public theorem section14_theorem_14_2_hypothesis_14_10_maximal_overgroup
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∃ M : Subgroup G, M ∈ section9MaximalSubgroups G ∧
      Subgroup.normalizer (V : Set G) ≤ M := by
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      _hMin⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, hTmax, _hSMF,
      _hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hStypes, _hTtypes, _hmaxclass⟩
  rcases hTTypeP with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hcompW2, hVleDer,
      _hVnil, _hW2norm, _hVcomp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  rcases Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1) with
    ⟨_hTmaxMF, _htypeT, _htypeII_of_pq, _hVcomm, hfrobVW2, _hQelem,
      _hQcard, _hv, _hTfamCoh, _hTI, _hTauT, _hnorm⟩
  have hVleT : V ≤ Tmax :=
    hVleDer.trans section12_ambientDerivedSubgroup_le
  have hVne : V ≠ ⊥ :=
    section14_frobeniusJoin_kernel_ne_bot hfrobVW2
  have hnormProper : Subgroup.normalizer (V : Set G) ≠ ⊤ :=
    section10_normalizer_ne_top_of_ne_bot_le_maximal hTmax hVleT hVne
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (V : Set G)) hnormProper with
    ⟨M, hM⟩
  exact ⟨M, hM.1, hM.2⟩

public theorem section14_theorem_14_2_hypothesis_14_10_typeI_of_overgroup
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G}
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
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hNormVleM : Subgroup.normalizer (V : Set G) ≤ M)
    (hMF : section16MFSubgroup M K) :
    Section8.typeIDefinitionData M K := by
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      _hMin⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, hTmax, _hSMF,
      hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hStypes, _hTtypes, _hmaxclass⟩
  have hTypeT16 : section16TypeII Tmax Q :=
    section14_theorem_14_9_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hTypeT : Section8.typeIIDefinitionData Tmax Q :=
    Section8.theorem_8_8_typeII_to_source_public (G := G) hTmax hTMF hTypeT16
  exact Section13.theorem_13_17_typeIDefinitionData
    Tmax Smax W W2 W1 Q P V U D C M K Tfam Sfam τT τS
    q p v u d c (section14_hypothesis_13_1_sourceData_swap hctx.1)
    hTypeT hMmax hNormVleM hMF

public theorem section14_inducedKernelFamily_bot_of_puncturedInducedFamily
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hS : Section7.puncturedInducedFamily K S) :
    Section6.inducedKernelFamily K (⊥ : Subgroup L) S := by
  refine ⟨bot_le, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
    refine ⟨θ, hθirr, ?_, hθne, hχeq⟩
    intro a
    have ha : (a : K) = 1 := by
      ext
      simpa using a.property
    simp [Section1.degree, ha]
  · intro hχ
    rcases hχ with ⟨θ, hθirr, _hθker, hθne, hχeq⟩
    exact (hS χ).mpr ⟨θ, hθirr, hθne, hχeq⟩

public theorem section14_theorem_14_2_hypothesis_14_10_reference_character
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K)
    (hPunct : Section7.puncturedInducedFamily (K.subgroupOf M) Mfam) :
    ∃ ψ : Section1.ClassFunction M,
      ψ ∈ Mfam ∧
        Section1.IsIrreducibleCharacterOnGroup ψ ∧
          Section1.degree ψ = (K.relIndex M : ℂ) := by
  classical
  have hTypeI' := hTypeI
  rcases hMF.1 with ⟨hKM, _hKnormal0, hKnil, _hHall⟩
  haveI : Group.IsNilpotent K := hKnil
  haveI : IsSolvable K := IsNilpotent.to_isSolvable
  let e : K.subgroupOf M ≃* K := Subgroup.subgroupOfEquivOfLe hKM
  have hKsolv : IsSolvable (K.subgroupOf M) := by
    exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have hAbot : (⊥ : Subgroup M).Normal := inferInstance
  rcases hTypeI with ⟨_U, _U1, _U0, hF, _hcases⟩
  rcases hF with
    ⟨_hsolv, _hodd, _hMF, hKbot, _hKltM, _hUne, _hcomp, _hU1le,
      _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
  have hKne : K ≠ ⊥ := hKbot.ne'
  have hsub_ne : K.subgroupOf M ≠ ⊥ := by
    intro hsubbot
    apply hKne
    exact (Subgroup.subgroupOf_eq_bot.mp hsubbot).eq_bot_of_le hKM
  have hAlt : (⊥ : Subgroup M) < K.subgroupOf M :=
    bot_lt_iff_ne_bot.mpr hsub_ne
  have hSbot :
      Section6.inducedKernelFamily (K.subgroupOf M) (⊥ : Subgroup M) Mfam :=
    section14_inducedKernelFamily_bot_of_puncturedInducedFamily hPunct
  rcases Section6.inducedKernelFamily_exists_degree_relIndex_of_lt
      hKsolv hAbot hAlt hSbot with
    ⟨ψ, hψmem, hψdegLocal⟩
  have hfrob : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hMF hTypeI'
  rcases hfrob with
    ⟨_hKMfrob, hKnormal, _R, hcomp, _hKneFrob, _hRne, hcent⟩
  haveI : (K.subgroupOf M).Normal := hKnormal
  have hψirr : Section1.IsIrreducibleCharacterOnGroup ψ :=
    Section6.theorem_6_8_inducedKernelFamily_irreducible_of_frobenius_complement
      hSbot hcomp hcent ψ hψmem
  have hrel : (K.subgroupOf M).relIndex (⊤ : Subgroup M) = K.relIndex M := by
    simpa using (Subgroup.relIndex_subgroupOf (H := K) (K := M) (L := M) le_rfl)
  refine ⟨ψ, hψmem, hψirr, ?_⟩
  simpa [hrel] using hψdegLocal

public theorem section14_theorem_14_2_hypothesis_14_10_dade_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U C D : Subgroup G}
    {M K V : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hNormVleM : Subgroup.normalizer (V : Set G) ≤ M)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K)
    (_ : Section7.puncturedInducedFamily (K.subgroupOf M) Mfam) :
    ∃ (R : G → Subgroup G),
    ∃ (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
      Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
        (∀ tildeAM : Set G,
          Section10.section10TildeAData M K tildeAM →
            Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM) ∧
        ∃ D tildeA tildeA0 tildeA1 : Set G,
          Section8.notation_8_14_source_data M
            (Section12.typeIASet M K) (Section12.typeIASet M K)
            (Section8.a1Set K) D tildeA tildeA0 tildeA1 R := by
  classical
  have _hNormVleM := hNormVleM
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      _hMin⟩
  rcases hChoice M K hMmax hMF (Or.inl hTypeI) with ⟨Ms, hMs⟩
  have hMsEq : Ms = K := Section8.msChoiceSource_eq_mf_of_typeI hMs hTypeI
  have hMsK : Section8.msChoiceSource M K K := by
    simpa [hMsEq] using hMs
  have h810 :
      Section8.notation_8_10_source_data M K K
        (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K) :=
    Section12.notation_8_10_source_data_of_typeI_msChoice M K hMmax hMF hTypeI hMsK
  have hA1X : Section8.a1Set K ⊆ Section12.typeIASet M K := by
    simpa [Section8.a1Set] using
      Section12.nonidentity_kernel_subset_typeIASet M K
        (Section12.section16MFSubgroup_le hMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      M K K (Section12.typeIASet M K) (Section12.typeIASet M K)
      (Section8.a1Set K) (Section12.typeIASet M K)
      (by infer_instance) h810 (Or.inl rfl) hA1X with
    ⟨R, tildeA, tildeA0, tildeA1, h814⟩
  have h815source :
      Section8.theorem_8_15_source_data M K K
        (Section12.typeIASet M K) (Section12.typeIASet M K)
        (Section8.a1Set K) (Section12.typeIASet M K)
        (Section8.section8DSet M (Section12.typeIASet M K))
        tildeA tildeA0 tildeA1 R :=
    ⟨h810, h814, Or.inr (Or.inl rfl)⟩
  have h815 :=
    Section8.theorem_8_15 M K K
      (Section12.typeIASet M K) (Section12.typeIASet M K)
      (Section8.a1Set K) (Section8.section8DSet M (Section12.typeIASet M K))
      tildeA tildeA0 tildeA1 (Section12.typeIASet M K) R Mfam
      (by infer_instance) h815source
  refine ⟨R, Section12.dadeTransformLinear R h815.2.1.subset_L, ?_, ?_, ?_⟩
  · exact Section12.dadeIsometryRelativeToTypeIASet_of_hypothesis2 M K R h815.2.1
  · intro tildeAM htilde
    rcases htilde with ⟨Ms0, A0, A00, A10, D0, tildeA00, tildeA10, R0, h8100, h8140⟩
    have hsupp0 :
        Section2.dadeSupport (Section12.typeIASet M K) R0 = tildeAM :=
      section14_typeI_dadeSupport_eq_tildeA_of_notation_8_14
        M K Ms0 A0 A00 A10 D0 tildeAM tildeA00 tildeA10 R0 hTypeI h8100 h8140
    have hsupp :
        Section2.dadeSupport (Section12.typeIASet M K) R = tildeA :=
      section14_typeI_dadeSupport_eq_tildeA_of_notation_8_14
        M K K (Section12.typeIASet M K) (Section12.typeIASet M K)
        (Section8.a1Set K) (Section8.section8DSet M (Section12.typeIASet M K))
        tildeA tildeA0 tildeA1 R hTypeI h810 h814
    have hsuppEq :
        Section2.dadeSupport (Section12.typeIASet M K) R =
          Section2.dadeSupport (Section12.typeIASet M K) R0 :=
      section14_typeI_dadeSupport_eq_of_notation_8_14
        M K K Ms0
        (Section12.typeIASet M K) (Section12.typeIASet M K)
        (Section8.a1Set K) (Section8.section8DSet M (Section12.typeIASet M K))
        tildeA tildeA0 tildeA1
        A0 A00 A10 D0 tildeAM tildeA00 tildeA10
        R R0 hTypeI h810 h814 h8100 h8140
    exact hsuppEq.trans hsupp0
  · exact ⟨Section8.section8DSet M (Section12.typeIASet M K),
      tildeA, tildeA0, tildeA1, h814⟩

public theorem section14_theorem_14_2_hypothesis_14_10_hypothesis12_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U C D : Subgroup G}
    {M K V : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hNormVleM : Subgroup.normalizer (V : Set G) ≤ M)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K) :
    ∃ (Mfam : Finset (Section1.ClassFunction M)),
    ∃ (R : G → Subgroup G),
    ∃ (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
      Section12.hypothesis_12_1_data M K Mfam R τM ∧
        (∀ tildeAM : Set G,
          Section10.section10TildeAData M K tildeAM →
            Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM) ∧
        ∃ D tildeA tildeA0 tildeA1 : Set G,
          Section8.notation_8_14_source_data M
            (Section12.typeIASet M K) (Section12.typeIASet M K)
            (Section8.a1Set K) D tildeA tildeA0 tildeA1 R := by
  have _hNormVleM := hNormVleM
  rcases Section12.exists_puncturedInducedFamily (K.subgroupOf M) with
    ⟨Mfam, hPunct⟩
  rcases section14_theorem_14_2_hypothesis_14_10_dade_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (Mfam := Mfam) (p := p) (q := q) (u := u) (v := v)
      (c := c) (d := d) hctx hMmax hNormVleM hMF hTypeI hPunct with
    ⟨R, τM, hDade, hDadeSupport, hDadeNotation⟩
  exact ⟨Mfam, R, τM, ⟨hMmax, hMF, hTypeI, hPunct, hDade⟩,
    hDadeSupport, hDadeNotation⟩

public theorem section14_theorem_14_2_hypothesis_14_10_coherent_family_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U C D : Subgroup G}
    {M K V : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (_ : Odd (Nat.card M))
    (hNormVleM : Subgroup.normalizer (V : Set G) ≤ M)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K) :
    ∃ (Mfam : Finset (Section1.ClassFunction M)),
    ∃ (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
      (∃ R : G → Subgroup G,
        Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
          (∀ tildeAM : Set G,
            Section10.section10TildeAData M K tildeAM →
              Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM) ∧
          ∃ D tildeA tildeA0 tildeA1 : Set G,
            Section8.notation_8_14_source_data M
              (Section12.typeIASet M K) (Section12.typeIASet M K)
              (Section8.a1Set K) D tildeA tildeA0 tildeA1 R) ∧
        Section7.puncturedInducedFamily (K.subgroupOf M) Mfam ∧
        Section5.hypothesis_5_2_b_statement Mfam τM ∧
        Section6.coherentFamily Mfam τM := by
  rcases section14_theorem_14_2_hypothesis_14_10_hypothesis12_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d)
      hctx hMmax hNormVleM hMF hTypeI with
    ⟨Mfam, R, τM, h12_1, hDadeSupport, hDadeNotation⟩
  have hDade : Section12.dadeIsometryRelativeToTypeIASet M K R τM :=
    h12_1.2.2.2.2
  have hPunct : Section7.puncturedInducedFamily (K.subgroupOf M) Mfam :=
    h12_1.2.2.2.1
  rcases Section12.theorem_12_2_a M K Mfam R τM h12_1 with ⟨SX, hSX⟩
  have h52b : Section5.hypothesis_5_2_b_statement Mfam τM :=
    Section12.hypothesis_5_2_b_of_hypothesis12_constituentFamilyData
      M K Mfam SX R τM h12_1 hSX
  have hfrob : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hMF hTypeI
  have hcoh : Section6.coherentFamily Mfam τM :=
    (Section12.theorem_12_6 M K Mfam R τM h12_1 hfrob).2
  exact ⟨Mfam, τM, ⟨R, hDade, hDadeSupport, hDadeNotation⟩,
    hPunct, h52b, hcoh⟩

public theorem section14_theorem_14_2_hypothesis_14_10_family_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U C D : Subgroup G}
    {M K V : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hModd : Odd (Nat.card M))
    (hNormVleM : Subgroup.normalizer (V : Set G) ≤ M)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K) :
    ∃ (Mfam : Finset (Section1.ClassFunction M)),
    ∃ (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
      (∃ R : G → Subgroup G,
        Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
          (∀ tildeAM : Set G,
            Section10.section10TildeAData M K tildeAM →
              Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM) ∧
          ∃ D tildeA tildeA0 tildeA1 : Set G,
            Section8.notation_8_14_source_data M
              (Section12.typeIASet M K) (Section12.typeIASet M K)
              (Section8.a1Set K) D tildeA tildeA0 tildeA1 R) ∧
        Section7.puncturedInducedFamily (K.subgroupOf M) Mfam ∧
        Section5.hypothesis_5_2_b_statement Mfam τM ∧
        Section7.isCoherentExtension Mfam τM τM₁ := by
  rcases section14_theorem_14_2_hypothesis_14_10_coherent_family_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d)
      hctx hMmax hModd hNormVleM hMF hTypeI with
    ⟨Mfam, τM, hDadeM, hPunctM, h52M, hcohM⟩
  rcases hcohM with ⟨_hsrc, _hnonempty, τM₁, hIso, hVirt, hAgree⟩
  exact ⟨Mfam, τM, τM₁, hDadeM, hPunctM, h52M,
    ⟨hIso, hVirt, hAgree⟩⟩

public theorem section14_theorem_14_2_hypothesis_14_10_character_package_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U C D : Subgroup G}
    {M K V : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hModd : Odd (Nat.card M))
    (hNormVleM : Subgroup.normalizer (V : Set G) ≤ M)
    (hMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K) :
    ∃ (Mfam : Finset (Section1.ClassFunction M)),
    ∃ (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
    ∃ (ψ : Section1.ClassFunction M),
      (∃ R : G → Subgroup G,
        Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
          (∀ tildeAM : Set G,
            Section10.section10TildeAData M K tildeAM →
              Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM) ∧
          ∃ D tildeA tildeA0 tildeA1 : Set G,
            Section8.notation_8_14_source_data M
              (Section12.typeIASet M K) (Section12.typeIASet M K)
              (Section8.a1Set K) D tildeA tildeA0 tildeA1 R) ∧
      Section7.puncturedInducedFamily (K.subgroupOf M) Mfam ∧
      Section5.hypothesis_5_2_b_statement Mfam τM ∧
      Section7.isCoherentExtension Mfam τM τM₁ ∧
      ψ ∈ Mfam ∧
      Section1.IsIrreducibleCharacterOnGroup ψ ∧
      Section1.degree ψ = (K.relIndex M : ℂ) := by
  rcases section14_theorem_14_2_hypothesis_14_10_family_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d)
      hctx hMmax hModd hNormVleM hMF hTypeI with
    ⟨Mfam, τM, τM₁, hDadeM, hPunctM, h52M, hExtM⟩
  rcases section14_theorem_14_2_hypothesis_14_10_reference_character
      hMmax hMF hTypeI hPunctM with
    ⟨ψ, hψmem, hψirr, hψdeg⟩
  exact ⟨Mfam, τM, τM₁, ψ, hDadeM, hPunctM, h52M, hExtM,
    hψmem, hψirr, hψdeg⟩

public theorem section14_theorem_14_2_hypothesis_14_10_source_choice_bridge
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
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        ¬ characteristicSubgroupIn U H →
          ∃ (M K : Subgroup G),
          ∃ (Mfam : Finset (Section1.ClassFunction M)),
          ∃ (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
          ∃ (ψ βM : Section1.ClassFunction M),
            hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM := by
  intro hctx h143 hnotChar
  have _hnotChar := hnotChar
  rcases section14_theorem_14_2_hypothesis_14_10_maximal_overgroup
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) hctx with
    ⟨M, hMmax, hNormVleM⟩
  rcases section16_exists_mfSubgroup (G := G) M with ⟨K, hMF⟩
  have hTypeI : Section8.typeIDefinitionData M K :=
    section14_theorem_14_2_hypothesis_14_10_typeI_of_overgroup
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (M := M) (K := K) (Sfam := Sfam)
      (Tfam := Tfam) (τS := τS) (τT := τT) (Lfam := Lfam)
      (RL := RL) (τL := τL) (τL₁ := τL₁) (φ := φ) (μ01 := μ01)
      (ν10 := ν10) (βS := βS) (βT := βT) (βL := βL)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d)
      hctx h143 hMmax hNormVleM hMF
  have hModd : Odd (Nat.card M) :=
    Section12.odd_card_of_typeIDefinitionData M K hTypeI
  rcases section14_theorem_14_2_hypothesis_14_10_character_package_source_bridge
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (C := C) (D := D)
      (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d)
      hctx hMmax hModd hNormVleM hMF hTypeI with
    ⟨Mfam, τM, τM₁, ψ, hDadeM, hPunctM, h52M, hExtM, hψmem,
      hψirr, hψdeg⟩
  let βM : Section1.ClassFunction M := Section7.theorem_7_8_betaInput M K ψ
  exact ⟨M, K, Mfam, τM, τM₁, ψ, βM, hMmax, hModd, hNormVleM, hMF,
    hTypeI, hDadeM, hPunctM, h52M, hExtM, hψmem, hψirr, hψdeg, rfl⟩

public theorem section14_theorem_14_2_source_choice_data_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      section14_theorem_14_2_sourceChoiceData Smax Tmax W1 W2 P Q U V := by
  intro hctx
  rcases section14_theorem_14_2_hypothesis_14_3_source_choice_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hctx with
    ⟨L, H, Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL, h143⟩
  refine ⟨L, H, Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL, h143, ?_⟩
  by_cases hchar : characteristicSubgroupIn U H
  · exact Or.inl hchar
  · refine Or.inr ?_
    rcases section14_theorem_14_2_hypothesis_14_10_source_choice_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        p q u v c d hctx h143 hchar with
      ⟨M, K, Mfam, τM, τM₁, ψ, βM, h1410⟩
    exact ⟨M, K, Mfam, τM, τM₁, ψ, βM, h1410⟩

public theorem section14_theorem_14_2_branch_choice_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      section14_theorem_14_2_branchChoiceData Smax Tmax W1 W2 P Q U V := by
  intro hctx
  exact section14_theorem_14_2_branchChoiceData_of_sourceChoiceData
    Smax Tmax W1 W2 P Q U V
    (section14_theorem_14_2_source_choice_data_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hctx)

public theorem section14_theorem_14_2_source_bridge_from_branch_choice
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      section14_theorem_14_2_branchChoiceData Smax Tmax W1 W2 P Q U V →
        theorem_14_2_a_data P U W2 p q ∧
          theorem_14_2_b_data Q W1 W2 U q := by
  intro hctx hchoice
  rcases hchoice with
    ⟨L, H, Lfam, RL, τL, τL₁, φ, μ01, ν10, βS, βT, βL, h143, hbranch⟩
  rcases hbranch with hchar | hMbranch
  · exact section14_theorem_14_7_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar
  · rcases hMbranch with
      ⟨M, K, Mfam, τM, τM₁, ψ, βM, h1410, hconj_or_not⟩
    rcases hconj_or_not with hLMconj | hnot
    · exact section14_theorem_14_12_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
        p q u v c d hctx h143 h1410 hLMconj
    · rcases hnot with ⟨h, h1413⟩
      have hHU : H = U :=
        section14_theorem_14_16_source_bridge
          Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
          Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
          p q u v c d h hctx h143 h1410 h1413
      have hchar : characteristicSubgroupIn U H := by
        rw [hHU]
        exact section14_characteristicSubgroupIn_self U
      exact section14_theorem_14_7_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar

/-! ## Proof placeholders -/

/-- Peterfalvi Theorem `(14.2)`, assembled in the minimal-counterexample
context from the branch route `(14.7)/(14.12)/(14.16)`. -/
public theorem theorem_14_2_from_minCE
    {G : Type u}
    [Group G]
    [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      theorem_14_2_a_data P U W2 p q ∧
        theorem_14_2_b_data Q W1 W2 U q := by
  intro hctx
  exact section14_theorem_14_2_source_bridge_from_branch_choice
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hctx
    (section14_theorem_14_2_branch_choice_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hctx)


end CFSG.Section14
