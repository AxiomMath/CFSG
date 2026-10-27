module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_3
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.3) -/


private theorem theorem_13_3_isMulCommutative_sup_of_le_centralizer
    {G : Type u} [Group G]
    {A Y : Subgroup G}
    (hAcomm : IsMulCommutative A)
    (hYcomm : IsMulCommutative Y)
    (hYleCentA : Y ≤ Subgroup.centralizer (A : Set G)) :
    IsMulCommutative (A ⊔ Y : Subgroup G) := by
  rw [Subgroup.sup_eq_closure]
  have hcomm : IsMulCommutative
      (Subgroup.closure ((A : Set G) ∪ (Y : Set G))) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with hxA | hxY
      · rcases hy with hyA | hyY
        · exact setLike_mul_comm
            (s := A) hxA hyA
        · exact Subgroup.mem_centralizer_iff.mp (hYleCentA hyY) x hxA
      · rcases hy with hyA | hyY
        · exact
            (Subgroup.mem_centralizer_iff.mp (hYleCentA hxY) y hyA).symm
        · exact setLike_mul_comm
            (s := Y) hxY hyY)
  exact ⟨⟨hcomm.is_comm.comm⟩⟩

private theorem hypothesis_13_1_muSum_characterData_of_sourceData
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < p →
            Section1.IsCharacter (μsum j) ∧
              Section1.degree (μsum j) = (u * q : ℂ) ∧
              inducedFromLinearCharacterForSection13 Smax (P ⊔ C) (μsum j) ∧
              μsum j ∈ Sfam := by
  classical
  have hsourceOrig := hsource
  have hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q :=
    section13_theorem_13_2_caseBData_bg_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hSTypeP : Section8.typePData Smax P U W1 W2 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hsourceSwap := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have hTTypeP : Section8.typePData Tmax Q V W2 W1 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceSwap
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig with
    ⟨_hMF, _htype, _htypeLarge, hUcomm, _hfrob, hPelem, _hPcard,
      _huBound, _hcoherent, _hbook, _hAZero, _hnorm⟩
  rcases hsource with
    ⟨_hcaseSource, hSTypePSource, _hTTypePSource, hp, hq, hC, _hD, _hc,
      _hd, _hUcard, _hVcard, hSnonker, hTnonker, hDadeS, hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hmin, hFourSixS, hFourSixT⟩
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  have hnotationNat :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ := by
    simpa [hp, hq] using hnotation
  have hjNat : j < Nat.card W2 := by simpa [hp] using hj
  have hFitEq : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hSTypePSource
  have hSubEq :
      (section8FittingSubgroup Smax).subgroupOf Smax =
        (P ⊔ C).subgroupOf Smax :=
    congrArg (fun H : Subgroup G ↦ H.subgroupOf Smax) hFitEq
  have hIndFit :=
    hypothesis_13_1_muSum_inducedFrom_fitting_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT
      hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotationNat j hj0 hjNat
  have htransport :
      ∀ H H' : Subgroup Smax, H = H' →
        (∃ θ : Section1.ClassFunction H,
          Section1.IsIrreducibleCharacterOnGroup θ ∧
            μsum j = Section1.inducedCF H θ) →
        ∃ θ : Section1.ClassFunction H',
          Section1.IsIrreducibleCharacterOnGroup θ ∧
            μsum j = Section1.inducedCF H' θ := by
    intro H H' hHH' hInd
    subst H'
    exact hInd
  rcases htransport _ _ hSubEq hIndFit with ⟨θ, hθirr, hμeq⟩
  have hPcomm : IsMulCommutative P := hPelem.toIsMulCommutative
  have hCcomm : IsMulCommutative C := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    have hx : ((x : C) : G) ∈ subgroupCentralizerIn U P := by
      rw [← hC]
      exact x.property
    have hy : ((y : C) : G) ∈ subgroupCentralizerIn U P := by
      rw [← hC]
      exact y.property
    apply Subtype.ext
    exact setLike_mul_comm (s := U) hx.1 hy.1
  have hCleCentP : C ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    have hx' : x ∈ subgroupCentralizerIn U P := by
      rw [← hC]
      exact hx
    exact hx'.2
  have hPCcomm : IsMulCommutative (P ⊔ C : Subgroup G) :=
    theorem_13_3_isMulCommutative_sup_of_le_centralizer
      hPcomm hCcomm hCleCentP
  letI : IsMulCommutative (P ⊔ C : Subgroup G) := hPCcomm
  letI : IsMulCommutative ((P ⊔ C).subgroupOf Smax) :=
    Subgroup.subgroupOf_isMulCommutative (H := P ⊔ C) (K := Smax)
  have hθdeg : Section1.degree θ = (1 : ℂ) :=
    Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθirr
  have hPCleS : P ⊔ C ≤ Smax := by
    rw [← hFitEq]
    exact section8FittingSubgroup_le Smax
  have hlinear :
      inducedFromLinearCharacterForSection13 Smax (P ⊔ C) (μsum j) :=
    ⟨hPCleS, θ, hθirr, hθdeg, hμeq⟩
  have hcharacter : Section1.IsCharacter (μsum j) := by
    rw [hμeq]
    exact Section1.isCharacter_inducedCF_of_isCharacter
      ((P ⊔ C).subgroupOf Smax) θ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hindex : ((P ⊔ C).subgroupOf Smax).index = q * u := by
    rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig with hcaseA | hcaseB
    · rcases hcaseA with ⟨hBarU, _a, hcaseAcore⟩
      exact Section9.HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9
        Smax P U W1 W2 C q u
        (Section9.case_9_7_a_hypothesis_9_2_sec9 hcaseAcore) hBarU
    · have hcaseB9 :
          Section9.case_9_7_b_data Smax P U W1 W2 ⊥ C p q u := by
        simpa [case_9_7_b_sourceDataForSection13] using hcaseB
      exact Section9.HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9
        Smax P U W1 W2 C q u
        (Section9.case_9_7_b_hypothesis_9_2_sec9 hcaseB9)
        (Section9.case_9_7_b_barU_cardinality_sec9 hcaseB9)
  have hlinear9 : Section9.inducedFromLinearCharacter Smax (P ⊔ C) (μsum j) :=
    ⟨θ, hθirr, hθdeg, hμeq⟩
  have hdegreeIndex :=
    Section9.degree_eq_index_of_inducedFromLinearCharacter_sec9
      Smax (P ⊔ C) (μsum j) hlinear9
  have hdegree : Section1.degree (μsum j) = (u * q : ℂ) := by
    rw [hindex] at hdegreeIndex
    calc
      Section1.degree (μsum j) = ((q * u : ℕ) : ℂ) := hdegreeIndex
      _ = (q : ℂ) * (u : ℂ) := by norm_num
      _ = (u : ℂ) * (q : ℂ) := mul_comm _ _
  have hmem : μsum j ∈ Sfam :=
    hypothesis_13_1_muSum_mem_sourceFamily
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT
      hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotationNat j hj0 hjNat
  exact ⟨hcharacter, hdegree, hlinear, hmem⟩

private theorem theorem_13_3_fittingSupportedFourSixData_of_typeP
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData
      Smax W1 W2 Wsec A A0 i0 j0 μsel δSign ωsec σsec τS) :
    ∃ σS : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup Smax),
        ∃ H_A : G → Subgroup G,
          Section4Scratch.hypothesis_4_6_supported_statement Smax
            (derivedSubgroup Smax)
            (W1.subgroupOf Smax)
            (W2.subgroupOf Smax)
            Wsec
            (P.subgroupOf Smax)
            A i0 j0 ωsec σS σsec μsel xChar
            (fun j ↦ (δSign j : ℂ)) τS H_A := by
  classical
  rcases hSTypeP with ⟨hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, hPleAmbient, _hCompMFU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2leP, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6,
      _hW2Second⟩
  rcases hNotation with
    ⟨MFsrc, Ms, _Abook, _A0book, _A1book, hSource,
      _hW, _hA0, h46, _hωNotation, _hIsoNotation, _hVirtNotation,
      _hPrinNotation, _hSigmaAgree, _h45Notation, _h48Notation,
      _hTauIsoNotation, hPackage⟩
  rcases hSource with
    ⟨_hApre, _hA0sub, hSourceNotation, _hTauSource⟩
  rcases hPackage with
    ⟨σS, xChar, H_A, _H_A0, hSupported, _hGalois⟩
  have hMFsrcEq : MFsrc = P :=
    section16MFSubgroup_unique hSourceNotation.2.1 hMF
  subst MFsrc
  have hPleMs : P ≤ Ms := by
    rcases hSourceNotation.2.2.1.to_literal with hEarly | hLate
    · rw [hEarly.2]
    · rw [hLate.2]
      exact hPleAmbient
  have hPleMsSub : P.subgroupOf Smax ≤ Ms.subgroupOf Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using hPleMs hxP
  have hPleDer : P.subgroupOf Smax ≤ derivedSubgroup Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxDerG : (x : G) ∈ ambientDerivedSubgroup Smax := hPleAmbient hxP
    have hxDerSub : x ∈ (ambientDerivedSubgroup Smax).subgroupOf Smax := by
      simpa [Subgroup.mem_subgroupOf] using hxDerG
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq
      (G := G) (E := Smax)] using hxDerSub
  have h46P :
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        Wsec
        (P.subgroupOf Smax)
        A := by
    rcases h46 with ⟨h42, _hMsNormal, _hW2leMs, _hMsleDer, hUnionMs, hAsub⟩
    refine ⟨h42, Section12.section16MFSubgroup_subgroupOf_normal hMF, ?_,
      hPleDer, ?_, hAsub⟩
    · intro x hx
      have hxW2 : (x : G) ∈ W2 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      simpa [Subgroup.mem_subgroupOf] using hW2leP hxW2
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨h, hxcentral⟩
      let k : {k : Ms.subgroupOf Smax // (k : Smax) ≠ 1} :=
        ⟨⟨(h.1 : Smax), hPleMsSub h.1.2⟩, by simpa using h.2⟩
      exact hUnionMs (Set.mem_iUnion.mpr ⟨k, by simpa [k] using hxcentral⟩)
  exact ⟨σS, xChar, H_A, h46P, hSupported.2⟩

private theorem theorem_13_3_exists_conjugate_muColumn_index_of_supportedData
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {K W1 W2 W H : Subgroup M}
    {A : Set M}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {μ : I → J → Section1.ClassFunction M}
    {xChar : J → Section1.ClassFunction K}
    {δSign : J → ℤ}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {H_A : G → Subgroup G}
    (hSupported : Section4Scratch.hypothesis_4_6_supported_statement M
      K W1 W2 W H A i0 j0 ω σM σ μ xChar
      (fun j ↦ (δSign j : ℂ)) τ H_A)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J,
      j' ≠ j0 ∧
        Section1.conjugateCharacter (Section10.muColumn μ j) =
          Section10.muColumn μ j' ∧
        Section10.muColumn μ j' ≠ Section10.muColumn μ j := by
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  have h47 : Section4Scratch.theorem_4_7_statement K H A :=
    Section4Scratch.theorem_4_7
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H) (A := A) h46
  have h49a : Section4Scratch.theorem_4_9_a_statement A j0 j μ :=
    Section4Scratch.theorem_4_9_a
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H) (A := A)
      (i0 := i0) (j0 := j0) (k := j) (ω := ω) (σ := σM)
      (piChar := μ) (xChar := xChar)
      (deltaSign := fun j ↦ (δSign j : ℂ))
      h46 h45a hω h43b h43c h47
  have hjMem : j ∈ Section4Scratch.equalDegreeColumnSet μ j0 j := ⟨hj, rfl⟩
  rcases (h49a hj).1 j hjMem with ⟨j', hj'Mem, hconj, hne⟩
  exact ⟨j', hj'Mem.1,
    by simpa [Section10.muColumn, Section4Scratch.piColumn] using hconj,
    by simpa [Section10.muColumn, Section4Scratch.piColumn] using hne⟩

private theorem theorem_13_3_inducedFromNonkernelFamily_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 : Subgroup G}
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup Smax) (P.subgroupOf Smax) Sfam := by
  rcases hTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hDerEq : ambientDerivedSubgroup Smax = P ⊔ U := hDerComp.2.2.1
  have hBase : Section5.inducedFromNonkernelFamily_statement
      ((P ⊔ U).subgroupOf Smax) (P.subgroupOf Smax) Sfam := by
    intro X hX
    exact (hSfam.2.2 X).mp hX
  simpa only [← section12_ambientDerivedSubgroup_subgroupOf_eq
    (G := G) (E := Smax), hDerEq] using hBase

private theorem theorem_13_3_irreducibleBranch_for_coherentExtension
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (hIso : Section5.isCFLinearIsometryOnSpan Sfam τ1)
    (hVirt : Section5.mapsIntegerSpanToVirtualCharacters Sfam τ1)
    (hAgree : Section5.agreesOnIntegerSpanOn
      Sfam Section5.puncturedSet τS τ1)
    (hIrr : ∃ X : Sfam,
      Section1.IsIrreducibleCharacterOnGroup
        (X : Section1.ClassFunction Smax)) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          theorem_13_3_signAlternativeData p q
            (fun j => τ1 (μsum j)) η := by
  classical
  have hsourceOrig := hsource
  have hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q :=
    section13_theorem_13_2_caseBData_bg_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hSTypeP : Section8.typePData Smax P U W1 W2 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hsourceSwap := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have hTTypeP : Section8.typePData Tmax Q V W2 W1 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceSwap
  rcases hsource with
    ⟨_hcaseSource, hSTypePDef, _hTTypePDef, hp, hq, _hC, _hD, _hc,
      _hd, _hUcard, _hVcard, hSnonker, hTnonker, hDadeS, hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, hmin, hFourSixS,
      hFourSixT⟩
  subst p
  subst q
  letI : IsMinCE G := hmin
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  rcases hIrr with ⟨X, hXirr⟩
  have hSne : Sfam.Nonempty := ⟨X, X.property⟩
  rcases section13_typeP_pf8_RFamily_of_typePFourSix
      hSTypePDef hFourSixS hSnonker hSne with
    ⟨_Ms, _Abook, _d52, _R, _hd52tau, _hSigmaAgree, h52a,
      _h52c, _h52d, _hExtra⟩
  have hInd : Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup Smax) (P.subgroupOf Smax) Sfam :=
    theorem_13_3_inducedFromNonkernelFamily_of_sourceData
      hSTypePDef Sfam hSnonker
  have hSign : theorem_13_3_signNormalizationFor
      (Nat.card W2) (Nat.card W1) δ δ' :=
    hypothesis_13_1_signNormalizationFor_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      (Nat.card W2) (Nat.card W1) u v c d hcase hSTypeP hTTypeP
      hsourceOrig ω η μ ν μsum νsum δ δ' σ hnotation
  have hCharData :=
    hypothesis_13_1_muSum_characterData_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      (Nat.card W2) (Nat.card W1) u v c d hsourceOrig
      ω η μ ν μsum νsum δ δ' σ hnotation
  rcases hypothesis_13_1_selectedColumnTransportData_of_sourceData
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hSelected, row, col, hrow0, hcol0, hcol_ne,
      hcol_inj, hcol_surj, hDelta, hColumn, hOmegaColumn⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases theorem_13_3_fittingSupportedFourSixData_of_typeP hSTypeP hSelected with
    ⟨σS, xChar, H_A, hSupported⟩
  have hContext :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53 Smax hSupported
  have hPF58 :=
    Section5.theorem_5_8_core
      (K := derivedSubgroup Smax)
      (W1 := W1.subgroupOf Smax)
      (W2 := W2.subgroupOf Smax)
      (W := Wsec)
      (H := P.subgroupOf Smax)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ωsec)
      (σL := σS)
      (σ := σsec)
      (piChar := μsel)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τS)
      (S := Sfam)
      hContext h52a ⟨X, hXirr⟩ hInd
  have hColumnMem : ∀ j, 0 < j → j < Nat.card W2 →
      Section10.muColumn μsel (col j) ∈ Sfam := by
    intro j hj0 hj
    rw [hColumn j hj0 hj]
    exact (hCharData j hj0 hj).2.2.2
  have hSelectedAlt : ∀ a : J, a ≠ j0 →
      Section10.muColumn μsel a ∈ Sfam →
      ∀ b : J,
        Section1.conjugateCharacter (Section10.muColumn μsel a) =
            Section10.muColumn μsel b →
          (τ1 (Section10.muColumn μsel a) =
              (δSign a : ℂ) •
                Section4Scratch.omegaColumnSigma σsec ωsec a) ∨
            (τ1 (Section10.muColumn μsel a) =
                (-(δSign a : ℂ)) •
                  Section4Scratch.omegaColumnSigma σsec ωsec b ∧
              ∀ l : J, l ≠ j0 →
                Section10.muColumn μsel l ∈ Sfam →
                  Section1.degree (Section10.muColumn μsel l) =
                    Section1.degree (Section10.muColumn μsel a) →
                    l = b ∨ l = a) := by
    intro a ha0 haS b hconj
    simpa [Section10.muColumn, Section4Scratch.piColumn] using
      hPF58 a ha0
        (by simpa [Section10.muColumn, Section4Scratch.piColumn] using haS)
        b
        (by simpa [Section10.muColumn, Section4Scratch.piColumn] using hconj)
        τ1 hIso hVirt hAgree
  have hNaturalAlt : ∀ j, 0 < j → j < Nat.card W2 →
      τ1 (μsum j) =
          (Finset.range (Nat.card W1)).sum (fun i => η i j) ∨
        ∃ k, 0 < k ∧ k < Nat.card W2 ∧ k ≠ j ∧
          Section1.conjugateCharacter
              (Section10.muColumn μsel (col j)) =
            Section10.muColumn μsel (col k) ∧
          τ1 (μsum j) =
            -((Finset.range (Nat.card W1)).sum (fun i => η i k)) ∧
          ∀ l, 0 < l → l < Nat.card W2 → l = k ∨ l = j := by
    intro j hj0 hj
    rcases theorem_13_3_exists_conjugate_muColumn_index_of_supportedData
        hSupported (hcol_ne j hj0 hj) with
      ⟨b, hb0, hconj, hne⟩
    rcases hcol_surj b with ⟨k, hk, hcolk⟩
    have hk0 : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      apply hb0
      exact hcolk ▸ hcol0
    have hkj : k ≠ j := by
      intro hkj
      subst k
      apply hne
      rw [← hcolk]
    have hconjJK :
        Section1.conjugateCharacter
            (Section10.muColumn μsel (col j)) =
          Section10.muColumn μsel (col k) := by
      rw [hcolk]
      exact hconj
    rcases hSelectedAlt (col j) (hcol_ne j hj0 hj)
        (hColumnMem j hj0 hj) b hconj with hpos | hneg
    · left
      calc
        τ1 (μsum j) = τ1 (Section10.muColumn μsel (col j)) := by
          rw [hColumn j hj0 hj]
        _ = (δSign (col j) : ℂ) •
            Section4Scratch.omegaColumnSigma σsec ωsec (col j) := hpos
        _ = Section4Scratch.omegaColumnSigma σsec ωsec (col j) := by
          simp [hDelta j hj0 hj, hSign.1 j hj]
        _ = (Finset.range (Nat.card W1)).sum (fun i => η i j) :=
          hOmegaColumn j hj0 hj
    · right
      refine ⟨k, hk0, hk, hkj, hconjJK, ?_, ?_⟩
      · calc
          τ1 (μsum j) = τ1 (Section10.muColumn μsel (col j)) := by
            rw [hColumn j hj0 hj]
          _ = (-(δSign (col j) : ℂ)) •
              Section4Scratch.omegaColumnSigma σsec ωsec b := hneg.1
          _ = -Section4Scratch.omegaColumnSigma σsec ωsec (col k) := by
            rw [hcolk]
            simp [hDelta j hj0 hj, hSign.1 j hj]
          _ = -((Finset.range (Nat.card W1)).sum (fun i => η i k)) := by
            rw [hOmegaColumn k hk0 hk]
      · intro l hl0 hl
        have hdeg :
            Section1.degree (Section10.muColumn μsel (col l)) =
              Section1.degree (Section10.muColumn μsel (col j)) := by
          rw [hColumn l hl0 hl, hColumn j hj0 hj]
          exact (hCharData l hl0 hl).2.1.trans
            (hCharData j hj0 hj).2.1.symm
        rcases hneg.2 (col l) (hcol_ne l hl0 hl)
            (hColumnMem l hl0 hl) hdeg with hlb | hlj
        · left
          apply hcol_inj l k hl hk
          exact hlb.trans hcolk.symm
        · right
          exact hcol_inj l j hl hj hlj
  by_cases hAll : ∀ j, 0 < j → j < Nat.card W2 →
      τ1 (μsum j) =
        (Finset.range (Nat.card W1)).sum (fun i => η i j)
  · exact Or.inl hAll
  · right
    push Not at hAll
    rcases hAll with ⟨j, hj0, hj, hjneg⟩
    rcases hNaturalAlt j hj0 hj with hpos |
      ⟨k, hk0, hk, hkj, hconjJK, hnegJK, huniq⟩
    · exact (hjneg hpos).elim
    · have hcard_le_three : Nat.card W2 ≤ 3 := by
        by_contra hcard
        have h4 : 4 ≤ Nat.card W2 := by omega
        have h1 := huniq 1 (by omega) (by omega)
        have h2 := huniq 2 (by omega) (by omega)
        have h3 := huniq 3 (by omega) (by omega)
        rcases h1 with h1 | h1 <;>
          rcases h2 with h2 | h2 <;>
            rcases h3 with h3 | h3 <;> omega
      have hcaseCopy := hcase
      rcases hcaseCopy with
        ⟨_hprod, _hcyc, _hW1ne, hW2ne, _hrest⟩
      have hodd : Odd (Nat.card W2) :=
        Odd.of_dvd_nat hmin.odd_order
          (Subgroup.card_subgroup_dvd_card W2)
      have hcard_ne_one : Nat.card W2 ≠ 1 := by
        intro hcard
        exact hW2ne ((Subgroup.card_eq_one (H := W2)).mp hcard)
      have hcard_pos : 0 < Nat.card W2 := Nat.card_pos (α := W2)
      rcases hodd with ⟨m, hm⟩
      have hcard : Nat.card W2 = 3 := by omega
      have hconjKJ :
          Section1.conjugateCharacter
              (Section10.muColumn μsel (col k)) =
            Section10.muColumn μsel (col j) := by
        rw [← hconjJK, Section12.conjugateCharacter_involutive]
      rcases hSelectedAlt (col k) (hcol_ne k hk0 hk)
          (hColumnMem k hk0 hk) (col j) hconjKJ with hposK | hnegK
      · have hposKNat :
            τ1 (μsum k) =
              (Finset.range (Nat.card W1)).sum (fun i => η i k) := by
          calc
            τ1 (μsum k) = τ1 (Section10.muColumn μsel (col k)) := by
              rw [hColumn k hk0 hk]
            _ = (δSign (col k) : ℂ) •
                Section4Scratch.omegaColumnSigma σsec ωsec (col k) := hposK
            _ = Section4Scratch.omegaColumnSigma σsec ωsec (col k) := by
              simp [hDelta k hk0 hk, hSign.1 k hk]
            _ = (Finset.range (Nat.card W1)).sum (fun i => η i k) :=
              hOmegaColumn k hk0 hk
        have himage : τ1 (μsum j) = -τ1 (μsum k) := by
          calc
            τ1 (μsum j) =
                -((Finset.range (Nat.card W1)).sum (fun i => η i k)) := hnegJK
            _ = -τ1 (μsum k) := congrArg Neg.neg hposKNat.symm
        have hcoljk : col j ≠ col k := by
          intro hEq
          exact hkj (hcol_inj j k hj hk hEq).symm
        have hsourceCross :
            Section1.scalarProduct Smax (μsum j) (μsum k) = 0 := by
          rw [← hColumn j hj0 hj, ← hColumn k hk0 hk]
          exact
            Section10.scalarProduct_muColumn_eq_zero_of_ne_of_section10FourSixNotationSupportedData
              hSelected hcoljk
        have hsourceSelf :
            Section1.scalarProduct Smax (μsum k) (μsum k) =
              (Fintype.card I : ℂ) := by
          rw [← hColumn k hk0 hk]
          exact
            Section10.scalarProduct_muColumn_self_of_section10FourSixNotationSupportedData
              hSelected (col k)
        have hambientCross :
            Section1.scalarProduct G (τ1 (μsum j)) (τ1 (μsum k)) = 0 :=
          (Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso
            (hCharData j hj0 hj).2.2.2
            (hCharData k hk0 hk).2.2.2).trans hsourceCross
        have hambientSelf :
            Section1.scalarProduct G (τ1 (μsum k)) (τ1 (μsum k)) =
              (Fintype.card I : ℂ) :=
          (Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso
            (hCharData k hk0 hk).2.2.2
            (hCharData k hk0 hk).2.2.2).trans hsourceSelf
        have hnegScalar :
            Section1.scalarProduct G (-τ1 (μsum k)) (τ1 (μsum k)) =
              -Section1.scalarProduct G (τ1 (μsum k)) (τ1 (μsum k)) := by
          have hEq :
              (-τ1 (μsum k) : Section1.ClassFunction G) =
                (-1 : ℂ) • τ1 (μsum k) := by
            ext g
            simp
          rw [hEq, Section1.scalarProduct_smul_left]
          simp
        rw [himage, hnegScalar, hambientSelf] at hambientCross
        have hcardI : (Fintype.card I : ℂ) ≠ 0 := by
          exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i0⟩).ne'
        exact (hcardI (neg_eq_zero.mp hambientCross)).elim
      · have hnegKNat :
            τ1 (μsum k) =
              -((Finset.range (Nat.card W1)).sum (fun i => η i j)) := by
          calc
            τ1 (μsum k) = τ1 (Section10.muColumn μsel (col k)) := by
              rw [hColumn k hk0 hk]
            _ = (-(δSign (col k) : ℂ)) •
                Section4Scratch.omegaColumnSigma σsec ωsec (col j) := hnegK.1
            _ = -Section4Scratch.omegaColumnSigma σsec ωsec (col j) := by
              simp [hDelta k hk0 hk, hSign.1 k hk]
            _ = -((Finset.range (Nat.card W1)).sum (fun i => η i j)) := by
              rw [hOmegaColumn j hj0 hj]
        have hjCases : j = 1 ∨ j = 2 := by omega
        have hkCases : k = 1 ∨ k = 2 := by omega
        have hpairJK : ({j, k} : Finset ℕ) = {1, 2} := by
          rcases hjCases with rfl | rfl
          · rcases hkCases with rfl | rfl
            · exact (hkj rfl).elim
            · rfl
          · rcases hkCases with rfl | rfl
            · exact Finset.pair_comm 2 1
            · exact (hkj rfl).elim
        have hpairKJ : ({k, j} : Finset ℕ) = {1, 2} := by
          rcases hjCases with rfl | rfl
          · rcases hkCases with rfl | rfl
            · exact (hkj rfl).elim
            · exact Finset.pair_comm 2 1
          · rcases hkCases with rfl | rfl
            · rfl
            · exact (hkj rfl).elim
        refine ⟨hcard, ?_⟩
        intro l hl0 hl
        rcases huniq l hl0 hl with rfl | rfl
        · exact ⟨j, hpairKJ, hnegKNat⟩
        · exact ⟨k, hpairJK, hnegJK⟩

private theorem theorem_13_3_allReducible_exists_positiveExtension
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hAllReducible : ∀ X : Sfam,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (X : Section1.ClassFunction Smax)) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          ∃ τ1 : Section1.ClassFunction Smax →ₗ[ℂ]
              Section1.ClassFunction G,
            Section6.coherentExtension Sfam τS τ1 ∧
              ∀ j, 0 < j → j < p →
                τ1 (μsum j) =
                  (Finset.range q).sum (fun i => η i j) := by
  classical
  have hsourceOrig := hsource
  have hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q :=
    section13_theorem_13_2_caseBData_bg_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hSTypeP : Section8.typePData Smax P U W1 W2 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hsourceSwap := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have hTTypeP : Section8.typePData Tmax Q V W2 W1 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceSwap
  rcases hsource with
    ⟨_hcaseSource, hSTypePDef, _hTTypePDef, hp, hq, _hC, _hD, _hc,
      _hd, _hUcard, _hVcard, hSnonker, hTnonker, hDadeS, hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, hmin, hFourSixS,
      hFourSixT⟩
  subst p
  subst q
  letI : IsMinCE G := hmin
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hSign : theorem_13_3_signNormalizationFor
      (Nat.card W2) (Nat.card W1) δ δ' :=
    hypothesis_13_1_signNormalizationFor_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      (Nat.card W2) (Nat.card W1) u v c d hcase hSTypeP hTTypeP
      hsourceOrig ω η μ ν μsum νsum δ δ' σ hnotation
  have hCharData :=
    hypothesis_13_1_muSum_characterData_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      (Nat.card W2) (Nat.card W1) u v c d hsourceOrig
      ω η μ ν μsum νsum δ δ' σ hnotation
  rcases hypothesis_13_1_selectedColumnTransportData_of_sourceData
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hSelected, row, col, hrow0, hcol0, hcol_ne,
      hcol_inj, hcol_surj, hDelta, hColumn, hOmegaColumn⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases theorem_13_3_fittingSupportedFourSixData_of_typeP hSTypeP hSelected with
    ⟨σS, xChar, H_A, hSupported⟩
  have hSupportedCopy := hSupported
  rcases hSupportedCopy with
    ⟨_h46, _hW2K, _h31, _hSigmaIso, hSigmaVirt, _hSigmaClass,
      _hSigmaPrincipal, _h22A, hSupportedRest⟩
  rcases hSupportedRest with
    ⟨hOmega, h43b, _h43c, _h43d, h45a, h45b, _hTauCyclic, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  have hContext :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53 Smax hSupported
  rcases hContext with
    ⟨_h46', _hTauCyclic', _hTauA0', _hTauIso', _hTauPunct',
      _hTauVirt', _h52b, _hOmega', _chi, _hChiOrth, _hChiSigned,
      _hChiSigma, _h43b', _h43c', _h43d', _h45a', _h45b', _h47,
      _h48, h49a, h49b, _h410⟩
  have hcaseCopy := hcase
  rcases hcaseCopy with
    ⟨_hprod, _hcyc, _hW1ne, hW2ne, _hrest⟩
  have hcard_ne_one : Nat.card W2 ≠ 1 := by
    intro hcard
    exact hW2ne ((Subgroup.card_eq_one (H := W2)).mp hcard)
  have hcard_pos : 0 < Nat.card W2 := Nat.card_pos (α := W2)
  have hone : 1 < Nat.card W2 := by omega
  let k : J := col 1
  have hk : k ≠ j0 := by
    exact hcol_ne 1 (by omega) hone
  have hSignK : (δSign k : ℂ) = 1 := by
    dsimp [k]
    rw [hDelta 1 (by omega) hone, hSign.1 1 hone]
    norm_num
  have hColumnMemNatural : ∀ j, 0 < j → j < Nat.card W2 →
      Section10.muColumn μsel (col j) ∈ Sfam := by
    intro j hj0 hj
    rw [hColumn j hj0 hj]
    exact (hCharData j hj0 hj).2.2.2
  have hColumnMem : ∀ j : J, j ≠ j0 →
      Section10.muColumn μsel j ∈ Sfam := by
    intro j hj
    rcases hcol_surj j with ⟨l, hl, hcoll⟩
    have hl0 : 0 < l := by
      by_contra hl0
      have hlzero : l = 0 := Nat.eq_zero_of_not_pos hl0
      subst l
      apply hj
      rw [← hcoll, hcol0]
    rw [← hcoll]
    exact hColumnMemNatural l hl0 hl
  have hColumnDegree : ∀ j : J, j ≠ j0 →
      Section1.degree (Section10.muColumn μsel j) =
        Section1.degree (Section10.muColumn μsel k) := by
    intro j hj
    rcases hcol_surj j with ⟨l, hl, hcoll⟩
    have hl0 : 0 < l := by
      by_contra hl0
      have hlzero : l = 0 := Nat.eq_zero_of_not_pos hl0
      subst l
      apply hj
      rw [← hcoll, hcol0]
    calc
      Section1.degree (Section10.muColumn μsel j) =
          Section1.degree (μsum l) := by rw [← hcoll, hColumn l hl0 hl]
      _ = (u * Nat.card W1 : ℂ) := (hCharData l hl0 hl).2.1
      _ = Section1.degree (μsum 1) :=
        (hCharData 1 (by omega) hone).2.1.symm
      _ = Section1.degree (Section10.muColumn μsel k) := by
        dsimp [k]
        rw [hColumn 1 (by omega) hone]
  let T := Section4Scratch.equalDegreeColumnIndex μsel j0 k
  let sourceColumn : T → Section1.ClassFunction Smax :=
    fun t => Section10.muColumn μsel t.1
  let targetColumn : T → Section1.ClassFunction G :=
    fun t => Section4Scratch.omegaColumnSigma σsec ωsec t.1
  have hInd : Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup Smax) (P.subgroupOf Smax) Sfam :=
    theorem_13_3_inducedFromNonkernelFamily_of_sourceData
      hSTypePDef Sfam hSnonker
  have hClassify : ∀ X : Sfam, ∃ j : J, j ≠ j0 ∧
      (X : Section1.ClassFunction Smax) = Section10.muColumn μsel j := by
    intro X
    simpa [Section10.muColumn, Section4Scratch.piColumn] using
      (Section5.theorem_5_3_b_nonbase_piColumn_pf53
        hOmega h43b h45a h45b hInd X (hAllReducible X))
  let columnToSfam : T → Sfam := fun t =>
    ⟨sourceColumn t, hColumnMem t.1 t.2.1⟩
  have hColumnToSfamInjective : Function.Injective columnToSfam := by
    intro t1 t2 ht
    apply Subtype.ext
    apply Section5.piColumn_injective_pf58 hOmega h43b
    exact congrArg (fun X : Sfam => (X : Section1.ClassFunction Smax)) ht
  have hColumnToSfamSurjective : Function.Surjective columnToSfam := by
    intro X
    rcases hClassify X with ⟨j, hj, hX⟩
    let t : T := ⟨j, hj, hColumnDegree j hj⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact hX.symm
  let e : T ≃ Sfam := Equiv.ofBijective columnToSfam
    ⟨hColumnToSfamInjective, hColumnToSfamSurjective⟩
  have he : ∀ t : T,
      ((e t : Sfam) : Section1.ClassFunction Smax) = sourceColumn t := by
    intro t
    rfl
  let Z := I × T
  let sourceEntry : Z → Section1.ClassFunction Smax :=
    fun z => μsel z.1 z.2.1
  let targetEntry : Z → Section1.ClassFunction G :=
    fun z => σsec (ωsec z.1 z.2.1)
  have hSourceEntryOrth : ∀ z w : Z,
      Section1.scalarProduct Smax (sourceEntry z) (sourceEntry w) =
        if z = w then 1 else 0 := by
    intro z w
    by_cases hzw : z = w
    · subst w
      simp [sourceEntry,
        Section10.scalarProduct_irreducible_self (h43b.2.2.1 z.1 z.2.1)]
    · have hpair : (z.1, z.2.1) ≠ (w.1, w.2.1) := by
        intro hEq
        apply hzw
        apply Prod.ext
        · exact congrArg (fun x : I × J => x.1) hEq
        · apply Subtype.ext
          exact congrArg (fun x : I × J => x.2) hEq
      have hne : sourceEntry z ≠ sourceEntry w :=
        h43b.2.2.2.1 (z.1, z.2.1) (w.1, w.2.1) hpair
      simp [hzw, sourceEntry, Section10.scalarProduct_irreducible_ne
        (h43b.2.2.1 z.1 z.2.1) (h43b.2.2.1 w.1 w.2.1) hne]
  have hSourceEntryLI : LinearIndependent ℂ sourceEntry := by
    rw [Fintype.linearIndependent_iff]
    intro a ha z
    have hsumFun :
        (∑ w : Z, a w • sourceEntry w) =
          (fun g => ∑ w : Z, (a w • sourceEntry w) g) := by
      ext g
      simp
    have hinner :
        Section1.scalarProduct Smax (∑ w : Z, a w • sourceEntry w)
            (sourceEntry z) = 0 := by
      rw [ha]
      simp [Section1.scalarProduct]
    have hcoeff :
        Section1.scalarProduct Smax (∑ w : Z, a w • sourceEntry w)
            (sourceEntry z) = a z := by
      rw [hsumFun, Section1.scalarProduct_fintype_sum_left]
      simp_rw [Section1.scalarProduct_smul_left, hSourceEntryOrth]
      simpa [mul_ite] using (Fintype.sum_ite_eq' z a)
    exact hcoeff ▸ hinner
  let basis := Module.Basis.sumExtend hSourceEntryLI
  have hBasisInl : ∀ z : Z, basis (Sum.inl z) = sourceEntry z := by
    intro z
    unfold basis Module.Basis.sumExtend
    rw [Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
    rfl
  let basisImage :
      Z ⊕ Module.Basis.sumExtendIndex hSourceEntryLI →
        Section1.ClassFunction G :=
    fun z => Sum.elim targetEntry (fun _ => 0) z
  let τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G :=
    basis.constr ℂ basisImage
  have hTau1Entry : ∀ z : Z, τ1 (sourceEntry z) = targetEntry z := by
    intro z
    calc
      τ1 (sourceEntry z) = τ1 (basis (Sum.inl z)) := by rw [hBasisInl]
      _ = basisImage (Sum.inl z) :=
        basis.constr_basis ℂ basisImage (Sum.inl z)
      _ = targetEntry z := rfl
  have hTau1Column : ∀ t : T, τ1 (sourceColumn t) = targetColumn t := by
    intro t
    rw [show sourceColumn t = ∑ i : I, sourceEntry (i, t) by rfl, map_sum]
    change (∑ i : I, τ1 (sourceEntry (i, t))) =
      ∑ i : I, targetEntry (i, t)
    exact Finset.sum_congr rfl (fun i _hi => hTau1Entry (i, t))
  have hEvalCoeffBasisSource : ∀ (f : T → Section1.ClassFunction Smax) (t : T),
      Section1.evalCoeff f (Section1.basisVector t) = f t := by
    intro f t
    ext g
    rw [Section1.evalCoeff, Finset.sum_eq_single t]
    · simp [Section1.basisVector]
    · intro l _hl hlt
      simp [Section1.basisVector, hlt]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  have hEvalCoeffBasisTarget : ∀ (f : T → Section1.ClassFunction G) (t : T),
      Section1.evalCoeff f (Section1.basisVector t) = f t := by
    intro f t
    ext g
    rw [Section1.evalCoeff, Finset.sum_eq_single t]
    · simp [Section1.basisVector]
    · intro l _hl hlt
      simp [Section1.basisVector, hlt]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  have h49bData := h49b k hk hk
  have hColumnGram : ∀ t s : T,
      Section1.scalarProduct G (targetColumn t) (targetColumn s) =
        Section1.scalarProduct Smax (sourceColumn t) (sourceColumn s) := by
    intro t s
    have hgram := h49bData.1
      (Section1.basisVector t) (Section1.basisVector s)
    rw [hEvalCoeffBasisTarget, hEvalCoeffBasisTarget,
      hEvalCoeffBasisSource, hEvalCoeffBasisSource] at hgram
    simpa [sourceColumn, targetColumn, hSignK, Section10.muColumn, Section4Scratch.piColumn] using hgram
  have hLands :=
    Section4Scratch.theorem_4_9_b_lands_in_zIrr
      (derivedSubgroup Smax) (W1.subgroupOf Smax) (W2.subgroupOf Smax)
      Wsec i0 j0 k ωsec σS σsec μsel (fun j => (δSign j : ℂ))
      hSigmaVirt hOmega h43b
  have hColumnVirt : ∀ t : T,
      Theory.Character.IsVirtualCharacter (targetColumn t) := by
    intro t
    have hvirt := hLands hk (Section1.basisVector t)
    rw [hEvalCoeffBasisTarget] at hvirt
    simpa [targetColumn, hSignK] using hvirt
  have hBasisGram : ∀ X Y : Sfam,
      Section1.scalarProduct G (τ1 X) (τ1 Y) =
        Section1.scalarProduct Smax X Y := by
    intro X Y
    have hX : (X : Section1.ClassFunction Smax) =
        sourceColumn (e.symm X) := by
      simpa using he (e.symm X)
    have hY : (Y : Section1.ClassFunction Smax) =
        sourceColumn (e.symm Y) := by
      simpa using he (e.symm Y)
    rw [hX, hY, hTau1Column, hTau1Column]
    exact hColumnGram (e.symm X) (e.symm Y)
  have hBasisVirt : ∀ X : Sfam,
      Theory.Character.IsVirtualCharacter (τ1 X) := by
    intro X
    have hX : (X : Section1.ClassFunction Smax) =
        sourceColumn (e.symm X) := by
      simpa using he (e.symm X)
    rw [hX, hTau1Column]
    exact hColumnVirt (e.symm X)
  have hAgreement :
      Section5.agreesOnIntegerSpanOn Sfam Section5.puncturedSet τS τ1 := by
    intro phi hphi
    rcases hphi with ⟨⟨coeff, rfl⟩, hPunct⟩
    let w : Section1.CoeffVector T := fun t => coeff (e t)
    have hSourceEval :
        Section1.evalCoeff sourceColumn w =
          Section1.evalCoeff
            (fun X : Sfam => (X : Section1.ClassFunction Smax)) coeff := by
      rw [Section1.evalCoeff, Section1.evalCoeff]
      exact Fintype.sum_equiv e
        (fun t : T => (w t : ℂ) • sourceColumn t)
        (fun X : Sfam =>
          (coeff X : ℂ) • (X : Section1.ClassFunction Smax))
        (by intro t; simp [w, he t])
    have hSourcePunct :
        Section1.supportedOn (Section1.evalCoeff sourceColumn w)
          Section5.puncturedSet := by
      rw [hSourceEval]
      exact hPunct
    have hA : Section1.supportedOn
        (Section1.evalCoeff sourceColumn w) A :=
      ((h49a k hk hk).2.2 w).mp hSourcePunct
    have hTauAgreement :
        τS (Section1.evalCoeff sourceColumn w) =
          Section1.evalCoeff targetColumn w := by
      simpa [sourceColumn, targetColumn, hSignK, Section10.muColumn, Section4Scratch.piColumn] using
        h49bData.2 w hA
    calc
      τ1 (Section1.evalCoeff
          (fun X : Sfam => (X : Section1.ClassFunction Smax)) coeff) =
          τ1 (Section1.evalCoeff sourceColumn w) := by rw [hSourceEval]
      _ = Section1.evalCoeff targetColumn w := by
        rw [Section5.map_evalCoeff]
        exact congrArg (fun f => Section1.evalCoeff f w)
          (funext hTau1Column)
      _ = τS (Section1.evalCoeff sourceColumn w) := hTauAgreement.symm
      _ = τS (Section1.evalCoeff
          (fun X : Sfam => (X : Section1.ClassFunction Smax)) coeff) := by
        rw [hSourceEval]
  have hExt : Section6.coherentExtension Sfam τS τ1 := by
    refine ⟨?_, ?_, hAgreement⟩
    · intro phi psi hphi hpsi
      rcases hphi with ⟨a, rfl⟩
      rcases hpsi with ⟨b, rfl⟩
      rw [Section5.map_evalCoeff, Section5.map_evalCoeff]
      exact Section5.scalarProduct_evalCoeff_eq_of_gram_eq
        (fun X : Sfam => (X : Section1.ClassFunction Smax))
        (fun X : Sfam => τ1 (X : Section1.ClassFunction Smax))
        hBasisGram a b
    · intro phi hphi
      rcases hphi with ⟨a, rfl⟩
      rw [Section5.map_evalCoeff]
      exact Section5.isVirtualCharacter_evalCoeff_pf59
        (fun X : Sfam => τ1 (X : Section1.ClassFunction Smax))
        hBasisVirt a
  refine ⟨τ1, hExt, ?_⟩
  intro j hj0 hj
  let t : T := ⟨col j, hcol_ne j hj0 hj,
    hColumnDegree (col j) (hcol_ne j hj0 hj)⟩
  have hSourceColumn : sourceColumn t = μsum j := by
    exact hColumn j hj0 hj
  calc
    τ1 (μsum j) = τ1 (sourceColumn t) := by rw [hSourceColumn]
    _ = targetColumn t := hTau1Column t
    _ = (Finset.range (Nat.card W1)).sum (fun i => η i j) :=
      hOmegaColumn j hj0 hj

private theorem theorem_13_3_exists_signAlternativeExtension_of_sourceData
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          ∃ τ1 : Section1.ClassFunction Smax →ₗ[ℂ]
              Section1.ClassFunction G,
            Section6.coherentExtension Sfam τS τ1 ∧
              theorem_13_3_signAlternativeData p q
                (fun j => τ1 (μsum j)) η := by
  classical
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  by_cases hAllReducible : ∀ X : Sfam,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (X : Section1.ClassFunction Smax)
  · rcases theorem_13_3_allReducible_exists_positiveExtension
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource hAllReducible
        ω η μ ν μsum νsum δ δ' σ hnotation with
      ⟨τ1, hExt, hPositive⟩
    exact ⟨τ1, hExt, Or.inl hPositive⟩
  · have hIrr : ∃ X : Sfam,
        Section1.IsIrreducibleCharacterOnGroup
          (X : Section1.ClassFunction Smax) := by
      push Not at hAllReducible
      exact hAllReducible
    rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d hsource with
      ⟨_hMF, _htype, _htypeLarge, _hUcomm, _hfrob, _hPelem, _hPcard,
        _huBound, hCoherent, _hbook, _hAZero, _hnorm⟩
    unfold Section6.coherentFamily Section5.definition_5_1_statement
      Section5.IsCoherentTriple at hCoherent
    rcases hCoherent with
      ⟨_hSourceVirt, _hSpanNonempty, τ1, hIso, hVirt, hAgree⟩
    have hAlternative :=
      theorem_13_3_irreducibleBranch_for_coherentExtension
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource τ1 hIso hVirt hAgree hIrr
        ω η μ ν μsum νsum δ δ' σ hnotation
    exact ⟨τ1, ⟨hIso, hVirt, hAgree⟩, hAlternative⟩

private theorem theorem_13_3_notation_output_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
          ω η μ ν μsum νsum δ δ' σ →
            theorem_13_3_signNormalizationFor p q δ δ' ∧
              ∃ τ1 : Section1.ClassFunction Smax →ₗ[ℂ]
                  Section1.ClassFunction G,
                Section6.coherentExtension Sfam τS τ1 ∧
                  theorem_13_3_characterOutputFor
                    Smax P C Sfam τ1 p q u μsum η := by
  classical
  have hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q :=
    section13_theorem_13_2_caseBData_bg_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hSTypeP : Section8.typePData Smax P U W1 W2 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hsourceSwap := section13_hypothesis_13_1_sourceData_swap hsource
  have hTTypeP : Section8.typePData Tmax Q V W2 W1 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceSwap
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hSign : theorem_13_3_signNormalizationFor p q δ δ' :=
    hypothesis_13_1_signNormalizationFor_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hcase hSTypeP hTTypeP hsource
      ω η μ ν μsum νsum δ δ' σ hnotation
  have hCharacter :=
    hypothesis_13_1_muSum_characterData_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
      ω η μ ν μsum νsum δ δ' σ hnotation
  rcases theorem_13_3_exists_signAlternativeExtension_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
      ω η μ ν μsum νsum δ δ' σ hnotation with
    ⟨τ1, hExt, hAlternative⟩
  exact ⟨hSign, τ1, hExt, hCharacter, hAlternative⟩

private theorem theorem_13_3_kernelInducedFamily_bot_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hTypePDef : Section8.typePDefinitionData Smax P U W1 W2)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam) :
    Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
      (⊥ : Subgroup G) Sfam := by
  rcases hTypePDef with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  rw [hDerComp.2.2.1]
  rcases hSfam with ⟨_hPUleS, hPlePU, hmem⟩
  refine ⟨bot_le, hPlePU, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθnotker, hχeq⟩
    refine ⟨θ, hθirr, hθnotker, ?_, hχeq⟩
    intro a
    have haS : ((a : (P ⊔ U).subgroupOf Smax) : Smax) = 1 := by
      apply Subtype.ext
      have haBot :
          (((a : (P ⊔ U).subgroupOf Smax) : Smax) : G) ∈
            (⊥ : Subgroup G) := by
        simpa [Subgroup.mem_subgroupOf] using a.property
      simpa [Subgroup.mem_bot] using haBot
    have ha : (a : (P ⊔ U).subgroupOf Smax) = 1 := by
      exact Subtype.ext haS
    simp [ha, Section1.degree]
  · rintro ⟨θ, hθirr, hθnotker, _hθbot, hχeq⟩
    rw [hmem χ]
    exact ⟨θ, hθirr, hθnotker, hχeq⟩

private theorem theorem_13_3_kernelInducedSubfamily_of_le
    {G : Type u} [Group G] [Finite G]
    {Smax P Y : Subgroup G}
    (Sfam : Finset (Section1.ClassFunction Smax))
    (hSbot : Section9.kernelInducedFamily Smax
      (ambientDerivedSubgroup Smax) P (⊥ : Subgroup G) Sfam)
    (hYle : Y ≤ ambientDerivedSubgroup Smax) :
    ∃ SY : Finset (Section1.ClassFunction Smax),
      SY ⊆ Sfam ∧
        Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P Y SY := by
  classical
  let SY := Section9.kernelInducedSubfamily_sec9 Smax
    (ambientDerivedSubgroup Smax) P Y Sfam
  refine ⟨SY, Section9.kernelInducedSubfamily_subset_sec9
    Smax (ambientDerivedSubgroup Smax) P Y Sfam, ?_⟩
  exact Section9.kernelInducedFamily_subfamily_of_le_sec9
    Smax (ambientDerivedSubgroup Smax) P (⊥ : Subgroup G) Y Sfam
    hYle bot_le hSbot

private theorem theorem_13_3_case_9_7_a_theorem_13_10_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcaseA : case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u) :
    theorem_13_10_hypothesis Smax P C Sfam p q u := by
  classical
  have hsourceFull := _hsource
  rcases _hsource with
    ⟨_hcase, hTypePDef, _hTypePDefT, _hp_card, _hq_card, hC, _hD,
      _hc_card, _hd_card, _hU_card, _hV_card, hSfam, _hTfam, _hDadeS,
      _hDadeT, _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, hMin, _hFourSixS,
      _hFourSixT⟩
  letI : IsMinCE G := hMin
  have hTypePDefCopy := hTypePDef
  rcases hTypePDefCopy with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hSbot : Section9.kernelInducedFamily Smax
      (ambientDerivedSubgroup Smax) P (⊥ : Subgroup G) Sfam :=
    theorem_13_3_kernelInducedFamily_bot_of_sourceData
      hTypePDef Sfam hSfam
  have hCleDer : C ≤ ambientDerivedSubgroup Smax := by
    intro x hx
    apply hUleDer
    have hx' : x ∈ subgroupCentralizerIn U P := by
      rw [← hC]
      exact hx
    exact hx'.1
  rcases theorem_13_3_kernelInducedSubfamily_of_le Sfam hSbot
      (Y := (⊥ : Subgroup G) ⊔ C) (by simpa using hCleDer) with
    ⟨SC, hSCsub, hSC⟩
  let Uprime : Subgroup G := (_root_.commutator U).map U.subtype
  have hUprimeLeDer : (⊥ : Subgroup G) ⊔ Uprime ≤ ambientDerivedSubgroup Smax := by
    apply sup_le bot_le
    rintro x ⟨y, _hy, rfl⟩
    exact hUleDer y.property
  rcases theorem_13_3_kernelInducedSubfamily_of_le Sfam hSbot
      (Y := (⊥ : Subgroup G) ⊔ Uprime) hUprimeLeDer with
    ⟨SU, _hSUsub, hSU⟩
  rcases _hcaseA with ⟨hBarU, a, hcaseAcore⟩
  have hchar := Section9.theorem_9_8_source_core_sec9
    Smax P U W1 W2 (⊥ : Subgroup G) C Uprime p q a u
    Sfam SC SU hcaseAcore hBarU rfl hSbot hSC hSU
  rcases hchar with
    ⟨_hdegreeDiv, _hunderlyingDiv, _hBarU, _hreducible, hExists, _hinitial⟩
  rcases hExists with ⟨χ, hχSC, hχirr, hχdegree, hχlinear⟩
  rcases hχlinear with ⟨θ, hθirr, hθdegree, hχeq⟩
  have hFitEq : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hTypePDef
  have hPCleS : P ⊔ C ≤ Smax := by
    rw [← hFitEq]
    exact section8FittingSubgroup_le Smax
  exact ⟨χ, hSCsub hχSC, hχirr, hχdegree.trans (mul_comm _ _),
    ⟨hPCleS, θ, hθirr, hθdegree, hχeq⟩⟩

private theorem theorem_13_3_case_9_7_b_no_theorem_13_10_tail_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hnot10 : ¬ theorem_13_10_hypothesis Smax P C Sfam p q u) :
    C = ⊥ ∧ u = (p ^ q - 1) / (p - 1) := by
  classical
  rcases _hsource with
    ⟨_hcase, hTypePDef, _hTypePDefT, _hp_card, _hq_card, hC, _hD,
      _hc_card, _hd_card, _hU_card, _hV_card, hSfam, _hTfam, _hDadeS,
      _hDadeT, _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, hMin, _hFourSixS,
      _hFourSixT⟩
  letI : IsMinCE G := hMin
  have hTypePDefCopy := hTypePDef
  rcases hTypePDefCopy with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hSbot : Section9.kernelInducedFamily Smax
      (ambientDerivedSubgroup Smax) P (⊥ : Subgroup G) Sfam :=
    theorem_13_3_kernelInducedFamily_bot_of_sourceData
      hTypePDef Sfam hSfam
  have hCleDer : C ≤ ambientDerivedSubgroup Smax := by
    intro x hx
    apply hUleDer
    have hx' : x ∈ subgroupCentralizerIn U P := by
      rw [← hC]
      exact hx
    exact hx'.1
  rcases theorem_13_3_kernelInducedSubfamily_of_le Sfam hSbot
      (Y := (⊥ : Subgroup G) ⊔ C) (by simpa using hCleDer) with
    ⟨SC, _hSCsub, hSC⟩
  let Cprime : Subgroup G := (_root_.commutator C).map C.subtype
  have hCprimeLeDer : (⊥ : Subgroup G) ⊔ Cprime ≤ ambientDerivedSubgroup Smax := by
    apply sup_le bot_le
    rintro x ⟨y, _hy, rfl⟩
    exact hCleDer y.property
  rcases theorem_13_3_kernelInducedSubfamily_of_le Sfam hSbot
      (Y := (⊥ : Subgroup G) ⊔ Cprime) hCprimeLeDer with
    ⟨SCprime, hSCprimeSub, hSCprime⟩
  have hcaseB9 :
      Section9.case_9_7_b_data Smax P U W1 W2 ⊥ C p q u := by
    simpa [case_9_7_b_sourceDataForSection13] using _hcaseB
  have hchar := Section9.theorem_9_9_source_core_sec9
    Smax P U W1 W2 (⊥ : Subgroup G) C Cprime p q u
    Sfam SC SCprime hcaseB9 rfl hSbot hSC hSCprime
  rcases hchar with
    ⟨_hdegreeDiv, hdegreeInduced, _hreducible, hnoIrreducible⟩
  apply hnoIrreducible
  rintro ⟨χ, hχSCprime, hχirr⟩
  rcases hdegreeInduced χ hχSCprime with ⟨hχdegree, hχlinear⟩
  rcases hχlinear with ⟨θ, hθirr, hθdegree, hχeq⟩
  have hFitEq : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hTypePDef
  have hPCleS : P ⊔ C ≤ Smax := by
    rw [← hFitEq]
    exact section8FittingSubgroup_le Smax
  exact _hnot10 ⟨χ, hSCprimeSub hχSCprime, hχirr,
    hχdegree.trans (mul_comm _ _),
    ⟨hPCleS, θ, hθirr, hθdegree, hχeq⟩⟩

private theorem theorem_13_3_no_theorem_13_10_case_b_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ¬ theorem_13_10_hypothesis Smax P C Sfam p q u →
      C = ⊥ ∧ case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u ∧
        u = (p ^ q - 1) / (p - 1) := by
  intro hnot10
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource with hcaseA | hcaseB
  · exact False.elim
      (hnot10
        (theorem_13_3_case_9_7_a_theorem_13_10_source
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d _hsource hcaseA))
  · rcases theorem_13_3_case_9_7_b_no_theorem_13_10_tail_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d _hsource hcaseB hnot10 with ⟨hC, hu⟩
    exact ⟨hC, hcaseB, hu⟩

public theorem theorem_13_3
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      (∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
        (η : ℕ → ℕ → Section1.ClassFunction G)
        (μ : ℕ → ℕ → Section1.ClassFunction Smax)
        (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
        (μsum : ℕ → Section1.ClassFunction Smax)
        (νsum : ℕ → Section1.ClassFunction Tmax)
        (δ δ' : ℕ → ℤ)
        (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
          hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
            theorem_13_3_signNormalizationFor p q δ δ' ∧
              ∃ τ1 : Section1.ClassFunction Smax →ₗ[ℂ]
                  Section1.ClassFunction G,
                Section6.coherentExtension Sfam τS τ1 ∧
                  theorem_13_3_characterOutputFor
                    Smax P C Sfam τ1 p q u μsum η) ∧
      (¬ theorem_13_10_hypothesis Smax P C Sfam p q u →
        C = ⊥ ∧ case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u ∧
          u = (p ^ q - 1) / (p - 1)) := by
  intro hsource
  exact
    ⟨theorem_13_3_notation_output_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource,
      theorem_13_3_no_theorem_13_10_case_b_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource⟩
end CFSG.Section13
