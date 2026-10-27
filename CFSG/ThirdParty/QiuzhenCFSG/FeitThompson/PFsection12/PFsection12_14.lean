module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.14)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.14) -/

/-- The source-data package for PF `(12.14)` implies the public character-value
comparison at `x * g`. -/
public theorem theorem_12_14_of_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (x g : G) (p : ℕ)
    (hsrc : theorem_12_14_source_data M K K' P0 L H Ls E e S R τ τ₁ χ ψ ψρ x g p)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ)
    (hxL : x ∈ L)
    (hgK : g ∈ K) :
    ψ (x * g) = ψρ ⟨x, hxL⟩ ∧
      ψρ ⟨x, hxL⟩ = χ ⟨x, hxL⟩ :=
  hsrc h128 h129 h13 hxL hgK

public theorem dadeSupport_eq_tildeA1_of_notation_8_14
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G)
    (hnot : Section8.notation_8_14_source_data
      M A A0 A1 D tildeA tildeA0 tildeA1 R) :
    Section2.dadeSupport A1 R = tildeA1 := by
  rcases hnot with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hR, _hRsource, _htildeA,
      _htildeA0, htildeA1⟩
  ext g
  constructor
  · rintro ⟨a, ha, r, hr, x, hx⟩
    rw [htildeA1]
    refine ⟨a, ha, a * r, ⟨r, hr, rfl⟩, x⁻¹, by trivial, ?_⟩
    calc
      g = x⁻¹ * Section2.conjBy x g * x := by
        simp [Section2.conjBy, mul_assoc]
      _ = x⁻¹ * (a * r) * x := by rw [hx]
      _ = x⁻¹ * (a * r) * x⁻¹⁻¹ := by simp
  · intro hg
    rw [htildeA1] at hg
    rcases hg with ⟨a, ha, z, ⟨r, hr, hz⟩, y, _hy, hg⟩
    refine ⟨a, ha, r, hr, y⁻¹, ?_⟩
    subst g
    subst z
    simp [Section2.conjBy, mul_assoc]

private theorem supportedOn_dadeTransform_of_CFon_subset
    {G : Type u} [Group G]
    {A A1 : Set G} {L : Subgroup G} {R : G → Subgroup G}
    (_hA1A : A1 ⊆ A)
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    {alpha : Section1.ClassFunction L}
    (halpha : Section2.CFOn L A1 alpha) :
    Section1.supportedOn
      (Section2.dadeTransform R hAL alpha) (Section2.dadeSupport A1 R) := by
  classical
  rw [Section1.supportedOn_iff]
  intro g hg
  by_cases hgA : ∃ a ∈ A, ∃ h ∈ R a, Section2.conjugateIn g (a * h)
  · let a : G := Classical.choose hgA
    have hspec := Classical.choose_spec hgA
    have ha : a ∈ A := hspec.1
    let r : G := Classical.choose hspec.2
    have hrspec := Classical.choose_spec hspec.2
    have hr : r ∈ R a := hrspec.1
    have hconj : Section2.conjugateIn g (a * r) := hrspec.2
    have ha1 : a ∉ A1 := by
      intro ha1
      exact hg ⟨a, ha1, r, hr, hconj⟩
    have hzero : alpha ⟨a, hAL a ha⟩ = 0 :=
      halpha.2 ⟨a, hAL a ha⟩ (by simpa using ha1)
    unfold Section2.dadeTransform
    rw [dif_pos hgA]
    simpa [a] using hzero
  · unfold Section2.dadeTransform
    rw [dif_neg hgA]

private theorem CFOn_a1Set_sub_conjugate_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    (hMF : section16MFSubgroup L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    {chi : Section1.ClassFunction L}
    (hchi : chi ∈ S) :
    Section2.CFOn L (Section8.a1Set H)
      (chi - Section1.conjugateCharacter chi) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  haveI : (H.subgroupOf L).Normal := section16MFSubgroup_subgroupOf_normal hMF
  have hchichar : Section1.IsCharacter chi := by
    rcases (hS chi).mp hchi with ⟨theta, hthetairr, _hthetane, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) theta
      (isCharacter_of_isIrreducibleCharacterOnGroup hthetairr)
  have hchiclass : Section1.IsClassFunction chi :=
    Section1.isCharacter_isClassFunction chi hchichar
  constructor
  · intro x g
    simp [Pi.sub_apply, Section1.conjugateCharacter, hchiclass x g]
  · intro l hlA1
    by_cases hlH : (l : G) ∈ H
    · have hl1G : (l : G) = 1 := by
        by_contra hlne
        exact hlA1 (by
          show (l : G) ∈ Section8.a1Set H
          simp [Section8.a1Set, section16NonidentityElements, hlH, hlne])
      have hl1 : l = 1 := Subtype.ext hl1G
      subst l
      have hdeg :
          Section1.degree (chi - Section1.conjugateCharacter chi) = 0 := by
        change Section1.degree chi -
          Section1.degree (Section1.conjugateCharacter chi) = 0
        rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hchichar]
        simp
      simpa [Section1.degree] using hdeg
    · have hlHsub : l ∉ H.subgroupOf L := by
        intro hl
        exact hlH hl
      have hchizero : chi l = 0 :=
        puncturedInducedFamily_eq_zero_of_not_mem
          (H.subgroupOf L) hS hchi hlHsub
      rw [Pi.sub_apply, hchizero]
      simp [Section1.conjugateCharacter, hchizero]

public theorem supportedOn_tau_sub_conjugate_tildeA1
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (hhyp : hypothesis_12_1_data L H S R tau)
    (hnot : Section8.notation_8_14_source_data L
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R)
    {chi : Section1.ClassFunction L}
    (hchi : chi ∈ S) :
    Section1.supportedOn
      (tau (chi - Section1.conjugateCharacter chi)) tildeA1 := by
  rcases hhyp with ⟨_hmax, hMF, _htypeI, hS, hDade⟩
  rcases hDade with ⟨_h22, hAL, htau⟩
  have hA1A : Section8.a1Set H ⊆ typeIASet L H := by
    simpa [Section8.a1Set] using
      nonidentity_kernel_subset_typeIASet L H (section16MFSubgroup_le hMF)
  have hCFa1 : Section2.CFOn L (Section8.a1Set H)
      (chi - Section1.conjugateCharacter chi) :=
    CFOn_a1Set_sub_conjugate_of_puncturedInducedFamily hMF hS hchi
  have hCFtype : Section2.CFOn L (typeIASet L H)
      (chi - Section1.conjugateCharacter chi) := CFOn_mono hA1A hCFa1
  rw [htau _ hCFtype]
  have hsupp := supportedOn_dadeTransform_of_CFon_subset (R := R) hA1A hAL hCFa1
  simpa [dadeSupport_eq_tildeA1_of_notation_8_14 L
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R hnot] using hsupp

public theorem coherentExtension_subsetSum_of_hypothesis52WithRData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R : S → Finset (Section1.ClassFunction G)}
    (h52 : hypothesis52WithRData S tau R)
    (hExt : Section7.isCoherentExtension S tau tau1)
    {chi : Section1.ClassFunction L} (hchi : chi ∈ S) :
    Section5.isSubsetSumOf (R ⟨chi, hchi⟩) (tau1 chi) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  rcases h52 with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
  let X : S := ⟨chi, hchi⟩
  have hchibar : Section1.conjugateCharacter chi ∈ S := by
    simpa [X] using (h52a X).1
  have hpairSub :
      ({(X : Section1.ClassFunction L),
        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
        Finset (Section1.ClassFunction L)) ⊆ S := by
    intro psi hpsi
    have hpsi' :
        psi = (X : Section1.ClassFunction L) ∨
          psi = Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
      simpa using hpsi
    rcases hpsi' with rfl | rfl
    · exact hchi
    · exact hchibar
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) tau1 :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSub hExt.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) tau1 :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub hExt.2.1
  have hdiffOn :
      Section5.integerSpanOn S Section5.puncturedSet
        (chi - Section1.conjugateCharacter chi) := by
    have hspan :
        Section5.integerSpan S (chi - Section1.conjugateCharacter chi) :=
      Section5.integerSpan_sub
        (Section5.integerSpan_of_mem S hchi)
        (Section5.integerSpan_of_mem S hchibar)
    have hchichar : Section1.IsCharacter chi := by
      simpa [X] using hsetup.2 X
    have hdeg :
        Section1.degree (chi - Section1.conjugateCharacter chi) = 0 := by
      change Section1.degree chi -
        Section1.degree (Section1.conjugateCharacter chi) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hchichar]
      simp
    exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
  have hagree :
      tau1 (chi - Section1.conjugateCharacter chi) =
        tau (chi - Section1.conjugateCharacter chi) :=
    hExt.2.2 _ hdiffOn
  have hsubsetX : Section5.isSubsetSumOf (R X)
      (tau1 (X : Section1.ClassFunction L)) :=
    Section5.theorem_5_5 S tau R hsetup h52a h52b h52c h52d h52e X tau1
      hIsoPair hVirtPair hagree
  simpa [X] using hsubsetX

public theorem not_conj_of_hypothesis_12_8_12_9_typeI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hTypeIL : Section8.typeIDefinitionData L H) :
    ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L := by
  rcases h128 with
    ⟨hp, _hbad, _hminp, _hMmax, hKMF, _hTypeIM, _hMsM, _hK', hquot, hP0⟩
  rcases h129 with
    ⟨_hP0comm, _hP0rank, _hLmax, hHMF, hMsL, hP0Ls, _hxL,
      ⟨_hp', hxOmega, hxne⟩, _hcentK, _hnorm, _hcentL⟩
  have hLs : Ls = H := by
    rcases hMsL with hEarly | hLate
    · exact hEarly.2
    · rcases hLate.1 with hIII | hIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) _hLmax hHMF hIII with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) _hLmax hHMF hIV with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hy, rfl⟩
    exact y.2
  have hP0ne : P0 ≠ ⊥ := by
    intro hbot
    have : x = 1 := by
      apply Subgroup.mem_bot.mp
      simpa [hbot] using hxP0
    exact hxne this
  have hpP0 : IsPGroup p P0 := by
    letI : Fact p.Prime := ⟨hp⟩
    rcases hP0 with ⟨P, hP0eq⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hp_dvd_P0 : p ∣ Nat.card P0 := by
    letI : Fact p.Prime := ⟨hp⟩
    rcases hpP0.exists_card_eq with ⟨n, hn⟩
    have hnpos : 0 < n := by
      rcases n with _ | n
      · simp only [pow_zero] at hn
        exact (hP0ne (Subgroup.card_eq_one.mp hn)).elim
      · omega
    rw [hn]
    rcases n with _ | n
    · omega
    · exact ⟨p ^ n, by rw [pow_succ']⟩
  have hp_dvd_H : p ∣ Nat.card H := by
    apply hp_dvd_P0.trans
    have hP0H : P0 ≤ H := by simpa [hLs] using hP0Ls
    have hdiv := Subgroup.card_subgroup_dvd_card (P0.subgroupOf H)
    rw [natCard_subgroupOf_eq P0 H hP0H] at hdiv
    exact hdiv
  have hp_not_dvd_K : ¬ p ∣ Nat.card K := by
    have hnot := theorem_12_9_prime_not_mem_subgroupPrimeSet_of_quotient_noncyclic
      M K p hp hKMF hquot
    intro hpK
    apply hnot
    dsimp [subgroupPrimeSet]
    apply Set.mem_setOf.mpr
    exact hpK
  rintro ⟨g, _hg, hML⟩
  have hKconjMF : section16MFSubgroup L (K.conjBy g) := by
    rw [hML]
    exact Section8.theorem_8_18_mfSubgroup_conjBy g hKMF
  have hKconj : K.conjBy g = H := section16MFSubgroup_unique hKconjMF hHMF
  apply hp_not_dvd_K
  rw [← section11_card_conjBy K g, hKconj]
  exact hp_dvd_H

set_option maxHeartbeats 800000
private theorem theorem_12_14_value_eq_projection
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (chi : Section1.ClassFunction L)
    (psi : Section1.ClassFunction G)
    (psirho : Section1.ClassFunction L)
    (x g : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psirho)
    (hxL : x ∈ L) (hgK : g ∈ K) :
    psi (x * g) = psirho ⟨x, hxL⟩ := by
  classical
  rcases h13 with
    ⟨h12L, _hcomp, _he, hchiS, _hdeg, h78pack, hnotpack,
      hExt, hpsi, hpsiclass, hrho⟩
  rcases hnotpack with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hMsLSource, hnotL⟩
  have hnotLcopy := hnotL
  rcases h128 with
    ⟨hp, _hbad, _hminp, hMmax, hKMF, hTypeIM, hMsM, _hK', hquot, hP0Sylow⟩
  rcases h129 with
    ⟨hP0comm, hP0rank, _hLmax, hHMF, hMsL, hP0Ls, _hxL,
      ⟨_hp', hxOmega, hxne⟩, _hcentK, hNxM, hCnotL⟩
  have hTypeIL : Section8.typeIDefinitionData L H := h12L.2.2.1
  have hLs : Ls = H := by
    rcases hMsL with hEarly | hLate
    · exact hEarly.2
    · rcases hLate.1 with hIII | hIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) h12L.1 hHMF hIII with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) h12L.1 hHMF hIV with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hy, rfl⟩
    exact y.2
  have hxH : x ∈ H := by
    rw [← hLs]
    exact hP0Ls hxP0
  have hnotconj :
      ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L :=
    not_conj_of_hypothesis_12_8_12_9_typeI
      M K K' P0 L H Ls x p
        ⟨hp, _hbad, _hminp, hMmax, hKMF, hTypeIM, hMsM, _hK', hquot,
          hP0Sylow⟩
        ⟨hP0comm, hP0rank, h12L.1, hHMF, hMsL, hP0Ls, hxL,
          ⟨_hp', hxOmega, hxne⟩, _hcentK, hNxM, hCnotL⟩ hTypeIL
  rcases exists_puncturedInducedFamily (K.subgroupOf M) with ⟨SM, hSM⟩
  have hnot10M : Section8.notation_8_10_source_data M K K
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K) :=
    notation_8_10_source_data_of_typeI_msChoice M K hMmax hKMF hTypeIM hMsM
  have hA1M : Section8.a1Set K ⊆ typeIASet M K := by
    simpa [Section8.a1Set] using
      nonidentity_kernel_subset_typeIASet M K (section16MFSubgroup_le hKMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      M K K (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      (typeIASet M K) inferInstance hnot10M (Or.inl rfl) hA1M with
    ⟨RM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have h815M : Section8.theorem_8_15_source_data M K K
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      (typeIASet M K) (Section8.section8DSet M (typeIASet M K))
      tildeAM tildeA0M tildeA1M RM :=
    ⟨hnot10M, hnotM, Or.inr (Or.inl rfl)⟩
  have h22M : Section2.Hypothesis2 (typeIASet M K) M RM :=
    Section8.theorem_8_15_hypothesis2 (inferInstance : IsMinCE G) h815M
  let tauM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G :=
    dadeTransformLinear RM h22M.subset_L
  have hDadeM : dadeIsometryRelativeToTypeIASet M K RM tauM := by
    simpa [tauM] using
      dadeIsometryRelativeToTypeIASet_of_hypothesis2 M K RM h22M
  have h12M : hypothesis_12_1_data M K SM RM tauM :=
    ⟨hMmax, hKMF, hTypeIM, hSM, hDadeM⟩
  rcases theorem_12_2_a M K SM RM tauM h12M with ⟨SXM, hdataM⟩
  rcases theorem_12_2_b M K SM SXM RM tauM h12M hdataM with
    ⟨R1M, RfunM, hRdataM, h52M⟩
  rcases theorem_12_2_a L H S R tau h12L with ⟨SXL, hdataL⟩
  rcases theorem_12_2_b L H S SXL R tau h12L hdataL with
    ⟨R1L, RfunL, hRdataL, h52L⟩
  have hsrcPair (chiM : Section1.ClassFunction M) :
      theorem_12_3_source_pair_data M K L H SM S tauM tau RM R
        chiM chi
        (Section8.section8DSet M (typeIASet M K))
        tildeAM tildeA0M tildeA1M DL tildeAL tildeA0L tildeA1L := by
    refine ⟨inferInstance, hMsM, hMsLSource, hnotM, hnotLcopy, ?_, ?_⟩
    · intro hchiM
      exact supportedOn_tau_sub_conjugate_tildeA1 h12M hnotM hchiM
    · intro _hchi
      exact supportedOn_tau_sub_conjugate_tildeA1 h12L hnotLcopy hchiS
  have horthFamilies (chiM : SM) :
      Section5.orthogonalFinsets (RfunM chiM) (RfunL ⟨chi, hchiS⟩) :=
    theorem_12_3 M K L H SM S tauM tau RM R SXM SXL R1M R1L
      RfunM RfunL (chiM : Section1.ClassFunction M) chi
      (Section8.section8DSet M (typeIASet M K))
      tildeAM tildeA0M tildeA1M DL tildeAL tildeA0L tildeA1L
      (hsrcPair chiM) h12M h12L hdataM hdataL hnotconj
      hRdataM h52M hRdataL h52L chiM.2 hchiS
  have hpsisubset :
      Section5.isSubsetSumOf (RfunL ⟨chi, hchiS⟩) psi := by
    rw [hpsi]
    exact coherentExtension_subsetSum_of_hypothesis52WithRData h52L hExt hchiS
  have horthM : orthogonalToAllR SM RfunM psi := by
    intro chiM alpha halpha
    rcases hpsisubset with ⟨F, hFsub, hpsiF⟩
    have hright : Section1.scalarProduct G alpha psi = 0 := by
      rw [hpsiF]
      have hsumF : F.sum (fun beta => beta) =
          (fun z : G => ∑ beta : F, (beta : Section1.ClassFunction G) z) := by
        ext z
        simpa using
          (Finset.sum_attach F fun beta : Section1.ClassFunction G => beta z).symm
      rw [hsumF, Section1.scalarProduct_fintype_sum_right]
      exact Finset.sum_eq_zero fun beta hbeta =>
        horthFamilies chiM halpha (hFsub beta.2)
    have hswap := Section1.scalarProduct_star_swap (G := G) alpha psi
    have hstarzero : star (Section1.scalarProduct G psi alpha) = 0 := by
      simpa [hright] using hswap
    simpa using congrArg star hstarzero
  have hxM : x ∈ M := by
    apply hNxM
    apply (centralizer_le_normalizer (Subgroup.zpowers x))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y * x = x * y := by
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, rfl⟩
      exact ((Commute.refl (x : G)).zpow_right k).symm
    exact this
  have hP0p : IsPGroup p P0 := by
    letI : Fact p.Prime := ⟨hp⟩
    rcases hP0Sylow with ⟨PM, hP0eq⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (PM : Subgroup M)) PM.isPGroup' M.subtype
  have hxK : x ∉ K := by
    intro hxK
    letI : Fact p.Prime := ⟨hp⟩
    have hpK := theorem_12_9_prime_not_mem_subgroupPrimeSet_of_quotient_noncyclic
      M K p hp hKMF hquot
    let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
    letI : IsElementaryAbelian p P1 := by
      simpa [P1] using
        (theorem_12_9_omega_one_noncyclic P0 p hp hP0p hP0comm hP0rank).1
    have hxpowP1 : (⟨x, by simpa [P1] using hxOmega⟩ : P1) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p P1) _
    have hxpow : x ^ p = 1 := congrArg Subtype.val hxpowP1
    have hxorder : orderOf x = p := orderOf_eq_prime hxpow hxne
    have hpCardK : p ∣ Nat.card K := by
      rw [← hxorder]
      exact Subgroup.orderOf_dvd_natCard K hxK
    apply hpK
    dsimp [subgroupPrimeSet]
    apply Set.mem_setOf.mpr
    exact hpCardK
  have hinputM : theorem_12_4_dade_induction_lemma_source_inputs M K SM RM tauM := by
    intro _hhyp
    exact ⟨inferInstance, hMsM, _, _, _, _, hnotM⟩
  have hcoset : constantOnRightCoset K psi x :=
    theorem_12_4 M K SM SXM RM R1M RfunM tauM psi x hinputM h12M
      hdataM hRdataM h52M hpsiclass horthM hxM hxK
  have hpsixg : psi (x * g) = psi x := hcoset ⟨g, hgK⟩
  rcases hnotL with
    ⟨_hA1L, _hAAL, hDL, _hRbotL, hUniqueL, hRsourceL,
      _htildeL, _htilde0L, _htilde1L⟩
  have hxA : x ∈ typeIASet L H :=
    ⟨hxL, hxne, x, hxH, hxne,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hCnotL' : ¬ Subgroup.centralizer ({x} : Set G) ≤ L := by
    simpa [elementCentralizerIn] using hCnotL
  have hxD : x ∈ DL := by
    rw [hDL]
    exact ⟨hxA, hCnotL'⟩
  have hC_le_N : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using
      (centralizer_le_normalizer (Subgroup.zpowers x))
  have hMcont : M ∈ section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({x} : Set G)) := ⟨hMmax, hC_le_N.trans hNxM⟩
  rcases hUniqueL x hxD with ⟨N, hNcont, hNuniq⟩
  have hNM : N = M := (hNuniq M hMcont).symm
  have hUniqueM : section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({x} : Set G)) = {M} := by
    ext Q
    constructor
    · intro hQ
      have hQN : Q = N := hNuniq Q hQ
      simp [hQN, hNM]
    · intro hQ
      have hQM : Q = M := by simpa using hQ
      simpa [hQM] using hMcont
  have hRx : R x = elementCentralizerIn K x :=
    hRsourceL x hxD M K hUniqueM hKMF
  have hRxK : R x ≤ K := by
    rw [hRx]
    exact fun _ hz => hz.1
  have hrhox : psirho ⟨x, hxL⟩ = psi x := by
    let xL : L := ⟨x, hxL⟩
    change psirho xL = psi x
    letI : Fintype (R (xL : G)) := Fintype.ofFinite _
    rw [hrho.2, Section7.dadeProjection, Section2.dadeAveragingFunction]
    have hRxK' : R (xL : G) ≤ K := by simpa [xL] using hRxK
    have hsum : (∑ z : R (xL : G), psi ((xL : G) * (z : G))) =
        (Nat.card (R (xL : G)) : ℂ) * psi x := by
      calc
        (∑ z : R (xL : G), psi ((xL : G) * (z : G))) =
            ∑ _z : R (xL : G), psi x := by
          apply Finset.sum_congr rfl
          intro z _hz
          simpa [xL] using hcoset ⟨(z : G), hRxK' z.2⟩
        _ = (Nat.card (R (xL : G)) : ℂ) * psi x := by
          simp [Finset.card_univ]
    rw [hsum]
    field_simp [show (Nat.card (R (xL : G)) : ℂ) ≠ 0 by
      exact_mod_cast (Nat.card_pos (α := R (xL : G))).ne']
  exact hpsixg.trans hrhox.symm

private theorem theorem_12_14_projection_eq_character
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (chi : Section1.ClassFunction L)
    (psi : Section1.ClassFunction G)
    (psirho : Section1.ClassFunction L)
    (x : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psirho)
    (hxL : x ∈ L) :
    psirho ⟨x, hxL⟩ = chi ⟨x, hxL⟩ := by
  classical
  rcases h13 with
    ⟨h12L, hcomp, he, hchiS, _hdeg, h78pack, _hnotpack,
      hExt, hpsi, hpsiclass, hrho⟩
  rcases h78pack with ⟨T, h76, hAgreeH, h78⟩
  have h12Lcopy := h12L
  rcases h12L with ⟨hLmax, hHMF, hTypeIL, hSL, hDadeL⟩
  rcases hDadeL with ⟨h22R, hALR, hTauR⟩
  have hAgreeR :
      Section7.agreesWithDadeTransform (typeIASet L H) L R tau :=
    ⟨hALR, hTauR⟩
  have h76R : Section7.hypothesis_7_6_statement
      (typeIASet L H) L H R T := by
    rcases h76 with ⟨hHL, hHnormal, _h22H, hAeq, hT⟩
    exact ⟨hHL, hHnormal, h22R, hAeq, hT⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    theorem_12_10 M K K' P0 L H Ls x p h128 h129
  have hrel : H.relIndex L = e := by
    have hHnormal : (H.subgroupOf L).Normal :=
      section16MFSubgroup_subgroupOf_normal hHMF
    have hlocal :
        (H.subgroupOf L).IsComplement' (E.subgroupOf L) :=
      section12ComplementIn_left_normal_isComplement' hcomp hHnormal
    rw [Subgroup.relIndex, hlocal.symm.index_eq_card,
      natCard_subgroupOf_eq E L hcomp.2.1, he]
  rcases Section7.theorem_7_8_a
      (typeIASet L H) L H R T S tau tau1 chi
      h76 hAgreeH h78 with ⟨a, r, hdecomp⟩
  have hdecompCopy := hdecomp
  rcases hdecomp with ⟨hpImg, hrImg, hrp, hbetaRaw⟩
  let beta : Section1.ClassFunction G :=
    Section7.theorem_7_8_beta L H tau chi
  let principal : Section1.ClassFunction G := Section1.principalCharacter G
  let gamma : Section1.ClassFunction G := tau1 chi
  let W : Section1.ClassFunction G :=
    Section7.theorem_7_8_weightedSum S tau1 (H.relIndex L)
  let component : Section1.ClassFunction G :=
    principal - gamma + (a : ℂ) • W
  have hbetaEq : beta = component + r := by
    simpa [beta, component, principal, gamma, W, add_assoc] using hbetaRaw
  have hrGamma : Section1.scalarProduct G r gamma = 0 := by
    simpa [gamma] using hrImg chi hchiS
  have hGammaR : Section1.scalarProduct G gamma r = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) r gamma
    have hstarzero : star (Section1.scalarProduct G gamma r) = 0 := by
      simpa [hrGamma] using hswap
    simpa using congrArg star hstarzero
  have hrW : Section1.scalarProduct G r W = 0 := by
    have hsum : W =
        fun g => ∑ phi : S,
          ((((phi : Section1.ClassFunction L) 1) /
            ((H.relIndex L : ℂ) *
              (Section5.cfNormSq (phi : Section1.ClassFunction L) : ℂ))) •
                tau1 (phi : Section1.ClassFunction L)) g := by
      ext g
      simp only [W, Section7.theorem_7_8_weightedSum, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact (Finset.sum_attach S
        (fun phi : Section1.ClassFunction L =>
          phi 1 / ((H.relIndex L : ℂ) * (Section5.cfNormSq phi : ℂ)) *
            tau1 phi g)).symm
    rw [hsum, Section1.scalarProduct_fintype_sum_right]
    exact Finset.sum_eq_zero fun phi _hphi => by
      rw [Section1.scalarProduct_smul_right, hrImg phi phi.2]
      simp
  have hWr : Section1.scalarProduct G W r = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) W r
    have hstarzero : star (Section1.scalarProduct G r W) = 0 := by
      simp [hrW]
    exact hswap.symm.trans hstarzero
  have hPrincipalR : Section1.scalarProduct G principal r = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) principal r
    have hstarzero : star (Section1.scalarProduct G r principal) = 0 := by
      simp [principal, hrp]
    exact hswap.symm.trans hstarzero
  have hcomponentR : Section1.scalarProduct G component r = 0 := by
    dsimp [component, principal, gamma, W]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      Section1.scalarProduct_smul_left]
    rw [hPrincipalR, hGammaR, hWr]
    simp
  have hrComponent : Section1.scalarProduct G r component = 0 := by
    dsimp [component, principal, gamma, W]
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      Section1.scalarProduct_smul_right]
    rw [hrp, hrGamma, hrW]
    simp
  let q : ℝ :=
    (1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
        (a : ℝ)^2 -
      2 * (1 / (Nat.card H : ℝ)) * (a : ℝ)
  have hbetaNorm :
      Section5.cfNormSq beta = (H.relIndex L : ℝ) + 1 := by
    simpa [beta] using Section7.theorem_7_8_beta_norm h76 hAgreeH h78
  have hWnorm :
      Section5.cfNormSq W =
        ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
    have hdegreeSum := Section7.theorem_7_8_b_degree_sum_identity h76 h78
    simpa [W] using
      Section7.theorem_7_8_b_weightedSum_norm_of_degree_sum
        (A := typeIASet L H) (L := L) (H := H) (T := T) (S := S)
        (τ := tau) (ν := tau1) (ζ := chi) h76 h78 hdegreeSum
  have hcomponentNorm :
      Section5.cfNormSq component = 2 + (Nat.card H : ℝ) * q := by
    simpa [component, principal, gamma, W, q] using
      Section7.theorem_7_8_b_component_norm_of_weightedSum_norm
        (A := typeIASet L H) (L := L) (H := H) (T := T) (S := S)
        (τ := tau) (ν := tau1) (ζ := chi) h76 h78 hpImg a hWnorm
  have hrNorm :
      Section5.cfNormSq r =
        (H.relIndex L : ℝ) - 1 - (Nat.card H : ℝ) * q := by
    have hnorm :=
      Section7.theorem_7_8_b_remainder_norm_of_orthogonal_decomposition
        (G := G) (β := beta) (c := component) (r := r)
        (target := (H.relIndex L : ℝ) + 1)
        (component := 2 + (Nat.card H : ℝ) * q)
        hbetaEq hcomponentR hrComponent hbetaNorm hcomponentNorm
    nlinarith
  rcases h128 with
    ⟨hp, hbad, hminp, hMmax, hKMF, hTypeIM, hMsM, hK', hquot, hP0Sylow⟩
  rcases h129 with
    ⟨hP0comm, hP0rank, _hLmax, _hHMF, hMsL, hP0Ls, _hxL,
      ⟨_hp', hxOmega, hxne⟩, hcentK, hNxM, hCnotL⟩
  have hLs : Ls = H := by
    rcases hMsL with hEarly | hLate
    · exact hEarly.2
    · rcases hLate.1 with hIII | hIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) hLmax hHMF hIII with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) hLmax hHMF hIV with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIL)
  have hP0p : IsPGroup p P0 := by
    letI : Fact p.Prime := ⟨hp⟩
    rcases hP0Sylow with ⟨PM, hP0eq⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (PM : Subgroup M)) PM.isPGroup' M.subtype
  let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
  have hP1card : Nat.card P1 = p ^ 2 := by
    letI : Fact p.Prime := ⟨hp⟩
    letI : IsMulCommutative P0 := hP0comm
    letI : Fact (IsPGroup p P0) := ⟨hP0p⟩
    have hgen : generatorRank P0 = 2 := by
      apply le_antisymm
      · exact
          (generatorRank_le_groupRank_of_commutative_pgroup (p := p) P0).trans_eq
            hP0rank
      · rw [← hP0rank]
        exact groupRank_le_generatorRank_of_commutative_pgroup hP0p hP0comm
    calc
      Nat.card P1 = Nat.card (omega₁ (G := P0) (p := p)) := by
        exact Subgroup.card_map_of_injective
          (K := omega₁ (G := P0) (p := p)) (f := P0.subtype)
          P0.subtype_injective
      _ = p ^ generatorRank P0 :=
        omega₁_card_eq_pow_generatorRank_of_commutative_pgroup (p := p) P0
      _ = p ^ 2 := by rw [hgen]
  have hP1H : P1 ≤ H := by
    intro y hy
    rw [← hLs]
    apply hP0Ls
    change y ∈ (omega₁ (G := P0) (p := p)).map P0.subtype at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact z.2
  have hpSqLeH : p ^ 2 ≤ Nat.card H := by
    have hcardLe := Subgroup.card_le_card_group (P1.subgroupOf H)
    rw [natCard_subgroupOf_eq P1 H hP1H, hP1card] at hcardLe
    exact hcardLe
  have hpDvdG : p ∣ Nat.card G := by
    apply (dvd_pow_self p (by decide : 2 ≠ 0)).trans
    rw [← hP1card]
    exact Subgroup.card_subgroup_dvd_card P1
  have hpNeTwo : p ≠ 2 :=
    Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpDvdG
  have hpOdd : Odd p := hp.odd_of_ne_two hpNeTwo
  have hpThree : 3 ≤ p := by
    have hpTwo := hp.two_le
    omega
  have heOdd : Odd e := by
    rw [he]
    exact odd_of_card_dvd IsMinCE.odd_order
      (Subgroup.card_subgroup_dvd_card E)
  have hEdiv :=
    (theorem_12_12 M K K' P0 L H Ls E x p e
      ⟨hp, hbad, hminp, hMmax, hKMF, hTypeIM, hMsM, hK', hquot, hP0Sylow⟩
      ⟨hP0comm, hP0rank, hLmax, hHMF, hMsL, hP0Ls, hxL,
        ⟨_hp', hxOmega, hxne⟩, hcentK, hNxM, hCnotL⟩
      hfrob hcomp he).2
  have hTwoE : 2 * e ≤ p + 1 := by
    rcases hEdiv with hminus | hplus
    · rcases hminus with ⟨k, hk⟩
      have hkEven : Even k := by
        rw [← Nat.not_odd_iff_even]
        intro hkOdd
        have hprodOdd : Odd (e * k) := Nat.odd_mul.mpr ⟨heOdd, hkOdd⟩
        rw [← hk] at hprodOdd
        have hpMinusEven : Even (p - 1) :=
          (Nat.even_sub' hp.one_le).2 (by simp [hpOdd])
        exact (Nat.not_even_iff_odd.mpr hprodOdd)
          hpMinusEven
      rcases hkEven with ⟨t, ht⟩
      have hdiv : 2 * e ∣ p - 1 := by
        refine ⟨t, ?_⟩
        rw [hk, ht]
        ring
      exact (Nat.le_of_dvd (by omega) hdiv).trans (by omega)
    · rcases hplus with ⟨k, hk⟩
      have hkEven : Even k := by
        rw [← Nat.not_odd_iff_even]
        intro hkOdd
        have hprodOdd : Odd (e * k) := Nat.odd_mul.mpr ⟨heOdd, hkOdd⟩
        rw [← hk] at hprodOdd
        exact (Nat.not_even_iff_odd.mpr hprodOdd) hpOdd.add_one
      rcases hkEven with ⟨t, ht⟩
      apply Nat.le_of_dvd (Nat.succ_pos p)
      refine ⟨t, ?_⟩
      calc
        p + 1 = e * k := hk
        _ = e * (t + t) := by rw [ht]
        _ = 2 * e * t := by ring
  have haZero : a = 0 := by
    have hePos : 0 < e := by rw [he]; exact Nat.card_pos
    have hhPos : 0 < Nat.card H := Nat.card_pos
    have heR : 0 < (e : ℝ) := by exact_mod_cast hePos
    have hhR : 0 < (Nat.card H : ℝ) := by exact_mod_cast hhPos
    have hnonneg : 0 ≤ Section5.cfNormSq r := Section5.cfNormSq_nonneg r
    have hqBound : (Nat.card H : ℝ) * q ≤ (e : ℝ) - 1 := by
      rw [hrel] at hrNorm
      nlinarith
    have hqExpand :
        (Nat.card H : ℝ) * q =
          (((Nat.card H : ℝ) - 1) / (e : ℝ)) * (a : ℝ)^2 -
            2 * (a : ℝ) := by
      dsimp [q]
      rw [hrel]
      field_simp [heR.ne', hhR.ne']
    rw [hqExpand] at hqBound
    have hscaled := mul_le_mul_of_nonneg_left hqBound heR.le
    have hub :
        ((Nat.card H : ℝ) - 1) * (a : ℝ)^2 -
            2 * (e : ℝ) * (a : ℝ) ≤
          (e : ℝ) * ((e : ℝ) - 1) := by
      have htemp : (e : ℝ) * ((((Nat.card H : ℝ) - 1) / (e : ℝ)) * (a : ℝ)^2 - 2 * (a : ℝ)) =
          ((Nat.card H : ℝ) - 1) * (a : ℝ)^2 - 2 * (e : ℝ) * (a : ℝ) := by
        field_simp [heR.ne']
      rw [htemp] at hscaled
      exact hscaled
    by_contra haNe
    have haCases : (a : ℝ) ≤ -1 ∨ 1 ≤ (a : ℝ) := by
      have : a ≤ -1 ∨ 1 ≤ a := by omega
      exact this.elim (fun h => Or.inl (by exact_mod_cast h))
        (fun h => Or.inr (by exact_mod_cast h))
    have hHminus : 0 ≤ (Nat.card H : ℝ) - 1 := by
      have : (1 : ℝ) ≤ Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
      nlinarith
    have hbase :
        (Nat.card H : ℝ) - 1 - 2 * (e : ℝ) ≤
          ((Nat.card H : ℝ) - 1) * (a : ℝ)^2 -
            2 * (e : ℝ) * (a : ℝ) := by
      rcases haCases with haNeg | haPos
      · have haSq : (1 : ℝ) ≤ (a : ℝ)^2 := by nlinarith [sq_nonneg ((a : ℝ) + 1)]
        have hsqTerm := mul_le_mul_of_nonneg_left haSq hHminus
        have hlinear : -2 * (e : ℝ) ≤ -2 * (e : ℝ) * (a : ℝ) := by
          nlinarith [mul_nonneg heR.le (show 0 ≤ -(a : ℝ) - 1 by nlinarith)]
        nlinarith
      · have haSq : (a : ℝ) ≤ (a : ℝ)^2 := by
          nlinarith [sq_nonneg ((a : ℝ) - 1)]
        have hsqTerm := mul_le_mul_of_nonneg_left haSq hHminus
        have hcoef : 0 ≤ (Nat.card H : ℝ) - 1 - 2 * (e : ℝ) := by
          have hpSqR : (p : ℝ)^2 ≤ (Nat.card H : ℝ) := by
            exact_mod_cast hpSqLeH
          have hTwoER : 2 * (e : ℝ) ≤ (p : ℝ) + 1 := by
            exact_mod_cast hTwoE
          have hpThreeR : (3 : ℝ) ≤ p := by exact_mod_cast hpThree
          nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) - 3 by nlinarith)
            (show 0 ≤ (p : ℝ) + 1 by nlinarith)]
        have hlinear := mul_le_mul_of_nonneg_left haPos hcoef
        nlinarith
    have hmain :
        (Nat.card H : ℝ) - 1 - 2 * (e : ℝ) ≤
          (e : ℝ) * ((e : ℝ) - 1) := hbase.trans hub
    have hpSqR : (p : ℝ)^2 ≤ (Nat.card H : ℝ) := by
      exact_mod_cast hpSqLeH
    have hTwoER : 2 * (e : ℝ) ≤ (p : ℝ) + 1 := by
      exact_mod_cast hTwoE
    have hpThreeR : (3 : ℝ) ≤ p := by exact_mod_cast hpThree
    have hprod :
        0 ≤ ((p : ℝ) + 1 - 2 * (e : ℝ)) *
          ((p : ℝ) + 1 + 2 * (e : ℝ)) :=
      mul_nonneg (by nlinarith) (by positivity)
    have hpoly :
        0 ≤ ((p : ℝ) - 3) * (3 * (p : ℝ) + 5) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    nlinarith
  rcases Section7.theorem_7_8_b_markedProjectionData_source_bridge
      (A := typeIASet L H) (L := L) (H := H) (K := R)
      (T := T) (S := S) (τ := tau) (ν := tau1) (ζ := chi)
      (a := a) (r := r) h76 hAgreeH h78 hdecompCopy with
    ⟨n, eta, d, c, ibeta, izeta, henum, hbasis, hcoeff,
      hibetazeta, hibeta, hizeta, hc⟩
  have hchiNorm : Section5.cfNormSq chi = 1 := by
    unfold Section5.cfNormSq
    rw [Section1.scalarProduct_irreducibleCharacter_self h78.2.2.2.2.2.2.1]
    simp
  have hsum :
      (∑ i : Fin n,
        (star (c i) /
          (Section5.cfNormSq (eta (Fin.succ i)) : ℂ)) *
            eta (Fin.succ i) ⟨x, hxL⟩) = chi ⟨x, hxL⟩ := by
    rw [Finset.sum_eq_single izeta]
    · rw [hc izeta, hizeta]
      simp [hibetazeta.symm, hchiNorm]
    · intro i _hi hine
      rw [hc i]
      simp [hine, haZero]
    · simp
  have hxH : x ∈ H := by
    rw [← hLs]
    apply hP0Ls
    change x ∈ (omega₁ (G := P0) (p := p)).map P0.subtype at hxOmega
    rcases hxOmega with ⟨z, hz, hzx⟩
    rw [← hzx]
    exact z.2
  have hxA : x ∈ typeIASet L H :=
    ⟨hxL, hxne, x, hxH, hxne,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcoeffPsi : Section7.projectionCoefficientPackage eta d tau psi c := by
    simpa [hpsi] using hcoeff
  have hprojection :=
    Section7.theorem_7_7 (typeIASet L H) L H R T eta d tau psi c
      h76R hAgreeR henum hbasis hpsiclass hcoeffPsi
  rw [hrho.2]
  exact (hprojection.1 ⟨x, hxL⟩ hxA).trans hsum


/-- Source leaf for PF `(12.14)`: the character-value comparison at `x * g`
from the `(12.9)` element, the `(12.13)` notation, and `g ∈ K`. -/
public theorem theorem_12_14_source_leaf
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (x g : G) (p : ℕ) :
    theorem_12_14_source_data M K K' P0 L H Ls E e S R τ τ₁ χ ψ ψρ x g p := by
  intro h128 h129 h13 hxL hgK
  exact ⟨
    theorem_12_14_value_eq_projection M K K' P0 L H Ls E e S R τ τ₁ χ ψ ψρ
      x g p h128 h129 h13 hxL hgK,
    theorem_12_14_projection_eq_character M K K' P0 L H Ls E e S R τ τ₁ χ ψ ψρ
      x p h128 h129 h13 hxL⟩

/-- Peterfalvi `(12.14)`.

Let `x` be as in `(12.9)`.  If `g ∈ K`, then
`ψ (x * g) = ψρ ⟨x, hxL⟩ = χ ⟨x, hxL⟩`. -/
public theorem theorem_12_14
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (x g : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ)
    (hxL : x ∈ L)
    (hgK : g ∈ K) :
    ψ (x * g) = ψρ ⟨x, hxL⟩ ∧
      ψρ ⟨x, hxL⟩ = χ ⟨x, hxL⟩ := by
  exact theorem_12_14_of_source_data M K K' P0 L H Ls E e S R τ τ₁ χ ψ ψρ x g p
    (theorem_12_14_source_leaf M K K' P0 L H Ls E e S R τ τ₁ χ ψ ψρ x g p)
    h128 h129 h13 hxL hgK

end CFSG.Section12
