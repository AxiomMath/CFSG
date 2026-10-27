module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
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
# Peterfalvi, Section 12: Theorem (12.6)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v
open Section1 Section2 Section3 Section4

/-! ## (12.6) -/

/-- Hypothesis `(12.1)` gives the Section 6 induced-kernel family with
kernel `⊥` for the subgroup `H` of `L`. -/
public theorem theorem_12_6_inducedKernelFamily_bot_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ) :
    Section6.inducedKernelFamily (H.subgroupOf L) ⊥ S := by
  classical
  rcases h12_1 with ⟨_hmax, _hMF, _hTypeI, hS, _hτ⟩
  refine ⟨bot_le, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
    refine ⟨θ, hθirr, ?_, hθne, hχeq⟩
    intro a
    have ha_one : (a : H.subgroupOf L) = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp a.property
    simp [ha_one, Section1.degree]
  · intro hχ
    rcases hχ with ⟨θ, hθirr, _hθker, hθne, hχeq⟩
    exact (hS χ).mpr ⟨θ, hθirr, hθne, hχeq⟩

/-- First source step in Peterfalvi `(12.6)`.

Under Hypothesis `(12.1)`, if `L` is Frobenius with kernel `H`, then the
punctured induced family `S` consists of irreducible characters.  This is the
formal placeholder for the invocation of Isaacs, Theorem 6.34, in the source
proof. -/
public theorem theorem_12_6_irreducible_of_frobenius
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup χ := by
  classical
  have hSbot :
      Section6.inducedKernelFamily (H.subgroupOf L) ⊥ S :=
    theorem_12_6_inducedKernelFamily_bot_of_hypothesis12 L H S R τ h12_1
  rcases hfrob with ⟨_hHL, hHnorm, _Rcomp, hcomp, _hHne, _hRne, hcent⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  exact Section6.theorem_6_8_inducedKernelFamily_irreducible_of_frobenius_complement
    hSbot hcomp hcent

/-- In the TI branch of PF `(12.6)`, the punctured image of `H` in `G` is a
TI-subset with normalizer `L`, in the Section 2 form needed by PF `(6.8)`. -/
public theorem theorem_12_6_isTISubsetWithNormalizer_subgroupImagePuncturedSet
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H : Subgroup G)
    (hmax : L ∈ section9MaximalSubgroups G)
    (hHL : H ≤ L)
    (hHnorm : (H.subgroupOf L).Normal)
    (hHne : H.subgroupOf L ≠ ⊥)
    (hTI : section16TISubset (section16NonidentityElements (H : Set G))) :
    Section2.IsTISubsetWithNormalizer
      (Section6.subgroupImagePuncturedSet L (H.subgroupOf L)) L := by
  classical
  have hHneAmbient : H ≠ (⊥ : Subgroup G) := by
    intro hHbot
    apply hHne
    ext x
    constructor
    · intro hx
      have hxG : (x : G) ∈ H := hx
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hHbot] using hxG
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxBot))
    · intro hx
      have hxone : x = 1 := Subgroup.mem_bot.mp hx
      simp [hxone]
  have hLmax8 : L ∈ section8MaximalSubgroups G :=
    section8_maximal_of_section9_maximal (G := G) hmax
  have hNormH : Subgroup.normalizer ((H : Set G)) = L :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      (G := G) hLmax8 hHL hHneAmbient hHnorm
  have hHmap : (H.subgroupOf L).map L.subtype = H := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyH, hyx⟩
      have hyH' : ((y : L) : G) ∈ H := Subgroup.mem_subgroupOf.mp hyH
      simpa [← hyx] using hyH'
    · intro hx
      exact ⟨⟨x, hHL hx⟩, hx, rfl⟩
  have hAeq :
      Section6.subgroupImagePuncturedSet L (H.subgroupOf L) =
        section16NonidentityElements (H : Set G) := by
    rw [Section6.theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured, hHmap]
    ext x
    rfl
  have hHsharpNonempty :
      (section16NonidentityElements (H : Set G)).Nonempty := by
    by_contra hEmpty
    apply hHneAmbient
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxH
    by_contra hxne
    exact hEmpty ⟨x, ⟨hxH, hxne⟩⟩
  refine ⟨?hne, ?hpunct, ?hTIsection2, ?hnorm⟩
  · rcases hHsharpNonempty with ⟨x, hx⟩
    exact ⟨x, by simpa [hAeq] using hx⟩
  · intro a ha
    have haSharp : a ∈ section16NonidentityElements (H : Set G) := by
      simpa [hAeq] using ha
    exact haSharp.2
  · intro g hg
    have hg16 :
        (section16NonidentityElements (H : Set G) ∩
            section16ConjugateSet (section16NonidentityElements (H : Set G)) g).Nonempty := by
      rcases hg with ⟨x, hxA, hxConj⟩
      refine ⟨x, ?_⟩
      constructor
      · simpa [hAeq] using hxA
      · rcases hxConj with ⟨y, hyA, hyx⟩
        exact ⟨y, by simpa [hAeq] using hyA, by simpa [Section2.conjBy] using hyx⟩
    rcases hTI g with hEq | hSub
    · change Section2.normalizesSet
        (Section6.subgroupImagePuncturedSet L (H.subgroupOf L)) g
      intro x
      rw [hAeq, Section2.conjBy]
      constructor
      · intro hx
        have hxConj :
            g * x * g⁻¹ ∈ section16ConjugateSet
              (section16NonidentityElements (H : Set G)) g := by
          simpa [hEq] using hx
        rcases hxConj with ⟨y, hySharp, hyx⟩
        have hxy : x = y := by
          have h := congrArg (fun z : G => g⁻¹ * z * g) hyx
          simpa [mul_assoc] using h
        simpa [hxy] using hySharp
      · intro hx
        have hxConj :
            g * x * g⁻¹ ∈
              section16ConjugateSet (section16NonidentityElements (H : Set G)) g :=
          ⟨x, hx, rfl⟩
        simpa [hEq] using hxConj
    · exfalso
      rcases hg16 with ⟨x, hx⟩
      have hxone : x = 1 := hSub hx
      exact hx.1.2 hxone
  · calc
      Section2.setNormalizer (Section6.subgroupImagePuncturedSet L (H.subgroupOf L))
          = Subgroup.normalizer (((H.subgroupOf L).map L.subtype : Subgroup G) : Set G) := by
            rw [Section6.theorem_6_8_normalizer_map_subtype_eq_setNormalizer_punctured]
      _ = Subgroup.normalizer ((H : Set G)) := by rw [hHmap]
      _ = L := hNormH

/-- On the `H#` support in the TI branch, the Section 12 Dade transform agrees
with ordinary induction from `L` to `G`, as required by PF `(6.8)`. -/
public theorem theorem_12_6_transformAgreesWithInductionOn_of_TI
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    [hHnormal : (H.subgroupOf L).Normal]
    (hSbot : Section6.inducedKernelFamily (H.subgroupOf L) ⊥ S)
    (hτ : dadeIsometryRelativeToTypeIASet L H R τ)
    (hTI :
      Section2.IsTISubsetWithNormalizer
        (Section6.subgroupImagePuncturedSet L (H.subgroupOf L)) L) :
    Section6.transformAgreesWithInductionOn L S τ := by
  classical
  intro χ hχ
  rcases hτ with ⟨h22, hτdef⟩
  rcases hτdef with ⟨hAL, hτeq⟩
  let Aimg : Set G := Section6.subgroupImagePuncturedSet L (H.subgroupOf L)
  have hAimgA : Aimg ⊆ typeIASet L H := by
    intro a ha
    rcases ha with ⟨h, hha, hhne⟩
    have haH : a ∈ H := by
      rw [← hha]
      exact Subgroup.mem_subgroupOf.mp h.property
    have haL : a ∈ L := by
      rw [← hha]
      exact (h : L).property
    have hane : a ≠ 1 := by
      intro ha1
      exact hhne (Subtype.ext (by simp [hha, ha1]))
    refine ⟨haL, hane, a, haH, hane, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    simp
  have hχAimg : Section2.CFOn L Aimg χ := by
    simpa [Aimg] using
      Section6.theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
        (L := L) (H := H.subgroupOf L) hSbot hχ
  have hχA : Section2.CFOn L (typeIASet L H) χ := CFOn_mono hAimgA hχAimg
  have hHyp2triv : Section2.Hypothesis2 Aimg L (fun _ : G => ⊥) := by
    simpa [Aimg] using (Section2.proposition_2_3 Aimg L hTI.1).mp hTI
  have hconst :
      ∀ ψ : Theory.Character.ConjClassFunction G,
        Theory.Character.IsIrreducibleConjCharacter ψ →
          ∀ ⦃a h0 : G⦄, a ∈ Aimg → h0 ∈ R a →
            Section1.ofConjClassFunction ψ (a * h0) =
              Section1.ofConjClassFunction ψ a := by
    intro ψ _hψ a h0 ha hh0
    have hcent_le_L : Section2.elementCentralizer a ≤ L := by
      intro c hc
      have hprod0 := hHyp2triv.centralizer_eq_product ha
      rcases hprod0.mul_surjective c hc with ⟨z, hz, k, hk, hck⟩
      have hz1 : z = 1 := by simpa using hz
      subst z
      have hkL : k ∈ L := (Subgroup.mem_inf.mp hk).1
      simpa [hck] using hkL
    have hprod := h22.centralizer_eq_product (hAimgA ha)
    have hRa_bot : R a = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxR
      have hxCent : x ∈ Section2.elementCentralizer a := hprod.left_le hxR
      have hxL : x ∈ L := hcent_le_L hxCent
      have hxInf : x ∈ R a ⊓ Section2.centralizerIn L a :=
        ⟨hxR, ⟨hxL, hxCent⟩⟩
      simpa [hprod.inf_eq_bot] using hxInf
    have hh0bot : h0 ∈ (⊥ : Subgroup G) := by
      simpa [hRa_bot] using hh0
    have hh0one : h0 = 1 := Subgroup.mem_bot.mp hh0bot
    simp [hh0one]
  have hdade :
      Section2.dadeTransform R hAL χ = Section1.inducedCF L χ :=
    dadeTransform_eq_inducedCF_of_irreducible_dade_coset_constancy_on_support
      (typeIASet L H) Aimg L R hAimgA h22 hAL χ hχAimg hconst
  calc
    τ χ = Section2.dadeTransform R hAL χ := hτeq χ hχA
    _ = Section1.inducedCF L χ := hdade

/-- The Section 6 `(6.8)` hypothesis package for the TI branch of Peterfalvi
`(12.6)`.

This is the adapter whose proof supplies the textbook sentence: when `H#` is a
TI-subset of the ambient group, the data of Hypothesis `(12.1)` and the
Frobenius-kernel hypothesis satisfy the hypotheses of PF `(6.8)`. -/
public theorem theorem_12_6_theorem_6_8_hypothesis_of_TI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hTI : section16TISubset (section16NonidentityElements (H : Set G))) :
    ∃ W1 W2 W : Subgroup L,
      Section6.theorem_6_8_hypothesis
        L (H.subgroupOf L) W1 W2 W S τ := by
  classical
  rcases h12_1 with ⟨hmax, hMF, hTypeI, hS, hτ⟩
  rcases hMF.1 with ⟨hHL, hHnorm, hHnil, _hHall⟩
  rcases hfrob with ⟨_hHLf, hHnormf, Rcomp, hcomp, hHne, hRne, hcent⟩
  have h12_1' : hypothesis_12_1_data L H S R τ :=
    ⟨hmax, hMF, hTypeI, hS, hτ⟩
  haveI : (H.subgroupOf L).Normal := hHnormf
  refine ⟨Rcomp, ⊥, ⊥, ?_⟩
  refine ⟨?hsemi, ?hodd, hHne, ?hnil, ?hTI68, ?hSbot, ?hTind, Or.inl ?hfrob6⟩
  · exact
      Section6.theorem_6_8_internalSemidirectProduct_top_of_normal_isComplement'
        hcomp
  · exact odd_card_of_typeIDefinitionData L H hTypeI
  · exact Group.nilpotent_of_mulEquiv (G := H) (G' := H.subgroupOf L)
      (Subgroup.subgroupOfEquivOfLe hHL).symm
  · exact theorem_12_6_isTISubsetWithNormalizer_subgroupImagePuncturedSet
      L H hmax hHL hHnorm hHne hTI
  · exact theorem_12_6_inducedKernelFamily_bot_of_hypothesis12 L H S R τ h12_1'
  · exact theorem_12_6_transformAgreesWithInductionOn_of_TI L H S R τ
      (theorem_12_6_inducedKernelFamily_bot_of_hypothesis12 L H S R τ h12_1')
      hτ
      (theorem_12_6_isTISubsetWithNormalizer_subgroupImagePuncturedSet
        L H hmax hHL hHnorm hHne hTI)
  · let Rtop : Subgroup (⊤ : Subgroup L) :=
      Rcomp.subgroupOf (⊤ : Subgroup L)
    have hKneTop :
        (H.subgroupOf L).subgroupOf (⊤ : Subgroup L) ≠ ⊥ := by
      intro hbot
      apply hHne
      ext x
      constructor
      · intro hx
        have hxTop :
            (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
              (H.subgroupOf L).subgroupOf (⊤ : Subgroup L) := hx
        have hxBotTop :
            (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
              (⊥ : Subgroup (⊤ : Subgroup L)) := by
          simpa [hbot] using hxTop
        have hxEq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = 1 :=
          Subgroup.mem_bot.mp hxBotTop
        exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hxEq)
      · intro hx
        have hxEq : x = 1 := Subgroup.mem_bot.mp hx
        simp [hxEq]
    have hRneTop : Rtop ≠ ⊥ := by
      intro hbot
      apply hRne
      ext x
      constructor
      · intro hx
        have hxTop :
            (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈ Rtop := hx
        have hxBotTop :
            (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
              (⊥ : Subgroup (⊤ : Subgroup L)) := by
          simpa [hbot] using hxTop
        have hxEq : (⟨x, trivial⟩ : (⊤ : Subgroup L)) = 1 :=
          Subgroup.mem_bot.mp hxBotTop
        exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hxEq)
      · intro hx
        have hxEq : x = 1 := Subgroup.mem_bot.mp hx
        simp [hxEq]
    have hcompTop :
        ((H.subgroupOf L).subgroupOf (⊤ : Subgroup L)).IsComplement' Rtop := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [Subgroup.disjoint_def]
        intro x hxH hxR
        apply Subtype.ext
        have hxHL : (x : L) ∈ H.subgroupOf L := hxH
        have hxRL : (x : L) ∈ Rcomp := hxR
        have hxBot : (x : L) ∈ (⊥ : Subgroup L) :=
          (Subgroup.disjoint_def.mp hcomp.disjoint) hxHL hxRL
        simpa using Subgroup.mem_bot.mp hxBot
      · rw [Set.eq_univ_iff_forall]
        intro x
        rcases hcomp.2 (x : L) with ⟨⟨⟨h, hhH⟩, ⟨r, hrR⟩⟩, hprod⟩
        refine ⟨⟨h, trivial⟩, hhH, ⟨r, trivial⟩, hrR, ?_⟩
        apply Subtype.ext
        exact hprod
    have hcentTop :
        ∀ r : Rtop, r ≠ 1 →
          Section2.centralizerIn
              ((H.subgroupOf L).subgroupOf (⊤ : Subgroup L)) (r : (⊤ : Subgroup L)) =
            ⊥ := by
      intro r hrne
      let r0 : Rcomp := ⟨((r : (⊤ : Subgroup L)) : L), r.property⟩
      have hr0ne : r0 ≠ 1 := by
        intro hr0
        apply hrne
        apply Subtype.ext
        apply Subtype.ext
        simpa [r0] using congrArg Subtype.val hr0
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxcommTop :
          x * (r : (⊤ : Subgroup L)) =
            (r : (⊤ : Subgroup L)) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hxcommL :
          ((x : (⊤ : Subgroup L)) : L) * ((r : (⊤ : Subgroup L)) : L) =
            ((r : (⊤ : Subgroup L)) : L) * ((x : (⊤ : Subgroup L)) : L) :=
        congrArg Subtype.val hxcommTop
      have hxL :
          ((x : (⊤ : Subgroup L)) : L) ∈
            Section2.centralizerIn (H.subgroupOf L) (r0 : L) := by
        constructor
        · exact hx.1
        · change ((x : (⊤ : Subgroup L)) : L) ∈ Section2.elementCentralizer (r0 : L)
          rw [Section2.elementCentralizer]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [r0] using hxcommL)
      have hxBotL : ((x : (⊤ : Subgroup L)) : L) ∈ (⊥ : Subgroup L) := by
        simpa [hcent r0 hr0ne] using hxL
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxBotL))
    exact
      ⟨le_top,
        Section6.theorem_6_8_subgroupOf_top_normal_of_normal (Z := H.subgroupOf L),
        Rtop, hcompTop, hKneTop, hRneTop, hcentTop⟩

/-- The TI branch in the proof of Peterfalvi `(12.6)`: if `H#` is a
TI-subset of `G`, then PF `(6.8)` gives coherence of `S`. -/
public theorem theorem_12_6_coherent_of_TI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hTI : section16TISubset (section16NonidentityElements (H : Set G))) :
    Section6.coherentFamily S τ := by
  rcases theorem_12_6_theorem_6_8_hypothesis_of_TI
      L H S R τ h12_1 hfrob hTI with
    ⟨W1, W2, W, h68⟩
  exact Section6.theorem_6_8 L (H.subgroupOf L) W1 W2 W S τ h68

/-- In the rank-two Type-I branch of PF `(12.6)`, all characters in the
punctured induced family have the same degree. -/
public theorem theorem_12_6_equal_degree_of_rank_two
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hrank : IsMulCommutative H ∧ groupRank H = 2) :
    ∀ X Y : S,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L) := by
  classical
  rcases h12_1 with ⟨hmax, hMF, hTypeI, hS, hτ⟩
  have h12_1' : hypothesis_12_1_data L H S R τ :=
    ⟨hmax, hMF, hTypeI, hS, hτ⟩
  have hSbot :
      Section6.inducedKernelFamily (H.subgroupOf L) ⊥ S :=
    theorem_12_6_inducedKernelFamily_bot_of_hypothesis12 L H S R τ h12_1'
  have hKcomm : IsMulCommutative (H.subgroupOf L) := by
    letI : IsMulCommutative H := hrank.1
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (s := H) a.property b.property
  have hquot :
      IsMulCommutative
        ((H.subgroupOf L) ⧸
          (⊥ : Subgroup L).subgroupOf (H.subgroupOf L)) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    calc
      QuotientGroup.mk x * QuotientGroup.mk y = QuotientGroup.mk (x * y) := by simp
      _ = QuotientGroup.mk (y * x) := by rw [hKcomm.is_comm.comm x y]
      _ = QuotientGroup.mk y * QuotientGroup.mk x := by simp
  intro X Y
  have hX :=
    Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
      (K := H.subgroupOf L) (A := ⊥) (SA := S)
      hSbot (by infer_instance) hquot X.property
  have hY :=
    Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
      (K := H.subgroupOf L) (A := ⊥) (SA := S)
      hSbot (by infer_instance) hquot Y.property
  exact hX.trans hY.symm

/-- The rank-two branch in the proof of Peterfalvi `(12.6)`: in case `(b)` of
Definition `(8.3)`, the elements of `S` have equal degree, and PF `(5.7)`
gives coherence. -/
public theorem theorem_12_6_coherent_of_rank_two
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (hrank : IsMulCommutative H ∧ groupRank H = 2) :
    Section6.coherentFamily S τ := by
  classical
  have hdeg : ∀ X Y : S,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L) :=
    theorem_12_6_equal_degree_of_rank_two L H S R τ h12_1 hrank
  rcases theorem_12_2_a L H S R τ h12_1 with ⟨SX, hdata⟩
  rcases theorem_12_2_b L H S SX R τ h12_1 hdata with
    ⟨_R1, Rfun, _hRdata, h52⟩
  rcases h52 with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
  exact Section5.theorem_5_7 S τ Rfun hsetup h52a h52b h52c h52d h52e hdeg

/-- The PF `(6.4)` package used in the exponent-divisibility branch of
Peterfalvi `(12.6)`. -/
public theorem theorem_12_6_hypothesis_6_4_of_exponent_case
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H) :
    Section6.hypothesis_6_4_statement
        (H.subgroupOf L) (⊥ : Subgroup L)
        ⁅H.subgroupOf L, H.subgroupOf L⁆ S τ ∧
      Section6.inducedKernelFamily (H.subgroupOf L) (⊥ : Subgroup L) S := by
  classical
  rcases h12_1 with ⟨hmax, hMF, hTypeI, hS, hτ⟩
  rcases hMF.1 with ⟨_hHL, _hHnorm, hHnil, _hHall⟩
  have h12_1' : hypothesis_12_1_data L H S R τ :=
    ⟨hmax, hMF, hTypeI, hS, hτ⟩
  have hSbot :
      Section6.inducedKernelFamily (H.subgroupOf L) (⊥ : Subgroup L) S :=
    theorem_12_6_inducedKernelFamily_bot_of_hypothesis12 L H S R τ h12_1'
  rcases theorem_12_2_a L H S R τ h12_1' with ⟨SX, hdata⟩
  rcases theorem_12_2_b L H S SX R τ h12_1' hdata with
    ⟨_R1, Rfun, _hRdata, h52R⟩
  have h52 : Section5.hypothesis_5_2_statement S τ := by
    rcases h52R with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
    exact ⟨hsetup, Rfun, h52a, h52b, h52c, h52d, h52e⟩
  have hHne : (H.subgroupOf L) ≠ ⊥ := by
    rcases hfrob with ⟨_hHLf, _hHnormf, _Rcomp, _hcomp, hHne, _hRne, _hcent⟩
    exact hHne
  have hnilLocal : Group.IsNilpotent (H.subgroupOf L) := by
    exact Group.nilpotent_of_mulEquiv (G := H) (G' := H.subgroupOf L)
      (Subgroup.subgroupOfEquivOfLe _hHL).symm
  have hfrobQuot :
      Section6.frobeniusQuotientWithKernel
        (H.subgroupOf L) ⁅H.subgroupOf L, H.subgroupOf L⁆ := by
    rcases hfrob with ⟨_hHLf, hHnormf, Rcomp, hcomp, _hHneF, hRne, hcent⟩
    haveI : (H.subgroupOf L).Normal := hHnormf
    have hcentElem :
        ∀ r : Rcomp, r ≠ 1 →
          elementCentralizerIn (H.subgroupOf L) (r : L) = ⊥ := by
      intro r hr
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcent r hr
    exact Section6.theorem_6_8_frobeniusQuotient_commutator_of_complement
      hHne hnilLocal hcomp hRne hcentElem
  have hcomm :
      Section6.commutatorQuotientHypothesis
        (⊥ : Subgroup L) ⁅H.subgroupOf L, H.subgroupOf L⁆
        (H.subgroupOf L) :=
    Section6.theorem_6_8_commutatorQuotient_bot_commutator
      (H.subgroupOf L) _hHnorm
  have hnilQuot :
      Section6.nilpotentQuotient (⊥ : Subgroup L) (H.subgroupOf L) :=
    Section6.theorem_6_8_nilpotentQuotient_bot (H.subgroupOf L) _hHnorm hnilLocal
  have hsolvLocal : Group.IsSolvable (H.subgroupOf L) := by
    letI : Group.IsNilpotent (H.subgroupOf L) := hnilLocal
    exact IsNilpotent.to_isSolvable
  have h61 :
      Section6.hypothesis_6_1_statement (H.subgroupOf L) S τ :=
    ⟨h52, _hHnorm, hsolvLocal, hSbot⟩
  have h64 :
      Section6.hypothesis_6_4_statement
        (H.subgroupOf L) (⊥ : Subgroup L)
        ⁅H.subgroupOf L, H.subgroupOf L⁆ S τ := by
    exact ⟨h61, odd_card_of_typeIDefinitionData L H hTypeI, bot_le, bot_le,
      hnilQuot, hcomm, hfrobQuot⟩
  exact ⟨h64, hSbot⟩

/-- PF `(6.5.b)` as used in the exponent-divisibility branch of
Peterfalvi `(12.6)`: non-coherence produces a bottom nonabelian
`p`-quotient. -/
public theorem theorem_12_6_exists_nonabelianPQuotient_of_not_coherent_exponent_case
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hnot : ¬ Section6.coherentFamily S τ) :
    ∃ p : ℕ,
      Section6.nonabelianPQuotient
        (⊥ : Subgroup L) (H.subgroupOf L) p := by
  classical
  rcases theorem_12_6_hypothesis_6_4_of_exponent_case
      L H S R τ h12_1 hfrob with
    ⟨h64, hSbot⟩
  exact Section6.theorem_6_5_b (H.subgroupOf L) (⊥ : Subgroup L)
    ⁅H.subgroupOf L, H.subgroupOf L⁆ S S τ h64 hSbot hnot

/-- First reduction in the exponent-divisibility branch of PF `(12.6)`.

If the family is not coherent, PF `(6.5.b)` applied with
`K = H.subgroupOf L`, `M = ⊥`, and `H₁ = ⁅H.subgroupOf L,H.subgroupOf L⁆`
produces a nonabelian `p`-quotient.  Since `M = ⊥`, this says that the local
copy of `H` in `L` is a `p`-group. -/
public theorem theorem_12_6_exists_isPGroup_of_not_coherent_exponent_case
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hnot : ¬ Section6.coherentFamily S τ) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p (H.subgroupOf L) := by
  classical
  rcases theorem_12_6_exists_nonabelianPQuotient_of_not_coherent_exponent_case
      L H S R τ h12_1 hfrob hnot with
    ⟨p, hpQ⟩
  exact ⟨p, hpQ.2.2.2.2.1, Section6.theorem_6_6_isPGroup_of_nonabelianPQuotient_bot hpQ⟩

/-- If the ambient Frobenius-kernel hypothesis holds, then the Type-F
complement chosen in `(8.1)` is itself a Frobenius complement. -/
public theorem theorem_12_6_frobeniusJoinWithKernel_of_typeF_frobenius
    {G : Type u} [Group G] [Finite G]
    (L H U U1 U0 : Subgroup G)
    (hF : Section8.typeFData L H U U1 U0)
    (hfrob : Section7.frobeniusWithKernel L H) :
    section12FrobeniusJoinWithKernel H U := by
  classical
  rcases hF with
    ⟨_hsolvL, _hoddL, hMF, _hHne, _hHLt, _hUne, hcomp, _hU1leU,
      _hU1comm, _hU1norm, _hcent, _hU0leU, _hexp, _hfrobU0⟩
  have hfrob6 : Section6.frobeniusWithKernel L H := by
    rcases hfrob with ⟨hHL, hHnorm, R, hcompR, hHneF, hRne, hcentR⟩
    exact ⟨hHL, hHnorm, R, hcompR, hHneF, hRne, hcentR⟩
  have hHnorm : (H.subgroupOf L).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  let Kloc : Subgroup L := H.subgroupOf L
  let Uloc : Subgroup L := U.subgroupOf L
  have hcompU : Kloc.IsComplement' Uloc := by
    simpa [Kloc, Uloc] using
      section12ComplementIn_left_normal_isComplement' hcomp hHnorm
  have hKloc_ne : Kloc ≠ ⊥ := by
    intro hbot
    have hHcard : Nat.card H = 1 := by
      calc
        Nat.card H = Nat.card Kloc := by
          symm
          exact natCard_subgroupOf_eq H L hcomp.1
        _ = 1 := by simp [Kloc, hbot]
    exact (ne_of_gt _hHne) ((Subgroup.eq_bot_iff_card (H := H)).2 hHcard)
  have hUloc_ne : Uloc ≠ ⊥ := by
    intro hbot
    have hUcard : Nat.card U = 1 := by
      calc
        Nat.card U = Nat.card Uloc := by
          symm
          exact natCard_subgroupOf_eq U L hcomp.2.1
        _ = 1 := by simp [Uloc, hbot]
    exact _hUne ((Subgroup.eq_bot_iff_card (H := U)).2 hUcard)
  have hcentU :
      ∀ u : Uloc, u ≠ 1 → elementCentralizerIn Kloc (u : L) = ⊥ := by
    intro u hu
    have huU : ((u : L) : G) ∈ U := by
      exact Subgroup.mem_subgroupOf.mp u.property
    have hu_notH : ((u : L) : G) ∉ H := by
      intro huH
      have huInf : ((u : L) : G) ∈ H ⊓ U := ⟨huH, huU⟩
      have huBot : ((u : L) : G) ∈ (⊥ : Subgroup G) := by
        exact hcomp.2.2.2.le_bot huInf
      apply hu
      apply Subtype.ext
      apply Subtype.ext
      simpa using huBot
    have hcentH :
        Section2.centralizerIn H ((u : L) : G) = ⊥ :=
      Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
        hfrob6 ((u : L) : G) (hcomp.2.1 huU) hu_notH
    ext x
    constructor
    · intro hx
      have hxH : ((x : L) : G) ∈ Section2.centralizerIn H ((u : L) : G) := by
        rcases hx with ⟨hxK, hxcent⟩
        refine ⟨by simpa [Kloc, Subgroup.mem_subgroupOf] using hxK, ?_⟩
        have hxcommL : (x : L) * (u : L) = (u : L) * (x : L) :=
          Subgroup.mem_centralizer_singleton_iff.mp hxcent
        have hxcommG :
            ((x : L) : G) * ((u : L) : G) =
              ((u : L) : G) * ((x : L) : G) :=
          congrArg (fun y : L => (y : G)) hxcommL
        exact Subgroup.mem_centralizer_singleton_iff.mpr hxcommG
      have hxBot : ((x : L) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hcentH] using hxH
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxBot))
    · intro hx
      rw [Subgroup.mem_bot.mp hx]
      exact (elementCentralizerIn Kloc (u : L)).one_mem
  have hfrobUloc : IsFrobeniusGroupWithKernelComplement Kloc Uloc :=
    (lemma_3_1 Kloc Uloc hKloc_ne hUloc_ne hHnorm hcompU).2 hcentU
  rw [section12FrobeniusJoinWithKernel, ← hcomp.2.2.1]
  simpa [Kloc, Uloc] using hfrobUloc

/-- PF `(8.2.a)` as used in the exponent branch of Peterfalvi `(12.6)`:
the quotient `L/H` has exponent equal to its order. -/
public theorem theorem_12_6_quotient_exponent_eq_card_of_typeF
    {G : Type u} [Group G] [Finite G]
    (L H U U1 U0 : Subgroup G)
    [hHnorm : (H.subgroupOf L).Normal]
    (hF : Section8.typeFData L H U U1 U0)
    (hfrob : Section7.frobeniusWithKernel L H) :
    Monoid.exponent (L ⧸ H.subgroupOf L) =
      Nat.card (L ⧸ H.subgroupOf L) := by
  classical
  rcases hF with
    ⟨hsolvL, hoddL, hMF, hHne, hHLt, hUne, hcomp, hU1leU,
      hU1comm, hU1norm, hcent, hU0leU, hexp, hfrobU0⟩
  have hF' : Section8.typeFData L H U U1 U0 :=
    ⟨hsolvL, hoddL, hMF, hHne, hHLt, hUne, hcomp, hU1leU,
      hU1comm, hU1norm, hcent, hU0leU, hexp, hfrobU0⟩
  have hfrobU : section12FrobeniusJoinWithKernel H U :=
    theorem_12_6_frobeniusJoinWithKernel_of_typeF_frobenius
      L H U U1 U0 hF' hfrob
  have hcycSylow : ∀ p : Nat.Primes, ∀ P : Sylow p.val U,
      IsCyclic (P : Subgroup U) :=
    (Section8.theorem_8_2_b L H U U1 U0 hF').1 hfrobU
  have hcardU_exp : Nat.card U = Monoid.exponent U := by
    have hZU : IsZGroup U := by
      rw [isZGroup_iff]
      intro p hp P
      exact hcycSylow ⟨p, hp⟩ P
    letI : IsZGroup U := hZU
    exact (IsZGroup.exponent_eq_card U).symm
  have hcompLocal : (H.subgroupOf L).IsComplement' (U.subgroupOf L) :=
    section12ComplementIn_left_normal_isComplement' hcomp hHnorm
  let eQ : L ⧸ H.subgroupOf L ≃* U.subgroupOf L :=
    hcompLocal.symm.QuotientMulEquiv
  have hExpQuot :
      Monoid.exponent (L ⧸ H.subgroupOf L) =
        Monoid.exponent (U.subgroupOf L) := by
    simpa using Monoid.exponent_eq_of_mulEquiv eQ
  have hExpUsub :
      Monoid.exponent (U.subgroupOf L) = Monoid.exponent U := by
    simpa using
      Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hcomp.2.1)
  have hCardQuot :
      Nat.card (L ⧸ H.subgroupOf L) = Nat.card (U.subgroupOf L) := by
    exact Nat.card_congr eQ.toEquiv
  have hCardUsub : Nat.card (U.subgroupOf L) = Nat.card U := by
    exact natCard_subgroupOf_eq U L hcomp.2.1
  calc
    Monoid.exponent (L ⧸ H.subgroupOf L) =
        Monoid.exponent (U.subgroupOf L) := hExpQuot
    _ = Monoid.exponent U := hExpUsub
    _ = Nat.card U := hcardU_exp.symm
    _ = Nat.card (U.subgroupOf L) := hCardUsub.symm
    _ = Nat.card (L ⧸ H.subgroupOf L) := hCardQuot.symm

/-- The exponent-divisibility branch in the proof of Peterfalvi `(12.6)`.

This is the source case `(8.3.c)`: after reducing to a `p`-group by PF
`(6.5.b)`, PF `(8.2.a)` identifies the exponent of `L/H`; the divisibility
condition in Definition `(8.3.c)` then lets PF `(6.5.c)` give coherence. -/
public theorem theorem_12_6_coherent_of_exponent_case
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (U U1 U0 : Subgroup G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hF : Section8.typeFData L H U U1 U0)
    (hexp : (∀ p : Nat.Primes, p ∈ subgroupPrimeSet H →
        Monoid.exponent U ∣ p.val - 1) ∧
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet H ∧
        IsCyclic (section10PPrimeCore p H)) :
    Section6.coherentFamily S τ := by
  by_contra hnot
  rcases theorem_12_6_exists_isPGroup_of_not_coherent_exponent_case
      L H S R τ h12_1 hfrob hnot with
    ⟨p, hpprime, hHp⟩
  rcases hF with
    ⟨hsolvL, hoddL, hMF, hHne, hHLt, hUne, hcomp, hU1leU,
      hU1comm, hU1norm, hcent, hU0leU, hexpU0, hfrobU0⟩
  have hF' : Section8.typeFData L H U U1 U0 :=
    ⟨hsolvL, hoddL, hMF, hHne, hHLt, hUne, hcomp, hU1leU,
      hU1comm, hU1norm, hcent, hU0leU, hexpU0, hfrobU0⟩
  haveI : (H.subgroupOf L).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  have hquot_exp_card :
      Monoid.exponent (L ⧸ H.subgroupOf L) =
        Nat.card (L ⧸ H.subgroupOf L) :=
    theorem_12_6_quotient_exponent_eq_card_of_typeF
      L H U U1 U0 hF' hfrob
  let pp : Nat.Primes := ⟨p, hpprime⟩
  have hHpH : IsPGroup p H :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := H) (K := L) hcomp.1)
  have hp_mem_H : pp ∈ subgroupPrimeSet H := by
    have hH_ne_bot : H ≠ ⊥ := ne_of_gt hHne
    have hπH : subgroupPrimeSet H = ({pp} : Set Nat.Primes) := by
      haveI : Fact p.Prime := ⟨hpprime⟩
      have hp_eq : (⟨p, Fact.out⟩ : Nat.Primes) = pp := Subtype.ext rfl
      simpa [pp, hp_eq] using
        section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
          (G := G) (p := p) (H := H) hHpH hH_ne_bot
    rw [hπH]
    exact Set.mem_singleton_iff.mpr (Subtype.ext rfl)
  have hExpU_dvd_pred : Monoid.exponent U ∣ p - 1 := by
    simpa [pp] using hexp.1 pp hp_mem_H
  have hcompLocal : (H.subgroupOf L).IsComplement' (U.subgroupOf L) :=
    section12ComplementIn_left_normal_isComplement' hcomp
      (section16MFSubgroup_subgroupOf_normal hMF)
  let eQ : L ⧸ H.subgroupOf L ≃* U.subgroupOf L :=
    hcompLocal.symm.QuotientMulEquiv
  have hExpQuotU :
      Monoid.exponent (L ⧸ H.subgroupOf L) = Monoid.exponent U := by
    calc
      Monoid.exponent (L ⧸ H.subgroupOf L) =
          Monoid.exponent (U.subgroupOf L) := by
            simpa using Monoid.exponent_eq_of_mulEquiv eQ
      _ = Monoid.exponent U := by
            simpa using
              Monoid.exponent_eq_of_mulEquiv
                (Subgroup.subgroupOfEquivOfLe (H := U) (K := L) hcomp.2.1)
  have hquot_exp_dvd_pred :
      Monoid.exponent (L ⧸ H.subgroupOf L) ∣ p - 1 := by
    simpa [hExpQuotU] using hExpU_dvd_pred
  have hcard_quot_dvd_pred :
      Nat.card (L ⧸ H.subgroupOf L) ∣ p - 1 := by
    simpa [hquot_exp_card] using hquot_exp_dvd_pred
  have hpQ :
      Section6.nonabelianPQuotient
        (⊥ : Subgroup L) (H.subgroupOf L) p := by
    rcases theorem_12_6_exists_nonabelianPQuotient_of_not_coherent_exponent_case
        L H S R τ h12_1 hfrob hnot with
      ⟨q, hqQ⟩
    have hqprime : Nat.Prime q := hqQ.2.2.2.2.1
    have hqP :
        IsPGroup q (H.subgroupOf L) :=
      Section6.theorem_6_6_isPGroup_of_nonabelianPQuotient_bot hqQ
    have hqH : IsPGroup q H :=
      hqP.of_equiv (Subgroup.subgroupOfEquivOfLe (H := H) (K := L) hcomp.1)
    let qq : Nat.Primes := ⟨q, hqprime⟩
    have hp_eq_q : p = q := by
      have hp_mem_single : pp ∈ ({qq} : Set Nat.Primes) := by
        have hH_ne_bot : H ≠ ⊥ := ne_of_gt hHne
        have hπH : subgroupPrimeSet H = ({qq} : Set Nat.Primes) := by
          haveI : Fact q.Prime := ⟨hqprime⟩
          simpa [qq] using
            section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
              (G := G) (p := q) (H := H) hqH hH_ne_bot
        simpa [hπH] using hp_mem_H
      have hppqq : pp = qq := by simpa using hp_mem_single
      exact congrArg (fun r : Nat.Primes => r.val) hppqq
    simpa [hp_eq_q] using hqQ
  rcases theorem_12_6_hypothesis_6_4_of_exponent_case
      L H S R τ h12_1 hfrob with
    ⟨h64, hSbot⟩
  have hnot_rel :
      ¬ (H.subgroupOf L).relIndex (⊤ : Subgroup L) ∣ p - 1 :=
    Section6.theorem_6_5_c (H.subgroupOf L) (⊥ : Subgroup L)
      ⁅H.subgroupOf L, H.subgroupOf L⁆ S S τ h64 hSbot hnot p hpQ
  have hrel_dvd_pred :
      (H.subgroupOf L).relIndex (⊤ : Subgroup L) ∣ p - 1 := by
    simpa [Subgroup.relIndex_top_right, Subgroup.index_eq_card] using hcard_quot_dvd_pred
  exact hnot_rel hrel_dvd_pred

/-- Peterfalvi `(12.6)`.

The set `S` consists of irreducible characters.  Moreover, `S` is a
coherent family. -/
public theorem theorem_12_6
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h12_1 : hypothesis_12_1_data L H S R τ)
    (hfrob : Section7.frobeniusWithKernel L H) :
    (∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup χ) ∧
    Section6.coherentFamily S τ := by
  refine ⟨?_, ?_⟩
  · exact theorem_12_6_irreducible_of_frobenius L H S R τ h12_1 hfrob
  · rcases h12_1 with ⟨hmax, hMF, hTypeI, hS, hτ⟩
    rcases hTypeI with ⟨U, U1, U0, hF, hcases⟩
    rcases hcases with hTI | hcases
    · exact theorem_12_6_coherent_of_TI L H S R τ
        ⟨hmax, hMF, ⟨U, U1, U0, hF, Or.inl hTI⟩, hS, hτ⟩ hfrob hTI
    · rcases hcases with hrank | hexp
      · exact theorem_12_6_coherent_of_rank_two L H S R τ
          ⟨hmax, hMF, ⟨U, U1, U0, hF, Or.inr (Or.inl hrank)⟩, hS, hτ⟩
          hfrob hrank
      · exact theorem_12_6_coherent_of_exponent_case L H S R τ U U1 U0
          ⟨hmax, hMF, ⟨U, U1, U0, hF, Or.inr (Or.inr hexp)⟩, hS, hτ⟩
          hfrob hF hexp


end CFSG.Section12
