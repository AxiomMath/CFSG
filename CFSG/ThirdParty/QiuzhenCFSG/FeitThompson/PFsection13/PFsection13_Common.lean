module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_12_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_Common
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

@[expose] public def theorem_13_10_sourceEstimate
    (p q u c : ℕ) (m : ℝ) : Prop :=
  0 < p ∧ 0 < q ∧ 0 < c ∧
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) > m / (p : ℝ)

/- The unfolded numerical estimate produced before substituting the definition
of `m` at the end of the proof of Peterfalvi `(13.10)`. -/
@[expose] public def theorem_13_10_rawSourceEstimate
    (p q u c : ℕ) : Prop :=
  0 < p ∧ 1 < q ∧ 0 < c ∧
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
      1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) -
        ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))


public theorem section13_theorem_13_10_sourceEstimate_from_raw
    {p q u c : ℕ} {m : ℝ}
    (hm : m = 1 - 1 / ((q - 1 : ℕ) : ℝ) -
      ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)))
    (hraw : theorem_13_10_rawSourceEstimate p q u c) :
    theorem_13_10_sourceEstimate p q u c m := by
  rcases hraw with ⟨hp, hq1, hc, hineq⟩
  refine ⟨hp, by omega, hc, ?_⟩
  have hq : 0 < q := by omega
  have hpRpos : (0 : ℝ) < p := by exact_mod_cast hp
  have hpR : (p : ℝ) ≠ 0 := hpRpos.ne'
  have hqsub_pos : 0 < q - 1 := Nat.sub_pos_of_lt hq1
  have hqsubRpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hqsub_pos
  have hqsubR : ((q - 1 : ℕ) : ℝ) ≠ 0 := hqsubRpos.ne'
  have hqRpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR : (q : ℝ) ≠ 0 := hqRpos.ne'
  have hqpowR : (q : ℝ) ^ p ≠ 0 := pow_ne_zero p hqR
  have hmdiv : m / (p : ℝ) =
      1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) -
        ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := by
    rw [hm]
    field_simp [hpR, hqsubR, hqpowR]
  simpa [hmdiv] using hineq

public theorem section13_theorem_13_10_rawSourcePositivity_of_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    0 < p ∧ 1 < q ∧ 0 < c := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, hc_card,
      _hd_card, _hU, _hV, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
      _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
      _hSType, _hTType, _hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hp_card]
    exact Nat.card_pos
  · rw [hq_card]
    exact (Subgroup.one_lt_card_iff_ne_bot W1).2 hW1ne
  · rw [hc_card]
    exact Nat.card_pos

public theorem section13_uv_pos_of_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    0 < u ∧ 0 < v := by
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, hU_card, hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hVpos : 0 < Nat.card V := Nat.card_pos
  rw [hU_card] at hUpos
  rw [hV_card] at hVpos
  exact ⟨Nat.pos_of_mul_pos_right hUpos, Nat.pos_of_mul_pos_right hVpos⟩

public theorem section13_section12InternalDirectProduct_swap
    {G : Type u} [Group G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W) :
    section12InternalDirectProduct W2 W1 W := by
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  refine ⟨hW2le, hW1le, ?_, hdisj.symm, ?_⟩
  · simpa [sup_comm] using hW
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hy) x hx).symm

/-- In a cyclic internal direct product, the two factors have coprime orders. -/
public theorem section13_natCard_coprime_of_section12InternalDirectProduct_cyclic
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcyc : IsCyclic W) :
    Nat.Coprime (Nat.card W1) (Nat.card W2) := by
  classical
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  let J : Subgroup G := W1 ⊔ W2
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) :=
    hcent.trans (centralizer_le_normalizer W2)
  let W1J : Subgroup J := W1.subgroupOf J
  let W2J : Subgroup J := W2.subgroupOf J
  haveI : W2J.Normal := by
    simpa [J, W2J] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  let f : W1 × W2 →* W :=
    { toFun := fun p =>
        ⟨(p.1 : G) * (p.2 : G), W.mul_mem (hW1le p.1.2) (hW2le p.2.2)⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro p q
        ext
        have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          (Subgroup.mem_centralizer_iff.mp (hcent q.1.2) (p.2 : G) p.2.2).symm
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc
          ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
              (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by
                simp [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hcomm]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by
                simp [mul_assoc] }
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    have hmul : (h₁ : G) * (k₁ : G) = (h₂ : G) * (k₂ : G) :=
      Subtype.ext_iff.mp heq
    have hleft_eq_right : (h₂ : G)⁻¹ * (h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by
      calc
        (h₂ : G)⁻¹ * (h₁ : G) =
            (h₂ : G)⁻¹ * ((h₁ : G) * (k₁ : G)) * (k₁ : G)⁻¹ := by
              simp [mul_assoc]
        _ = (h₂ : G)⁻¹ * ((h₂ : G) * (k₂ : G)) * (k₁ : G)⁻¹ := by
              rw [hmul]
        _ = (k₂ : G) * (k₁ : G)⁻¹ := by
              simp
    have hmemW1 : (h₂ : G)⁻¹ * (h₁ : G) ∈ W1 :=
      W1.mul_mem (W1.inv_mem h₂.2) h₁.2
    have hmemW2 : (h₂ : G)⁻¹ * (h₁ : G) ∈ W2 := by
      rw [hleft_eq_right]
      exact W2.mul_mem k₂.2 (W2.inv_mem k₁.2)
    have hh_eq_one : (h₂ : G)⁻¹ * (h₁ : G) = 1 :=
      Subgroup.disjoint_def.mp hdisj hmemW1 hmemW2
    have hh : h₁ = h₂ := by
      apply Subtype.ext
      calc
        (h₁ : G) = (h₂ : G) * ((h₂ : G)⁻¹ * (h₁ : G)) := by simp
        _ = (h₂ : G) := by simp [hh_eq_one]
    have hk : k₁ = k₂ := by
      apply Subtype.ext
      have hmul' := congrArg (fun z : G => (h₂ : G)⁻¹ * z) hmul
      simpa [hh, mul_assoc] using hmul'
    exact Prod.ext hh hk
  have hf_surj : Function.Surjective f := by
    intro w
    let j : J := ⟨(w : G), by simp [J, ← hW, w.2]⟩
    have htop : W1J ⊔ W2J = ⊤ := by
      simpa [J, W1J, W2J] using
        (Subgroup.subgroupOf_sup (A := W1) (A' := W2) (B := J)
          le_sup_left le_sup_right).symm
    have hjmem : j ∈ W1J ⊔ W2J := by
      rw [htop]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right.mp hjmem) with ⟨x, hx, y, hy, hxy⟩
    refine ⟨(⟨(x : G), by simpa [W1J, Subgroup.mem_subgroupOf] using hx⟩,
      ⟨(y : G), by simpa [W2J, Subgroup.mem_subgroupOf] using hy⟩), ?_⟩
    ext
    change (x : G) * (y : G) = (w : G)
    simpa [j] using congrArg Subtype.val hxy
  let e : W1 × W2 ≃* W := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hprodcyc : IsCyclic (W1 × W2) := e.isCyclic.mpr hcyc
  letI : IsCyclic (W1 × W2) := hprodcyc
  simpa [Nat.card_eq_fintype_card] using coprime_card_of_isCyclic_prod W1 W2

public theorem section13_theorem_8_8_source_case_b_data_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : Section8.theorem_8_8_source_case_b_data W W1 W2 S T SF TF) :
    Section8.theorem_8_8_source_case_b_data W W2 W1 T S TF SF := by
  rcases hcase with
    ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
      hSeq, hTeq, hSdisj, hTdisj, hST, hTypeII, hSType, hTType, hCover⟩
  refine ⟨section13_section12InternalDirectProduct_swap hprod, hcyc, hW2ne, hW1ne,
    ?_, hTmax, hSmax, hTF, hSF, hTeq, hSeq, hTdisj, hSdisj, ?_, ?_, hTType,
    hSType, ?_⟩
  · intro W0 hW0ne hW0sub
    exact hnorm W0 hW0ne (by
      intro x hx
      simpa [Set.union_comm] using hW0sub hx)
  · simpa [inf_comm] using hST
  · rcases hTypeII with hSII | hTII
    · exact Or.inr hSII
    · exact Or.inl hTII
  · intro M hM
    rcases hCover M hM with hS | hT | hI
    · exact Or.inr (Or.inl hS)
    · exact Or.inl hT
    · exact Or.inr (Or.inr hI)

public theorem section13_theorem_3_2_map_statement_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
    Section3.theorem_3_2_map_statement W2 W1 W σ := by
  rcases hσ with ⟨hiso, hvirt, hind, hclass, hprin, hagree, hvanish⟩
  refine ⟨hiso, hvirt, ?_, hclass, hprin, ?_, ?_⟩
  · intro α hα
    exact hind α (by simpa [Section3.cyclicTISet, Set.union_comm] using hα)
  · intro α hα x hx
    simpa [Section3.cyclicTISet, Set.union_comm] using hagree α hα x (by
      simpa [Section3.cyclicTISet, Set.union_comm] using hx)
  · intro χ hχ hχnot
    simpa [Section3.VanishesOn, Section3.cyclicTISet, Set.union_comm] using
      hvanish χ hχ hχnot

public theorem section13_notation_8_10_source_data_A_eq_centralizerUnion_of_late
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hLate :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    A = Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms := by
  rcases hNotation with ⟨_hM, _hMF, hChoice, _hA1, hCases⟩
  rcases hCases with hI | hP
  · rcases hI with ⟨hTypeI, _hA, _hA0⟩
    have hnotI : ¬ Section8.typeIDefinitionData M MF := by
      rcases hChoice with hI' | hII | hIII | hIV | hV
      · intro _hTypeI
        rcases hLate with hIII | hIV | hV
        · exact hI'.2.2.1 hIII
        · exact hI'.2.2.2.1 hIV
        · exact hI'.2.2.2.2.1 hV
      · exact hII.1
      · exact hIII.1
      · exact hIV.1
      · exact hV.1
    exact False.elim (hnotI hTypeI)
  · rcases hP with
      ⟨_U, _W1, _W2, _hTypeP, _hTypes, hA, _hA0, _hLateA1⟩
    exact hA

public theorem section13_hypothesis52FullData_with_late_book_of_typePFourSix
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hTypeP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    ∃ Ms : Subgroup G, ∃ Abook : Set G,
      ∃ d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook,
        MF ≤ Ms ∧ d52.tau = τ ∧
          typePFourSixSigmaAgreesOnCyclicTI M W1 W2 d52.W d52.sigma ∧
          ((Section8.typeIIIDefinitionData M MF ∨
              Section8.typeIVDefinitionData M MF ∨
                Section8.typeVDefinitionData M MF) →
            Abook = Section8.section8CentralizerUnion
                (ambientDerivedSubgroup M) Ms ∧
              Ms = ambientDerivedSubgroup M) := by
  classical
  rcases hTypeP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  rcases hFourSix with
    ⟨I, instI, decI, J, instJ, decJ, W46, A, A0, i0, j0, μ, δSign, ω, σ,
      hNotation, hSigmaAgree, hCyclicSource⟩
  rcases hCyclicSource with
    ⟨H_cyclicA0, hCyclicHypothesis, hTauCyclic, _hBookSource⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hNotation with
    ⟨MFsrc, Ms, Abook, _A0book, _A1book, hSource, hW, _hA0,
      _h46, _h33, _hIso, _hVirt, _hPrin, _hSigmaCyclic, _h45, _h48,
      _hTauIso, hPackage⟩
  rcases hSource with
    ⟨hA, _hA0sub, hSourceNotation, _hDadeSource⟩
  have hMFsrcEq : MFsrc = MF :=
    section16MFSubgroup_unique hSourceNotation.2.1 hMF
  subst MFsrc
  have hMFleMs : MF ≤ Ms := by
    rcases hSourceNotation.2.2.1 with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs⟩
      rw [hMs]
    · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs⟩
      rw [hMs]
    · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hMs⟩
      rw [hMs]
      exact hDerComp.1
    · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hMs⟩
      rw [hMs]
      exact hDerComp.1
    · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs⟩
      rw [hMs]
  cases hPackage with
  | mk σM xChar H_A H_A0 hSupported _hGalois =>
      have hPrimeCarrier :
          Section4Scratch.primeDadeA0Set
              (W1.subgroupOf M) (W2.subgroupOf M) W46 A =
            Section8.section8CyclicA0Set M W1 W2 Abook := by
        simp [Section4Scratch.primeDadeA0Set,
          Section8.section8CyclicA0Set, hA, hW]
      have hCyclicHypothesis' :
          Section2.hypothesis_2_2_statement
            (Section4Scratch.subgroupImageSet M
              (Section8.section8CyclicA0Set M W1 W2 Abook))
            M H_cyclicA0 := by
        simpa [hPrimeCarrier] using hCyclicHypothesis
      have hTauCyclic' :
          ∀ α : Section1.ClassFunction M,
            Section2.CFOn M
                (Section4Scratch.subgroupImageSet M
                  (Section8.section8CyclicA0Set M W1 W2 Abook)) α →
              τ α = Section2.dadeTransform H_cyclicA0
                hCyclicHypothesis'.subset_L α := by
        intro α hα
        have hα' :
            Section2.CFOn M
              (Section4Scratch.subgroupImageSet M
                (Section4Scratch.primeDadeA0Set
                  (W1.subgroupOf M) (W2.subgroupOf M) W46 A)) α := by
          simpa [hPrimeCarrier] using hα
        calc
          τ α = Section2.dadeTransform H_cyclicA0
              hCyclicHypothesis.subset_L α := hTauCyclic α hα'
          _ = Section2.dadeTransformLinear H_cyclicA0
              hCyclicHypothesis.subset_L α :=
            (Section2.dadeTransformLinear_apply H_cyclicA0
              hCyclicHypothesis.subset_L α).symm
          _ = Section2.dadeTransform H_cyclicA0
              hCyclicHypothesis'.subset_L α :=
            Section8.dadeTransformLinear_apply_of_carrier_eq
              (congrArg (Section4Scratch.subgroupImageSet M) hPrimeCarrier)
              hCyclicHypothesis.subset_L hCyclicHypothesis'.subset_L α
      have hSupported' :
          Section4Scratch.hypothesis_4_6_supported_statement M
            (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W46
            (Ms.subgroupOf M) (Section8.section8SubgroupSetPreimage M Abook)
            i0 j0 ω σM σ μ xChar (fun j => (δSign j : ℂ)) τ H_A := by
        simpa [hA] using hSupported
      let d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook :=
        Section8.section8Hypothesis52FullData_of_supportedHypothesis
          hCyclicHypothesis' hTauCyclic' hSigmaAgree hW hSupported'
      have hSigmaAgree' : typePFourSixSigmaAgreesOnCyclicTI M W1 W2 d52.W d52.sigma := by
        dsimp [d52, Section8.section8Hypothesis52FullData_of_supportedHypothesis]
        exact hSigmaAgree
      exact ⟨Ms, Abook, d52, hMFleMs, rfl, hSigmaAgree',
        fun hLate =>
          ⟨section13_notation_8_10_source_data_A_eq_centralizerUnion_of_late
              hSourceNotation hLate,
            Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
              hSourceNotation hLate⟩⟩

public theorem section13_hypothesis52FullData_with_late_of_typePFourSix
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hTypeP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    ∃ Ms : Subgroup G, ∃ Abook : Set G,
      ∃ d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook,
        MF ≤ Ms ∧ d52.tau = τ ∧
          typePFourSixSigmaAgreesOnCyclicTI M W1 W2 d52.W d52.sigma ∧
          ((Section8.typeIIIDefinitionData M MF ∨
              Section8.typeIVDefinitionData M MF ∨
                Section8.typeVDefinitionData M MF) →
            Ms = ambientDerivedSubgroup M) := by
  rcases section13_hypothesis52FullData_with_late_book_of_typePFourSix
      hTypeP hFourSix with
    ⟨Ms, Abook, d52, hMFleMs, hd52tau, hSigmaAgree, hLateBook⟩
  exact ⟨Ms, Abook, d52, hMFleMs, hd52tau, hSigmaAgree,
    fun hLate => (hLateBook hLate).2⟩

public theorem section13_hypothesis52FullData_of_typePFourSix
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hTypeP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    ∃ Ms : Subgroup G, ∃ Abook : Set G,
      ∃ d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook,
        MF ≤ Ms ∧ d52.tau = τ ∧
          typePFourSixSigmaAgreesOnCyclicTI M W1 W2 d52.W d52.sigma := by
  rcases section13_hypothesis52FullData_with_late_of_typePFourSix
      hTypeP hFourSix with
    ⟨Ms, Abook, d52, hMFleMs, hd52tau, hSigmaAgree, _hLate⟩
  exact ⟨Ms, Abook, d52, hMFleMs, hd52tau, hSigmaAgree⟩

public theorem section13_section8InducedNonkernelFamily_of_nonkernelInducedFamily_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hTypeP : Section8.typePDefinitionData M MF U W1 W2)
    (hMFleMs : MF ≤ Ms)
    (hS : nonkernelInducedFamily M (MF ⊔ U) MF S)
    (hne : S.Nonempty)
    (hclosed : ∀ χ : Section1.ClassFunction M,
      χ ∈ S → Section1.conjugateCharacter χ ∈ S) :
    Section8.section8InducedNonkernelFamily M Ms S := by
  classical
  rcases hTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hDerEq : ambientDerivedSubgroup M = MF ⊔ U := hDerComp.2.2.1
  have hH : (MF ⊔ U).subgroupOf M = derivedSubgroup M := by
    rw [← hDerEq]
    exact section12_ambientDerivedSubgroup_subgroupOf_eq
  refine ⟨hne, hclosed, ?_⟩
  intro χ hχ
  rcases (hS.2.2 χ).mp hχ with ⟨θ, hθirr, hθnotMF, hχeq⟩
  let Q : Subgroup M → Prop := fun K =>
    ∃ B : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup B ∧
        ¬ Section1.subgroupInKernel' B ((Ms.subgroupOf M).subgroupOf K) ∧
          χ = Section1.inducedCF K B
  have hQ : Q ((MF ⊔ U).subgroupOf M) := by
    refine ⟨θ, hθirr, ?_, hχeq⟩
    intro hθkerMs
    apply hθnotMF
    exact Section9.subgroupInKernel'_mono_sec9
      (Subgroup.subgroupOf_mono ((MF ⊔ U).subgroupOf M)
        (Subgroup.subgroupOf_mono M hMFleMs)) hθkerMs
  have hQder : Q (derivedSubgroup M) := hH ▸ hQ
  rcases hQder with ⟨B, hBirr, hBnot, hχind⟩
  refine ⟨B, hBirr, ?_, hχind⟩
  intro hBker
  apply hBnot
  intro a
  exact hBker a.1 a.2

public theorem section13_nonkernelInducedFamily_conjugate_mem
    {G : Type u} [Group G] [Finite G]
    (M H K : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (hS : nonkernelInducedFamily M H K S)
    {χ : Section1.ClassFunction M}
    (hχ : χ ∈ S) :
    Section1.conjugateCharacter χ ∈ S := by
  rcases hS with ⟨_hHM, _hKH, hS⟩
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθnotker, hχeq⟩
  refine (hS (Section1.conjugateCharacter χ)).mpr ?_
  refine ⟨Section1.conjugateCharacter θ,
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hθirr, ?_, ?_⟩
  · intro hkerbar
    apply hθnotker
    intro a
    have h := hkerbar a
    have hstar := congrArg star h
    simpa [Section1.conjugateCharacter, Section1.degree] using hstar
  · rw [hχeq, Section9.conjugateCharacter_inducedCF_sec9 (H.subgroupOf M) θ]

public theorem section13_nonkernelInducedFamily_conjugate_closed
    {G : Type u} [Group G] [Finite G]
    (M H K : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (hS : nonkernelInducedFamily M H K S) :
    ∀ χ : Section1.ClassFunction M,
      χ ∈ S → Section1.conjugateCharacter χ ∈ S := by
  intro χ hχ
  exact section13_nonkernelInducedFamily_conjugate_mem M H K S hS hχ

/- PF `(1.5.e)`: in odd order, an induced irreducible whose inducing
character is nontrivial on `K` cannot be fixed by complex conjugation. -/
public theorem section13_nonkernelInducedFamily_ne_conjugate
    {G : Type u} [Group G] [Finite G]
    (M H K : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (hHnormal : (H.subgroupOf M).Normal)
    (hoddM : Odd (Nat.card M))
    (hS : nonkernelInducedFamily M H K S) :
    ∀ χ : Section1.ClassFunction M, χ ∈ S →
      χ ≠ Section1.conjugateCharacter χ := by
  letI : (H.subgroupOf M).Normal := hHnormal
  intro χ hχ hχreal
  rcases (hS.2.2 χ).mp hχ with ⟨θ, hθirr, hθnotker, hχeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθrep_ne_principal :
      ρ.character ≠ Section1.principalCharacter (H.subgroupOf M) := by
    intro hprincipal
    apply hθnotker
    intro a
    rw [hθeq, hprincipal]
    simp [Section1.principalCharacter, Section1.degree]
  have horth :
      Section1.scalarProduct M
        (Section1.inducedCF (H.subgroupOf M) ρ.character)
        (Section1.conjugateCharacter
          (Section1.inducedCF (H.subgroupOf M) ρ.character)) = 0 := by
    simpa [Section1.orthogonal] using
      (Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        (H.subgroupOf M) ρ hoddM hρirr hθrep_ne_principal)
  have hzero : Section1.scalarProduct M χ χ = 0 := by
    have horthχ :
        Section1.scalarProduct M χ (Section1.conjugateCharacter χ) = 0 := by
      simpa [hχeq, hθeq] using horth
    rw [← hχreal] at horthχ
    exact horthχ
  have hself :
      Section1.scalarProduct M χ χ =
        ((H.subgroupOf M).relIndex
          (Section1.inertiaSubgroup (H.subgroupOf M) ρ.character) : ℂ) := by
    simpa [hχeq, hθeq] using
      (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        (H.subgroupOf M) ρ hρirr)
  rw [hself] at hzero
  have hrel_ne :
      ((H.subgroupOf M).relIndex
        (Section1.inertiaSubgroup (H.subgroupOf M) ρ.character) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Subgroup.index_ne_zero_of_finite
        (H := (H.subgroupOf M).subgroupOf
          (Section1.inertiaSubgroup (H.subgroupOf M) ρ.character)))
  exact hrel_ne hzero

public theorem section13_nonempty_of_coherentFamily
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hcoh : Section6.coherentFamily S T) :
    S.Nonempty := by
  classical
  rcases hcoh with ⟨_hsrc, hnon, _hrest⟩
  rcases hnon with ⟨χ, hχon, hχne⟩
  by_contra hSempty
  rw [Finset.not_nonempty_iff_eq_empty] at hSempty
  rcases hχon with ⟨hχspan, _hsupp⟩
  rcases hχspan with ⟨v, hχeq⟩
  apply hχne
  rw [hχeq]
  subst S
  ext x
  simp [Section1.evalCoeff]

public theorem section13_typeP_pf8_RFamily_of_typePFourSix
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hTypeP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ)
    (hS : nonkernelInducedFamily M (MF ⊔ U) MF S)
    (hne : S.Nonempty) :
    ∃ Ms : Subgroup G, ∃ Abook : Set G,
      ∃ d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook,
        ∃ R : S → Finset (Section1.ClassFunction G),
          d52.tau = τ ∧
            typePFourSixSigmaAgreesOnCyclicTI M W1 W2 d52.W d52.sigma ∧
            Section5.hypothesis_5_2_a_statement S ∧
            Section5.hypothesis_5_2_c_statement S ∧
            Section5.hypothesis_5_2_d_statement S τ R ∧
            (letI : Fintype d52.I := d52.instFintypeI
             letI : Fintype d52.J := d52.instFintypeJ
             letI : DecidableEq d52.I := d52.instDecidableEqI
             letI : DecidableEq d52.J := d52.instDecidableEqJ
             letI : Fintype G := Fintype.ofFinite G
             Section5.theorem_5_3_b_extra_statement S R
               (Finset.univ.image fun p : d52.I × d52.J =>
                 d52.sigma (d52.omega p.1 p.2))) := by
  classical
  rcases section13_hypothesis52FullData_of_typePFourSix hTypeP hFourSix with
    ⟨Ms, Abook, d52, hMFleMs, hd52tau, hSigmaAgree⟩
  have hclosed : ∀ χ : Section1.ClassFunction M,
      χ ∈ S → Section1.conjugateCharacter χ ∈ S :=
    section13_nonkernelInducedFamily_conjugate_closed M (MF ⊔ U) MF S hS
  have hInd : Section8.section8InducedNonkernelFamily M Ms S :=
    section13_section8InducedNonkernelFamily_of_nonkernelInducedFamily_typeP
      hTypeP hMFleMs hS hne hclosed
  rcases Section8.theorem_8_15_hypothesis_5_2_extra_of_fullData
      (G := G) (M := M) (Ms := Ms) (W1 := W1) (W2 := W2)
      (A := Abook)
      (S := S) (by infer_instance) d52 hInd with
    ⟨R, _hsetup, _h52a, _h52b, _h52c, h52d, _h52e, hextra⟩
  refine ⟨Ms, Abook, d52, R, hd52tau, hSigmaAgree, _h52a, _h52c, ?_, hextra⟩
  simpa [hd52tau] using h52d

public theorem section13_typeP_coherent_subseq_diff_mem_puncturedSpan
    {L : Type u} [Group L] [Finite L]
    (Sfam : Finset (Section1.ClassFunction L))
    (h52a : Section5.hypothesis_5_2_a_statement Sfam)
    {φ : Section1.ClassFunction L}
    (hφS : φ ∈ Sfam)
    (hφIrr : Section1.IsIrreducibleCharacterOnGroup φ) :
    Section5.integerSpanOn Sfam Section5.puncturedSet
      (φ - Section1.conjugateCharacter φ) := by
  refine ⟨Section5.integerSpan_sub (Section5.integerSpan_of_mem Sfam hφS)
    (Section5.integerSpan_of_mem Sfam ((h52a ⟨φ, hφS⟩).1)), ?_⟩
  apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
  change Section1.degree φ - Section1.degree (Section1.conjugateCharacter φ) = 0
  rcases hφIrr with ⟨n, ρ, _hρirr, rfl⟩
  simp [Section1.degree, Section1.conjugateCharacter]

public theorem section13_orthogonalFinsets_mono_right
    {G : Type u} [Group G] [Finite G]
    {R S T : Finset (Section1.ClassFunction G)}
    (horth : Section5.orthogonalFinsets R S)
    (hsub : T ⊆ S) :
    Section5.orthogonalFinsets R T := by
  intro φ ψ hφR hψT
  exact horth hφR (hsub hψT)

/- Checked PF `(3.9)` transport adapter.  Once the local PF8 image of a
transported irreducible has the same cyclic-TI values as the global source
character, PF `(3.9)(a)` identifies it with the global PF `(3.2)` image. -/
public theorem section13_typeP_coherent_subseq_transport_eq_of_cyclicTI_agreement
    {G : Type u} [Group G] [Finite G]
    {Smax W W1 W2 : Subgroup G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p q : ℕ}
    (hq : 0 < q)
    (hp : 0 < p)
    {ωFin : Fin q → Fin p → Section1.ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hq⟩ ⟨0, hp⟩ ωFin)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    {Ms : Subgroup G} {A : Set G}
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 A)
    (e : W ≃* d52.W)
    (ξ : Section1.ClassFunction W)
    (hξ : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hVagree :
      ∀ z : G, ∀ hz : z ∈ Section3.cyclicTISet W1 W2 W,
        d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) z =
          ξ ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩) :
    σ ξ = d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hωFin σ hσ with
    ⟨χ, horth, hsigned, h00, hInd, hσω⟩
  have hσ_eq : σ = Section3.sigmaOfPF35 ωFin χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hq⟩) (j0 := ⟨0, hp⟩)
      (ω := ωFin) (χ := χ) h31 hωFin hσω
  rcases d52.fullHypothesis with
    ⟨_h46, _hW2K, _h31local, hIsoFull, hVirtFull, _hClassFull, _hPrinFull,
      _h22A, _hFullRest⟩
  have htransportIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_irreducible e hξ
  have hξ_class : Section1.IsClassFunction ξ := by
    rcases hξ with ⟨_n, ρ, _hρirr, hξeq⟩
    rw [hξeq]
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have htransportClass :
      Section1.IsClassFunction
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_isClass e hξ_class
  have htransportVirt :
      Theory.Character.IsVirtualCharacter
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup htransportIrr
  have hImageVirt :
      Theory.Character.IsVirtualCharacter
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) :=
    hVirtFull _ htransportVirt
  have hselfW : Section1.scalarProduct W ξ ξ = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hξ
  have hself :
      Section1.scalarProduct G
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ))
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) = 1 := by
    calc
      Section1.scalarProduct G
          (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ))
          (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) =
        Section1.scalarProduct d52.W
          (Section6.theorem_6_8_transportClassFunction e ξ)
          (Section6.theorem_6_8_transportClassFunction e ξ) :=
          hIsoFull _ _ htransportClass htransportClass
      _ = Section1.scalarProduct W ξ ξ :=
          Section6.theorem_6_8_scalarProduct_transportClassFunction e ξ ξ
      _ = 1 := hselfW
  have hXsigned :
      Section3.IsSignedIrreducibleCharacter
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ)) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hImageVirt hself
  have hXeq :
      d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) =
        Section3.sigmaOfPF35 ωFin χ ξ :=
    Section3.proposition_3_9_a_uniqueness_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hq⟩) (j0 := ⟨0, hp⟩)
      (ω := ωFin) (χ := χ) h31 hωFin horth hsigned h00 hInd
      hξ hXsigned hVagree
  calc
    σ ξ = Section3.sigmaOfPF35 ωFin χ ξ := by rw [hσ_eq]
    _ = d52.sigma (Section6.theorem_6_8_transportClassFunction e ξ) :=
      hXeq.symm

/- The carrier equivalence between the Section `(3.3)` cyclic-TI subgroup `W`
and the PF8 Section `(4.6)` subgroup `d52.W`.  This is bookkeeping: Section 3
gives `W = W₁ ⊔ W₂`, Type-P data embeds that product in `Smax`, and PF8 stores
`d52.W = (W₁ ⊔ W₂).subgroupOf Smax`. -/
public noncomputable def section13_typeP_cyclicTI_carrier_equiv
    {G : Type u} [Group G] [Finite G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W) :
    W ≃* d52.W := by
  classical
  have hW_eq_sup : W = W1 ⊔ W2 := by
    change Section3.isCyclicTIHypothesis W1 W2 W at h31
    rcases h31 with ⟨_hW1W, _hW2W, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    apply le_antisymm
    · intro x hxW
      rcases hIP.mul_surjective x hxW with ⟨a, ha, b, hb, hx⟩
      rw [hx]
      exact (W1 ⊔ W2).mul_mem
        ((show W1 ≤ W1 ⊔ W2 from le_sup_left) ha)
        ((show W2 ≤ W1 ⊔ W2 from le_sup_right) hb)
    · exact sup_le hIP.left_le hIP.right_le
  have hWsup_le : W1 ⊔ W2 ≤ Smax := by
    rcases hTypeP with
      ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUleDer, _hUnil,
        _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
        hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
    rcases hW1Hall with ⟨hW1le, _hHall⟩
    have hPle : P ≤ Smax := Section12.section16MFSubgroup_le hMF
    have hW2P : W2 ≤ P := hW2le.trans inf_le_left
    exact sup_le hW1le (hW2P.trans hPle)
  exact (MulEquiv.subgroupCongr hW_eq_sup).trans
    ((Subgroup.subgroupOfEquivOfLe (H := W1 ⊔ W2) (K := Smax) hWsup_le).symm.trans
      (MulEquiv.subgroupCongr d52.W_eq.symm))


public theorem section13_typeP_cyclicTI_transport_agreement
    {G : Type u} [Group G] [Finite G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (p q : ℕ)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (hq : 0 < q)
    (hp : 0 < p)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hq⟩ ⟨0, hp⟩ ωFin) :
      let e := section13_typeP_cyclicTI_carrier_equiv
        Smax W W1 W2 P U d52 hTypeP h31
      ∀ x : Fin q × Fin p,
        ∀ z : G, ∀ hz : z ∈ Section3.cyclicTISet W1 W2 W,
          d52.sigma
              (Section6.theorem_6_8_transportClassFunction e
                (ωFin x.1 x.2)) z =
            (ωFin x.1 x.2)
              ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩ := by
  classical
  intro e x z hz
  have hW_eq_sup : W = W1 ⊔ W2 := by
    change Section3.isCyclicTIHypothesis W1 W2 W at h31
    rcases h31 with ⟨_hW1W, _hW2W, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    apply le_antisymm
    · intro y hyW
      rcases hIP.mul_surjective y hyW with ⟨a, ha, b, hb, hy⟩
      rw [hy]
      exact (W1 ⊔ W2).mul_mem
        ((show W1 ≤ W1 ⊔ W2 from le_sup_left) ha)
        ((show W2 ≤ W1 ⊔ W2 from le_sup_right) hb)
    · exact sup_le hIP.left_le hIP.right_le
  have hWsup_le : W1 ⊔ W2 ≤ Smax := by
    rcases hTypeP with
      ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUleDer, _hUnil,
        _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
        hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
    rcases hW1Hall with ⟨hW1le, _hHall⟩
    have hPle : P ≤ Smax := Section12.section16MFSubgroup_le hMF
    have hW2P : W2 ≤ P := hW2le.trans inf_le_left
    exact sup_le hW1le (hW2P.trans hPle)
  have hWleS : W ≤ Smax := by
    rw [hW_eq_sup]
    exact hWsup_le
  let zS : Smax := ⟨z, hWleS (Section3.cyclicTISet_subset W1 W2 W hz)⟩
  have hzlocal :
      zS ∈ Section3.cyclicTISet
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) d52.W := by
    have hzWsup : z ∈ (W1 ⊔ W2 : Subgroup G) := by
      simpa [hW_eq_sup] using Section3.cyclicTISet_subset W1 W2 W hz
    have hzW1 : z ∉ (W1 : Set G) :=
      Section3.cyclicTISet_not_mem_left W1 W2 W hz
    have hzW2 : z ∉ (W2 : Set G) :=
      Section3.cyclicTISet_not_mem_right W1 W2 W hz
    refine ⟨?_, ?_⟩
    · simp [zS, Subgroup.mem_subgroupOf, d52.W_eq, hzWsup]
    · intro hmem
      rcases hmem with hleft | hright
      · exact hzW1 (by simpa [zS, Subgroup.mem_subgroupOf] using hleft)
      · exact hzW2 (by simpa [zS, Subgroup.mem_subgroupOf] using hright)
  have hclass : Section1.IsClassFunction
      (Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2)) :=
    Section6.theorem_6_8_transportClassFunction_isClass e
      (hωFin.is_class x.1 x.2)
  have h := hSigmaAgree _ hclass zS hzlocal
  have harg :
      e.symm
          ⟨zS, Section3.cyclicTISet_subset
            (W1.subgroupOf Smax) (W2.subgroupOf Smax) d52.W hzlocal⟩ =
        ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩ := by
    ext
    simp [e, section13_typeP_cyclicTI_carrier_equiv, zS]
  calc
    d52.sigma (Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2)) z =
        Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2)
          ⟨zS, Section3.cyclicTISet_subset
            (W1.subgroupOf Smax) (W2.subgroupOf Smax) d52.W hzlocal⟩ := h
    _ = (ωFin x.1 x.2)
        ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩ := by
      simp [Section6.theorem_6_8_transportClassFunction, harg]

/- Source leaf for the remaining finite table alignment between the Section 13
`ωFin` table and the PF8 Section `(4.6)` table after the carrier equivalence
has been fixed by checked subgroup bookkeeping. -/
public theorem section13_typeP_coherent_subseq_natural_table_transport_entries_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (hq : 0 < q)
    (hp : 0 < p)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (_hd52tau : d52.tau = τS)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (_hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hq⟩ ⟨0, hp⟩ ωFin) :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      let e := section13_typeP_cyclicTI_carrier_equiv
        Smax W W1 W2 P U d52 _hTypeP _h31
      ∀ x : Fin q × Fin p,
        ∃ y : d52.I × d52.J,
          Section6.theorem_6_8_transportClassFunction e
              (ωFin x.1 x.2) =
            d52.omega y.1 y.2 := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  intro e x
  rcases d52.fullHypothesis with
    ⟨_h46, _hW2K, _h31local, _hIsoFull, _hVirtFull, _hClassFull, _hPrinFull,
      _h22A, hFullRest⟩
  rcases hFullRest with
    ⟨hωd52, _h43b, _h43c, _h43d, _h45a, _h45b, _htauCyc, _htauA0,
      _htauIso, _htauPunct, _htauVirt, _hPF39, _hPF39BaseRow⟩
  have htransportIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2)) :=
    Section6.theorem_6_8_transportClassFunction_irreducible e
      (_hωFin.irreducible x.1 x.2)
  rcases hωd52.all_irreducibles
      (Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2))
      htransportIrr with
    ⟨i, j, hij⟩
  exact ⟨(i, j), hij⟩

/- Checked glue around the remaining table-entry source leaf.  The carrier
equivalence and the `cycTIisoC` value agreement are now checked above. -/
public theorem section13_typeP_coherent_subseq_natural_table_transport_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hq : 0 < q)
    (hp : 0 < p)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (_hd52tau : d52.tau = τS)
    (_hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (_hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hq⟩ ⟨0, hp⟩ ωFin)
    (_hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      ∃ e : W ≃* d52.W,
        ∀ x : Fin q × Fin p,
          ∃ y : d52.I × d52.J,
            (∀ z : G, ∀ hz : z ∈ Section3.cyclicTISet W1 W2 W,
              d52.sigma
                  (Section6.theorem_6_8_transportClassFunction e
                    (ωFin x.1 x.2)) z =
                (ωFin x.1 x.2)
                  ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩) ∧
            Section6.theorem_6_8_transportClassFunction e
                (ωFin x.1 x.2) =
              d52.omega y.1 y.2 := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  let e := section13_typeP_cyclicTI_carrier_equiv
    Smax W W1 W2 P U d52 _hTypeP _h31
  refine ⟨e, ?_⟩
  intro x
  rcases section13_typeP_coherent_subseq_natural_table_transport_entries_source
      Smax W W1 W2 P U τS p q ωFin hq hp d52
      _hd52tau _hTypeP _hFourSix _h31 _hωFin x with
    ⟨y, htable⟩
  refine ⟨y, ?_, htable⟩
  exact section13_typeP_cyclicTI_transport_agreement
    Smax W W1 W2 P U p q ωFin hq hp d52
    _hSigmaAgree _hTypeP _h31 _hωFin x

/- Source leaf for the remaining finite Section `(3.3)` table-convention
transfer.  The natural-number Section 13 notation has already been unpacked to
its finite `ωFin` table. -/
public theorem section13_typeP_coherent_subseq_natural_table_entry_fin_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hq : 0 < q)
    (hp : 0 < p)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (_hd52tau : d52.tau = τS)
    (_hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (_hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hq⟩ ⟨0, hp⟩ ωFin)
    (_hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      ∀ x : Fin q × Fin p,
        ∃ y : d52.I × d52.J,
          d52.sigma (d52.omega y.1 y.2) =
            σ (ωFin x.1 x.2) := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  rcases section13_typeP_coherent_subseq_natural_table_transport_source
      Smax W W1 W2 P U τS p q ωFin σ hq hp d52
      _hd52tau _hSigmaAgree _hTypeP _hFourSix _h31 _hωFin _hσ with
    ⟨e, hentries⟩
  intro x
  rcases hentries x with ⟨y, hVagree, htransport⟩
  have hξirr :
      Section1.IsIrreducibleCharacterOnGroup (ωFin x.1 x.2) :=
    _hωFin.irreducible x.1 x.2
  have hσeq :
      σ (ωFin x.1 x.2) =
        d52.sigma
          (Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2)) :=
    section13_typeP_coherent_subseq_transport_eq_of_cyclicTI_agreement
      hq hp _h31 _hωFin _hσ d52 e (ωFin x.1 x.2) hξirr hVagree
  refine ⟨y, ?_⟩
  calc
    d52.sigma (d52.omega y.1 y.2) =
        d52.sigma
          (Section6.theorem_6_8_transportClassFunction e (ωFin x.1 x.2)) := by
      rw [← htransport]
    _ = σ (ωFin x.1 x.2) := hσeq.symm

/- Checked wrapper from Section 13's natural-number notation to the finite
Section `(3.3)` table. -/
public theorem section13_typeP_coherent_subseq_natural_table_entry_index_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (_hd52tau : d52.tau = τS)
    (_hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω)
    (_hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      ∀ x : Fin q × Fin p,
        ∃ y : d52.I × d52.J,
          d52.sigma (d52.omega y.1 y.2) =
            σ (ω (x.1 : ℕ) (x.2 : ℕ)) := by
  classical
  rcases _hω with ⟨h31, hq, hp, ωFin, hωFin, hωEq⟩
  intro x
  rcases section13_typeP_coherent_subseq_natural_table_entry_fin_source
      Smax W W1 W2 P U τS p q ωFin σ hq hp d52
      _hd52tau _hSigmaAgree _hTypeP _hFourSix h31 hωFin _hσ x with
    ⟨y, hy⟩
  refine ⟨y, ?_⟩
  simpa [hωEq (x.1 : ℕ) (x.2 : ℕ) x.1.2 x.2.2] using hy

/- Checked wrapper turning the pointwise table-index source into membership in
the PF8 Section `(4.6)` table image. -/
public theorem section13_typeP_coherent_subseq_natural_table_entry_mem_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (_hd52tau : d52.tau = τS)
    (_hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω)
    (_hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      ∀ x : Fin q × Fin p,
        σ (ω (x.1 : ℕ) (x.2 : ℕ)) ∈
          (Finset.univ.image fun y : d52.I × d52.J =>
            d52.sigma (d52.omega y.1 y.2)) := by
  classical
  intro x
  rcases section13_typeP_coherent_subseq_natural_table_entry_index_source
      Smax W W1 W2 P U τS ω σ p q d52
      _hd52tau _hSigmaAgree _hTypeP _hFourSix _hω _hσ x with
    ⟨y, hy⟩
  exact Finset.mem_image.mpr ⟨y, by simp, hy⟩

/- Checked finite-set wrapper for the remaining table-convention transfer.  The
orthogonality argument only needs containment of the natural Section 13
`σ(ω i j)` image in the PF8 Section `(4.6)` image, not a componentwise
row/column indexing map. -/
public theorem section13_typeP_coherent_subseq_natural_table_image_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (_hd52tau : d52.tau = τS)
    (_hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω)
    (_hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      (Finset.univ.image fun x : Fin q × Fin p =>
          σ (ω (x.1 : ℕ) (x.2 : ℕ))) ⊆
        (Finset.univ.image fun x : d52.I × d52.J =>
          d52.sigma (d52.omega x.1 x.2)) := by
  classical
  intro χ hχ
  rcases Finset.mem_image.mp hχ with ⟨x, _hx, rfl⟩
  exact section13_typeP_coherent_subseq_natural_table_entry_mem_source
    Smax W W1 W2 P U τS ω σ p q d52
    _hd52tau _hSigmaAgree _hTypeP _hFourSix _hω _hσ x

/- Checked transfer from PF8 table orthogonality to the natural Section 13
table.  The only remaining source content is the finite image containment
above. -/
public theorem section13_typeP_coherent_subseq_natural_orthogonal_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : Subgroup G} {Abook : Set G}
    (Smax W W1 W2 P U : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook)
    (R : Sfam → Finset (Section1.ClassFunction G))
    (_hd52tau : d52.tau = τS)
    (_hSigmaAgree : typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma)
    (_hpf8orth :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      letI : Fintype G := Fintype.ofFinite G
      Section5.theorem_5_3_b_extra_statement Sfam R
        (Finset.univ.image fun x : d52.I × d52.J =>
          d52.sigma (d52.omega x.1 x.2)))
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω)
    (_hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
      ∀ φ : Section1.ClassFunction Smax, ∀ hφS : φ ∈ Sfam,
        Section1.IsIrreducibleCharacterOnGroup φ →
          Section5.orthogonalFinsets (R ⟨φ, hφS⟩)
            (Finset.univ.image fun x : Fin q × Fin p =>
              σ (ω (x.1 : ℕ) (x.2 : ℕ))) := by
  classical
  intro φ hφS hφIrr
  let Ωpf8 : Finset (Section1.ClassFunction G) :=
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    Finset.univ.image fun x : d52.I × d52.J =>
      d52.sigma (d52.omega x.1 x.2)
  let Ωnat : Finset (Section1.ClassFunction G) :=
    Finset.univ.image fun x : Fin q × Fin p =>
      σ (ω (x.1 : ℕ) (x.2 : ℕ))
  have horthPf8 : Section5.orthogonalFinsets (R ⟨φ, hφS⟩) Ωpf8 := by
    simpa [Ωpf8] using _hpf8orth ⟨φ, hφS⟩ hφIrr
  have hsub : Ωnat ⊆ Ωpf8 := by
    simpa [Ωnat, Ωpf8] using
      section13_typeP_coherent_subseq_natural_table_image_source
        Smax W W1 W2 P U τS ω σ p q d52
        _hd52tau _hSigmaAgree _hTypeP _hFourSix _hω _hσ
  simpa [Ωnat] using section13_orthogonalFinsets_mono_right horthPf8 hsub


public theorem
    section13_typeP_coherentExtension_orthogonal_cyclicTIiso_sigma_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax W W1 W2 P U : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hcohBase : Section6.coherentFamily Sfam τS)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (φ : Section1.ClassFunction Smax)
    (hφS : φ ∈ Sfam)
    (hφIrr : Section1.IsIrreducibleCharacterOnGroup φ)
    (i j : ℕ)
    (hi : i < q)
    (hj : j < p) :
    Section1.scalarProduct G (τ1 φ) (σ (ω i j)) = 0 := by
  classical
  letI : Fintype Smax := Fintype.ofFinite Smax
  have hne : Sfam.Nonempty := section13_nonempty_of_coherentFamily hcohBase
  rcases section13_typeP_pf8_RFamily_of_typePFourSix
      hTypeP hFourSix hSfam hne with
    ⟨_Ms, _Abook, d52, R, hd52tau, hSigmaAgree, h52a, h52c, h52d,
      hpf8orth⟩
  let X : Sfam := ⟨φ, hφS⟩
  have hpairSub :
      ({(X : Section1.ClassFunction Smax),
        Section1.conjugateCharacter (X : Section1.ClassFunction Smax)} :
        Finset (Section1.ClassFunction Smax)) ⊆ Sfam := by
    intro ψ hψ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with hψ | hψ
    · rw [hψ]
      exact X.2
    · rw [hψ]
      exact (h52a X).1
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction Smax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)} :
          Finset (Section1.ClassFunction Smax)) τ1 :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSub hcoh.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction Smax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)} :
          Finset (Section1.ClassFunction Smax)) τ1 :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub hcoh.2.1
  have hdiffAgree :
      τ1 ((X : Section1.ClassFunction Smax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) =
        τS ((X : Section1.ClassFunction Smax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) :=
    hcoh.2.2 _
      (section13_typeP_coherent_subseq_diff_mem_puncturedSpan
        Sfam h52a X.2 (by simpa [X] using hφIrr))
  have hsubsetφ : Section5.isSubsetSumOf (R X) (τ1 φ) := by
    simpa [X] using
      Section5.theorem_5_5_core Sfam τS R h52a h52c h52d X τ1
        hIsoPair hVirtPair hdiffAgree
  have horth :
      ∀ φ : Section1.ClassFunction Smax, ∀ hφS : φ ∈ Sfam,
        Section1.IsIrreducibleCharacterOnGroup φ →
          Section5.orthogonalFinsets (R ⟨φ, hφS⟩)
            (Finset.univ.image fun x : Fin q × Fin p =>
              σ (ω (x.1 : ℕ) (x.2 : ℕ))) :=
    section13_typeP_coherent_subseq_natural_orthogonal_source
      Smax W W1 W2 P U Sfam τS ω σ p q d52 R
      hd52tau hSigmaAgree hpf8orth hTypeP hFourSix hSfam hω hσ
  have horthφ := horth φ hφS hφIrr
  have homega :
      σ (ω i j) ∈
        (Finset.univ.image fun x : Fin q × Fin p =>
          σ (ω (x.1 : ℕ) (x.2 : ℕ))) := by
    exact Finset.mem_image.mpr
      ⟨(⟨i, hi⟩, ⟨j, hj⟩), Finset.mem_univ _, by simp⟩
  exact
    Section10.scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets
      hsubsetφ horthφ homega

public theorem section13_typeP_coherentExtension_orthogonal_cyclicTIiso_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P U : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hcohBase : Section6.coherentFamily Sfam τS)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hnotation : hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ)
    (φ : Section1.ClassFunction Smax)
    (hφS : φ ∈ Sfam)
    (hφIrr : Section1.IsIrreducibleCharacterOnGroup φ)
    (i j : ℕ)
    (hi : i < q)
    (hj : j < p) :
    Section1.scalarProduct G (τ1 φ) (η i j) = 0 := by
  rcases hnotation with
    ⟨hω, hσ, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rw [hη i j hi hj]
  exact section13_typeP_coherentExtension_orthogonal_cyclicTIiso_sigma_source
    Smax W W1 W2 P U Sfam τS τ1 ω σ p q hTypeP hFourSix hSfam
      hcohBase hcoh hω hσ φ hφS hφIrr i j hi hj

public theorem section13_hypothesis_13_1_omegaNotationData_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G} {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    (hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω) :
    hypothesis_13_1_omegaNotationData W W2 W1 q p (fun i j => ω j i) := by
  rcases hω with ⟨h31, hq, hp, ωFin, hωFin, hωspec⟩
  refine ⟨Section3.hypothesis_3_1_statement_swap h31, hp, hq,
    (fun i j => ωFin j i), ?_, ?_⟩
  · exact Section3.notation_3_3_statement_swap hωFin
  · intro i j hi hj
    exact hωspec j i hj hi

public theorem section13_hypothesis_13_1_characterNotationDataFor_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G} {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1 q p
      (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
      (fun i j => μ j i) νsum μsum δ' δ σ := by
  rcases hnotation with
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  refine ⟨section13_hypothesis_13_1_omegaNotationData_swap hω,
    section13_theorem_3_2_map_statement_swap hσ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj
    exact hη j i hj hi
  · intro j hj
    exact hδ' j hj
  · intro i hi
    exact hδ i hi
  · intro i j hi hj
    exact hνirr j i hj hi
  · intro i j hi hj
    exact hμirr j i hj hi
  · intro j hj0 hjq
    exact hνzero_nonprincipal j hj0 hjq
  · intro i hi0 hip
    exact hμzero_nonprincipal i hi0 hip
  · intro i j hi hj
    exact hνind j i hj hi
  · intro i j hi hj
    exact hμind j i hj hi
  · intro j hj
    exact hνsum j hj
  · intro i hi
    exact hμsum i hi
  · exact hbaseT
  · exact hbaseS
  · intro j k hj0 hjq hk0 hkq
    exact hνzeroDegree j k hj0 hjq hk0 hkq
  · intro i k hi0 hip hk0 hkp
    exact hμzeroDegree i k hi0 hip hk0 hkp

public theorem section13_hypothesis_13_1_characterNotationData_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G} {p q : ℕ}
    (hnotation : hypothesis_13_1_characterNotationData Smax Tmax W W1 W2 p q) :
    hypothesis_13_1_characterNotationData Tmax Smax W W2 W1 q p := by
  rcases hnotation with ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ, hfor⟩
  exact ⟨(fun i j => ω j i), (fun i j => η j i), (fun i j => ν j i),
    (fun i j => μ j i), νsum, μsum, δ', δ, σ,
    section13_hypothesis_13_1_characterNotationDataFor_swap hfor⟩

public theorem section13_hypothesis_13_1_dadeDifferenceDataFor_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G} {p q : ℕ}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (h :
      hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT p q) :
    hypothesis_13_1_dadeDifferenceDataFor Tmax Smax W W2 W1 τT τS q p := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hnotationOrig :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ :=
    section13_hypothesis_13_1_characterNotationDataFor_swap hnotation
  rcases h (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
      (fun i j => μ j i) νsum μsum δ' δ σ hnotationOrig with
    ⟨hS, hT⟩
  refine ⟨?_, ?_⟩
  · intro i j k hi hj0 hj hk0 hk hdeg
    exact hT j k i hj0 hj hk0 hk hi hdeg
  · intro i k j hi0 hi hk0 hk hj hdeg
    exact hS j i k hj hi0 hi hk0 hk hdeg

public theorem section13_hypothesis_13_1_zeroBaseDegreeDataFor_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G} {p q : ℕ}
    (h : hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2 p q) :
    hypothesis_13_1_zeroBaseDegreeDataFor Tmax Smax W W2 W1 q p := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hnotationOrig :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ :=
    section13_hypothesis_13_1_characterNotationDataFor_swap hnotation
  rcases h (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
      (fun i j => μ j i) νsum μsum δ' δ σ hnotationOrig with
    ⟨hS, hT⟩
  refine ⟨?_, ?_⟩
  · intro j k hj0 hj hk0 hk
    exact hT j k hj0 hj hk0 hk
  · intro i k hi0 hi hk0 hk
    exact hS i k hi0 hi hk0 hk

public theorem section13_hypothesis_13_1_conjugateIndexDataFor_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G} {p q : ℕ}
    (h : hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2 p q) :
    hypothesis_13_1_conjugateIndexDataFor Tmax Smax W W2 W1 q p := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hnotationOrig :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ :=
    section13_hypothesis_13_1_characterNotationDataFor_swap hnotation
  rcases h (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
      (fun i j => μ j i) νsum μsum δ' δ σ hnotationOrig with
    ⟨hS, hT⟩
  refine ⟨?_, ?_⟩
  · intro j hj0 hj
    rcases hT j hj0 hj with ⟨k, hk0, hk, hkj, hη, hμ⟩
    exact ⟨k, hk0, hk, hkj, hη, hμ⟩
  · intro i hi0 hi
    rcases hS i hi0 hi with ⟨k, hk0, hk, hki, hη, hν⟩
    exact ⟨k, hk0, hk, hki, hη, hν⟩

public theorem section13_hypothesis_13_1_conjugateBetaTauDataFor_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q : Subgroup G} {p q : ℕ}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    (h :
      hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT p q) :
    hypothesis_13_1_conjugateBetaTauDataFor Tmax Smax W W2 W1 Q P τT τS q p := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hnotationOrig :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ :=
    section13_hypothesis_13_1_characterNotationDataFor_swap hnotation
  rcases h (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
      (fun i j => μ j i) νsum μsum δ' δ σ hnotationOrig with
    ⟨hS, hT⟩
  refine ⟨?_, ?_⟩
  · intro j k hj0 hj hk0 hk hμ
    exact hT j k hj0 hj hk0 hk hμ
  · intro i k hi0 hi hk0 hk hν
    exact hS i k hi0 hi hk0 hk hν


public theorem section13_hypothesis_13_1_sourceData_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    hypothesis_13_1_sourceData Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c := by
  rcases hsource with
    ⟨hcase, hptypeS, hptypeT, hp_card, hq_card, hC, hD, hc_card, hd_card,
      hU_card, hV_card, hSfam, hTfam, hDadeS, hDadeT, hnotation,
      hDadeDiff, hZeroDegree, hConjIndex, hConjBetaTau, hChoice, hMin,
      hFourSixS, hFourSixT⟩
  exact ⟨section13_theorem_8_8_source_case_b_data_swap hcase, hptypeT, hptypeS,
    hq_card, hp_card, hD, hC, hd_card, hc_card, hV_card, hU_card, hTfam, hSfam,
    hDadeT, hDadeS, section13_hypothesis_13_1_characterNotationData_swap hnotation,
    section13_hypothesis_13_1_dadeDifferenceDataFor_swap hDadeDiff,
    section13_hypothesis_13_1_zeroBaseDegreeDataFor_swap hZeroDegree,
    section13_hypothesis_13_1_conjugateIndexDataFor_swap hConjIndex,
    section13_hypothesis_13_1_conjugateBetaTauDataFor_swap hConjBetaTau,
    hChoice, hMin, hFourSixT, hFourSixS⟩


public theorem section13_supportEnergy_mono
    {G : Type u} [Group G] [Finite G]
    {X Y : Set G} (hXY : X ⊆ Y) (χ : Section1.ClassFunction G) :
    Section7.supportEnergy X χ ≤ Section7.supportEnergy Y χ := by
  classical
  unfold Section7.supportEnergy
  refine Finset.sum_le_sum ?_
  intro g _
  by_cases hx : g ∈ X
  · have hy : g ∈ Y := hXY hx
    simp [hx, hy]
  · by_cases hy : g ∈ Y
    · simp [hx, hy, Complex.normSq_nonneg]
    · simp [hx, hy]

public theorem section13_supportEnergy_union_of_disjoint
    {G : Type u} [Group G] [Finite G]
    {X Y : Set G} (hXY : Disjoint X Y) (χ : Section1.ClassFunction G) :
    Section7.supportEnergy (X ∪ Y) χ =
      Section7.supportEnergy X χ + Section7.supportEnergy Y χ := by
  classical
  unfold Section7.supportEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro g _
  by_cases hx : g ∈ X
  · have hy : g ∉ Y := by
      intro hy
      exact hXY.le_bot ⟨hx, hy⟩
    simp [Set.mem_union, hx, hy]
  · by_cases hy : g ∈ Y
    · simp [Set.mem_union, hx, hy]
    · simp [Set.mem_union, hx, hy]

public theorem section13_supportEnergy_singleton
    {G : Type u} [Group G] [Finite G]
    (x : G) (χ : Section1.ClassFunction G) :
    Section7.supportEnergy ({x} : Set G) χ = Complex.normSq (χ x) := by
  classical
  unfold Section7.supportEnergy
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _hy hyx
    simp [hyx]
  · intro hx
    simp at hx

public theorem section13_one_div_card_le_singleton_energy_div
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G)
    (hχ1 : 1 ≤ Complex.normSq (χ 1)) :
    1 / (Nat.card G : ℝ) ≤ Section7.supportEnergy ({1} : Set G) χ / (Nat.card G : ℝ) := by
  rw [section13_supportEnergy_singleton]
  exact div_le_div_of_nonneg_right hχ1 (by positivity)

public theorem section13_supportEnergy_le_univ
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (χ : Section1.ClassFunction G) :
    Section7.supportEnergy X χ ≤ Section7.supportEnergy Set.univ χ :=
  section13_supportEnergy_mono (by intro g _hg; trivial) χ

public theorem section13_cfNormSq_eq_inv_card_mul_supportEnergy_univ
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G) :
    Section5.cfNormSq χ =
      (Nat.card G : ℝ)⁻¹ * Section7.supportEnergy Set.univ χ := by
  classical
  unfold Section5.cfNormSq Section1.scalarProduct Section7.supportEnergy
  have hcast : ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  simp only [Set.mem_univ, if_true]
  calc
    Complex.re (χ g * star (χ g))
      = Complex.re (star (χ g) * χ g) := by rw [mul_comm]
    _ = Complex.re ((Complex.normSq (χ g) : ℝ) : ℂ) := by
          congr 1
          simpa using (Complex.normSq_eq_conj_mul_self (z := χ g)).symm
    _ = Complex.normSq (χ g) := by simp

public theorem section13_supportEnergy_univ_eq_card_mul_cfNormSq
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G) :
    Section7.supportEnergy Set.univ χ = (Nat.card G : ℝ) * Section5.cfNormSq χ := by
  have h := section13_cfNormSq_eq_inv_card_mul_supportEnergy_univ χ
  have hcard : (Nat.card G : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < Nat.card G := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
    exact hpos.ne'
  calc
    Section7.supportEnergy Set.univ χ =
        (Nat.card G : ℝ) * ((Nat.card G : ℝ)⁻¹ * Section7.supportEnergy Set.univ χ) := by
      field_simp [hcard]
    _ = (Nat.card G : ℝ) * Section5.cfNormSq χ := by rw [← h]

public theorem section13_supportEnergy_univ_div_card_eq_cfNormSq
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G) :
    Section7.supportEnergy Set.univ χ / (Nat.card G : ℝ) = Section5.cfNormSq χ := by
  rw [section13_supportEnergy_univ_eq_card_mul_cfNormSq]
  have hG : (Nat.card G : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < Nat.card G := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
    exact hpos.ne'
  field_simp [hG]

public theorem section13_one_le_normSq_one_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    1 ≤ Complex.normSq (χ 1) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμ_bound : 1 ≤ Complex.normSq (μ 1) := by
    rcases hμ with ⟨n, ρ, hρ, rfl⟩
    have hdeg_ne : Section1.degree ρ.character ≠ 0 :=
      Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup ρ.character
        ⟨n, ρ, hρ, rfl⟩
    have hfin_ne : Module.finrank ℂ (Fin n → ℂ) ≠ 0 := by
      intro hzero
      apply hdeg_ne
      simp [Section1.degree_representation_character ρ, hzero]
    have hfin_ge : (1 : ℝ) ≤ (Module.finrank ℂ (Fin n → ℂ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hfin_ne))
    have hval : ρ.character 1 = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
      calc
        ρ.character 1 = Section1.degree ρ.character :=
          (Section1.degree_apply ρ.character).symm
        _ = (Module.finrank ℂ (Fin n → ℂ) : ℂ) :=
          Section1.degree_representation_character ρ
    rw [hval, Complex.normSq_natCast]
    nlinarith
  rcases hε with rfl | rfl
  · simpa using hμ_bound
  · simpa using hμ_bound

public theorem section13_scalarProduct_self_of_irreducibleCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

public theorem section13_isClassFunction_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hμ with ⟨n, ρ, _hρ, rfl⟩
  rcases hε with rfl | rfl
  · intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  · intro x g
    simpa [Pi.smul_apply, mul_assoc] using Representation.char_conj (ρ := ρ) g x

public theorem section13_complementIn_of_normal_isComplement'
    {G : Type u} [Group G] [Finite G]
    {H K L : Subgroup G}
    (hKL : section12ComplementIn H K L) (hKnorm : section10NormalIn K H) :
    (L.subgroupOf H).IsComplement' (K.subgroupOf H) := by
  rcases hKL with ⟨hKH, hLH, hHsup, hdisj⟩
  have hsup_local : L.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
    calc
      L.subgroupOf H ⊔ K.subgroupOf H = (L ⊔ K).subgroupOf H := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := H) hLH hKH
      _ = ⊤ := by
        rw [sup_comm, hHsup]
        simp
  haveI : (K.subgroupOf H).Normal := hKnorm.2
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf H) (K.subgroupOf H)).symm

public theorem section13_complementIn_left_hallSubgroupOf_of_right_hallSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {H K L : Subgroup G}
    (hcomp : section12ComplementIn H K L)
    (hKnorm : section10NormalIn K H)
    (hLHall : section16HallSubgroupOf L H) :
    section16HallSubgroupOf K H := by
  classical
  refine ⟨hcomp.1, ?_⟩
  letI : (K.subgroupOf H).Normal := hKnorm.2
  have hcomp' : (L.subgroupOf H).IsComplement' (K.subgroupOf H) :=
    section13_complementIn_of_normal_isComplement' hcomp hKnorm
  rcases hcomp with ⟨hKH, _hLH, _hsup, _hdisj⟩
  rcases hLHall with ⟨_hLH, hLHallSub⟩
  refine isHallSubgroup_of (G := H) (π := subgroupPrimeSet K)
    (H := K.subgroupOf H) ?_ ?_
  · intro p hpK
    have hcardK : Nat.card (K.subgroupOf H) = Nat.card K :=
      natCard_subgroupOf_eq K H hKH
    rw [hcardK] at hpK
    exact hpK
  · intro p hpK hpidxK
    have hpLcard : p.val ∣ Nat.card (L.subgroupOf H) := by
      simpa [hcomp'.index_eq_card] using hpidxK
    have hpLπ : p ∈ subgroupPrimeSet L :=
      hLHallSub.p_in_pi_of_p_dvd_card p hpLcard
    have hpKcard : p.val ∣ Nat.card (K.subgroupOf H) := by
      have hcardK : Nat.card (K.subgroupOf H) = Nat.card K :=
        natCard_subgroupOf_eq K H hKH
      rw [hcardK]
      exact hpK
    have hpLidx : p.val ∣ (L.subgroupOf H).index := by
      simpa [hcomp'.symm.index_eq_card] using hpKcard
    exact (hLHallSub.p_in_pi_of_p_dvd_index p hpLidx) hpLπ

public theorem section13_complementIn_right_hallSubgroupOf_of_left_hallSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {H K L : Subgroup G}
    (hcomp : section12ComplementIn H K L)
    (hKnorm : section10NormalIn K H)
    (hKHall : section16HallSubgroupOf K H) :
    section16HallSubgroupOf L H := by
  classical
  letI : (K.subgroupOf H).Normal := hKnorm.2
  rcases hcomp with ⟨hKH, hLH, hHsup, hdisj⟩
  have hcomp' : (L.subgroupOf H).IsComplement' (K.subgroupOf H) := by
    have hsup_local : L.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
      calc
        L.subgroupOf H ⊔ K.subgroupOf H = (L ⊔ K).subgroupOf H := by
          symm
          exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := H) hLH hKH
        _ = ⊤ := by
          rw [sup_comm, hHsup]
          simp
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxL hxK
      apply Subtype.ext
      exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
        by simpa [Subgroup.mem_subgroupOf] using hxL⟩
    · simpa [hsup_local] using
        (Subgroup.mul_normal (L.subgroupOf H) (K.subgroupOf H)).symm
  rcases hKHall with ⟨_hKH, hKHallSub⟩
  refine ⟨hLH, ?_⟩
  refine isHallSubgroup_of (G := H) (π := subgroupPrimeSet L)
    (H := L.subgroupOf H) ?_ ?_
  · intro p hpL
    have hcardL : Nat.card (L.subgroupOf H) = Nat.card L :=
      natCard_subgroupOf_eq L H hLH
    change p.val ∣ Nat.card L
    exact hcardL ▸ hpL
  · intro p hpL hpidxL
    have hpKcard : p.val ∣ Nat.card (K.subgroupOf H) := by
      simpa [hcomp'.symm.index_eq_card] using hpidxL
    have hpKπ : p ∈ subgroupPrimeSet K :=
      hKHallSub.p_in_pi_of_p_dvd_card p hpKcard
    have hpLcard : p.val ∣ Nat.card (L.subgroupOf H) := by
      have hcardL : Nat.card (L.subgroupOf H) = Nat.card L :=
        natCard_subgroupOf_eq L H hLH
      change p.val ∣ Nat.card L at hpL
      exact hcardL.symm ▸ hpL
    have hpKidx : p.val ∣ (K.subgroupOf H).index := by
      simpa [hcomp'.index_eq_card] using hpLcard
    exact (hKHallSub.p_in_pi_of_p_dvd_index p hpKidx) hpKπ

public theorem section13_hallSubgroup_in_intermediate_of_hall_overgroup
    {G : Type u} [Group G] [Finite G]
    {H D M : Subgroup G}
    (hHD : H ≤ D) (hDM : D ≤ M)
    (hHallHM : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M)) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D) := by
  classical
  let Dsub : Subgroup M := D.subgroupOf M
  have hHcardM : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M (hHD.trans hDM)
  have hHcardD : Nat.card (H.subgroupOf D) = Nat.card H :=
    natCard_subgroupOf_eq H D hHD
  have hHsub_le_Dsub : H.subgroupOf M ≤ Dsub := by
    intro x hx
    exact hHD hx
  refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet H)
    (H := H.subgroupOf D) ?_ ?_
  · intro p hp
    have hpH : p.val ∣ Nat.card H := hHcardD ▸ hp
    have hpHM : p.val ∣ Nat.card (H.subgroupOf M) := hHcardM.symm ▸ hpH
    exact hHallHM.p_in_pi_of_p_dvd_card p hpHM
  · intro p hpπ hpidx
    have hrel_eq :
        (H.subgroupOf D).index = (H.subgroupOf M).relIndex Dsub := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := H) (K := D) (L := M) hDM
      simpa [Dsub, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (H.subgroupOf D).index ∣ (H.subgroupOf M).index := by
      have hrel_dvd :
          (H.subgroupOf M).relIndex Dsub ∣ (H.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hHsub_le_Dsub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallHM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

public theorem section13_hallSubgroup_in_overgroup_of_hall_intermediate
    {G : Type u} [Group G] [Finite G]
    {H D M : Subgroup G}
    (hHD : H ≤ D) (hDM : D ≤ M)
    (hHallHD : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D))
    (hHallDM : IsHallSubgroup (subgroupPrimeSet D) (D.subgroupOf M)) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M) := by
  classical
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet H)
    (H := H.subgroupOf M) ?_ ?_
  · intro p hp
    have hcardM : Nat.card (H.subgroupOf M) = Nat.card H :=
      natCard_subgroupOf_eq H M (hHD.trans hDM)
    change p.val ∣ Nat.card H
    exact hcardM ▸ hp
  · intro p hpH hpidxM
    let Dsub : Subgroup M := D.subgroupOf M
    have hHsubM_le_Dsub : H.subgroupOf M ≤ Dsub := by
      intro x hx
      exact hHD hx
    have hrel_eq : (H.subgroupOf M).relIndex Dsub = (H.subgroupOf D).index := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := H) (K := D) (L := M) hDM
      simpa [Dsub, Subgroup.relIndex] using hsub
    have hidx_eq : (H.subgroupOf M).index =
        (H.subgroupOf D).index * (D.subgroupOf M).index := by
      calc
        (H.subgroupOf M).index =
            (H.subgroupOf M).relIndex Dsub * Dsub.index := by
          exact (Subgroup.relIndex_mul_index hHsubM_le_Dsub).symm
        _ = (H.subgroupOf D).index * (D.subgroupOf M).index := by
          rw [hrel_eq]
    have hpProd : p.val ∣ (H.subgroupOf D).index * (D.subgroupOf M).index := by
      simpa [hidx_eq] using hpidxM
    rcases (p.property.dvd_mul).mp hpProd with hpHD | hpDMidx
    · exact (hHallHD.p_in_pi_of_p_dvd_index p hpHD) hpH
    · have hpHcard : p.val ∣ Nat.card H := by
        simpa [subgroupPrimeSet] using hpH
      have hpD : p ∈ subgroupPrimeSet D :=
        hpHcard.trans (Subgroup.card_dvd_of_le hHD)
      exact (hHallDM.p_in_pi_of_p_dvd_index p hpDMidx) hpD

public theorem section13_card_eq_mul_of_complementIn_normal
    {G : Type u} [Group G] [Finite G]
    {H K L : Subgroup G}
    (hKL : section12ComplementIn H K L) (hKnorm : section10NormalIn K H) :
    Nat.card H = Nat.card K * Nat.card L := by
  rcases hKL with ⟨hKH, hLH, hHsup, hdisj⟩
  have hKL' : section12ComplementIn H K L := ⟨hKH, hLH, hHsup, hdisj⟩
  have hcomp := section13_complementIn_of_normal_isComplement' hKL' hKnorm
  have hmul := hcomp.card_mul
  rw [section12_card_subgroupOf_eq hLH, section12_card_subgroupOf_eq hKH] at hmul
  simpa [Nat.mul_comm] using hmul.symm

public theorem section13_mf_normalIn_ambientDerived_of_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePDefinitionData M MF U W1 W2) :
    section10NormalIn MF (ambientDerivedSubgroup M) := by
  rcases htype with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUle, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hMF with ⟨⟨hMFM, hMFNormalM, _hMFnil, _hMFHall⟩, _hmax⟩
  have hMFDer : MF ≤ ambientDerivedSubgroup M := hDercomp.1
  refine ⟨hMFDer, ?_⟩
  have hDerM : ambientDerivedSubgroup M ≤ M := section12_ambientDerivedSubgroup_le
  have hM_le_norm : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFNormalM
  have hDer_le_norm : ambientDerivedSubgroup M ≤ Subgroup.normalizer (MF : Set G) :=
    hDerM.trans hM_le_norm
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFDer).2 hDer_le_norm

public theorem section13_smax_card_formula_of_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hP_card : Nat.card P = p ^ q) :
    Nat.card Smax = (p ^ q) * (u * c) * q := by
  rcases hsource with
    ⟨_hcaseB, htypeS, _htypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have htypeSOrig := htypeS
  rcases htypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hScomp, _hUle, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup Smax) Smax :=
    section12_normalIn_ambientDerivedSubgroup
  have hS_card : Nat.card Smax = Nat.card (ambientDerivedSubgroup Smax) * Nat.card W1 :=
    section13_card_eq_mul_of_complementIn_normal hScomp hDer_norm
  have hP_norm_der : section10NormalIn P (ambientDerivedSubgroup Smax) :=
    section13_mf_normalIn_ambientDerived_of_typeP (M := Smax) (MF := P)
      (U := U) (W1 := W1) (W2 := W2) htypeSOrig
  have hDer_card : Nat.card (ambientDerivedSubgroup Smax) = Nat.card P * Nat.card U :=
    section13_card_eq_mul_of_complementIn_normal hDercomp hP_norm_der
  rw [hS_card, hDer_card, hP_card, hU_card, ← hq_card]

public theorem section13_tmax_card_formula_of_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hQ_card : Nat.card Q = q ^ p)
    (hV_card : Nat.card V = v) :
    Nat.card Tmax = p * (q ^ p) * v := by
  rcases hsource with
    ⟨_hcaseB, _htypeS, htypeT, hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have htypeTOrig := htypeT
  rcases htypeT with
    ⟨_hMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, _hVle, _hVnil, _hW2norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW1le, _hW1cyc,
      _hW1ne, _hcent, _hnorm⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup Tmax) Tmax :=
    section12_normalIn_ambientDerivedSubgroup
  have hT_card : Nat.card Tmax = Nat.card (ambientDerivedSubgroup Tmax) * Nat.card W2 :=
    section13_card_eq_mul_of_complementIn_normal hTcomp hDer_norm
  have hQ_norm_der : section10NormalIn Q (ambientDerivedSubgroup Tmax) :=
    section13_mf_normalIn_ambientDerived_of_typeP (M := Tmax) (MF := Q)
      (U := V) (W1 := W2) (W2 := W1) htypeTOrig
  have hDer_card : Nat.card (ambientDerivedSubgroup Tmax) = Nat.card Q * Nat.card V :=
    section13_card_eq_mul_of_complementIn_normal hDercomp hQ_norm_der
  rw [hT_card, hDer_card, hQ_card, hV_card, ← hp_card]
  ring

public theorem section13_tderiv_card_formula_of_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hQ_card : Nat.card Q = q ^ p)
    (hV_card : Nat.card V = v) :
    Nat.card (ambientDerivedSubgroup Tmax) = (q ^ p) * v := by
  rcases hsource with
    ⟨_hcaseB, _htypeS, htypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have htypeTOrig := htypeT
  rcases htypeT with
    ⟨_hMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVle, _hVnil, _hW2norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW1le, _hW1cyc,
      _hW1ne, _hcent, _hnorm⟩
  have hQ_norm_der : section10NormalIn Q (ambientDerivedSubgroup Tmax) :=
    section13_mf_normalIn_ambientDerived_of_typeP (M := Tmax) (MF := Q)
      (U := V) (W1 := W2) (W2 := W1) htypeTOrig
  have hDer_card : Nat.card (ambientDerivedSubgroup Tmax) = Nat.card Q * Nat.card V :=
    section13_card_eq_mul_of_complementIn_normal hDercomp hQ_norm_der
  rw [hDer_card, hQ_card, hV_card]

public theorem section13_normSq_one_eq_of_degree_nat_mul
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} {a b : ℕ}
    (hdeg : Section1.degree χ = (a * b : ℂ)) :
    Complex.normSq (χ 1) = ((a * b : ℕ) : ℝ) * ((a * b : ℕ) : ℝ) := by
  rw [← Section1.degree_apply χ, hdeg]
  rw [Complex.normSq_mul, Complex.normSq_natCast, Complex.normSq_natCast]
  norm_num [Nat.cast_mul]
  ring

public theorem section13_natCard_puncturedSubgroupSet
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    Nat.card (Section7.puncturedSubgroupSet H) = Nat.card H - 1 := by
  classical
  let e : Section7.puncturedSubgroupSet H ≃ {h : H // h ≠ 1} :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simpa using x.2.2⟩
      invFun := fun h => ⟨h.1.1, h.1.2, by simpa using h.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro h; rfl }
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl (fun h : H => h = 1)]
  simp

public theorem section13_real_geom_quotient_cast
    {p q : ℕ} (hq1 : 1 < q) :
    (((q ^ p - 1) / (q - 1) : ℕ) : ℝ) =
      ((q : ℝ) ^ p - 1) / ((q - 1 : ℕ) : ℝ) := by
  have hqsub_pos : 0 < q - 1 := Nat.sub_pos_of_lt hq1
  have hqsubR : ((q - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqsub_pos.ne'
  have hdvd : q - 1 ∣ q ^ p - 1 := Nat.sub_one_dvd_pow_sub_one q p
  have hqpos : 0 < q := by omega
  have hone_le_pow : 1 ≤ q ^ p := Nat.one_le_pow p q hqpos
  rw [Nat.cast_div hdvd hqsubR]
  rw [Nat.cast_sub hone_le_pow, Nat.cast_sub hq1.le]
  norm_num

public theorem section13_tTerm_substitution_of_v
    {p q : ℕ} {v : ℝ}
    (hp : 0 < p) (hq1 : 1 < q)
    (hv : v = ((q : ℝ) ^ p - 1) / ((q - 1 : ℕ) : ℝ)) :
    1 / (p : ℝ) - v / ((p : ℝ) * ((q : ℝ) ^ p)) =
      1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
        1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqsub_pos : 0 < q - 1 := Nat.sub_pos_of_lt hq1
  have hqsubR : ((q - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqsub_pos.ne'
  have hqpos : 0 < q := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hqpow : (q : ℝ) ^ p ≠ 0 := pow_ne_zero p hqR
  rw [hv]
  field_simp [hpR, hqsubR, hqpow]
  ring

public theorem section13_qTerm_substitution_of_v
    {p q : ℕ} {v : ℝ}
    (hp : 0 < p) (hq1 : 1 < q)
    (hv : v = ((q : ℝ) ^ p - 1) / ((q - 1 : ℕ) : ℝ)) :
    (((q : ℝ) ^ p - 1) / ((p : ℝ) * ((q : ℝ) ^ p) * v)) =
      ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqsub_pos : 0 < q - 1 := Nat.sub_pos_of_lt hq1
  have hqsubR : ((q - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqsub_pos.ne'
  have hqpos : 0 < q := by omega
  have hqRpos : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqR : (q : ℝ) ≠ 0 := hqRpos.ne'
  have hqpow : (q : ℝ) ^ p ≠ 0 := pow_ne_zero p hqR
  have hqpow_gt_one : (1 : ℝ) < (q : ℝ) ^ p :=
    one_lt_pow₀ (by exact_mod_cast hq1) hp.ne'
  have hnum : (q : ℝ) ^ p - 1 ≠ 0 := by linarith
  rw [hv]
  field_simp [hpR, hqpow, hqsubR, hnum]

public theorem section13_lratio_of_card_formula
    {p q u c sCard : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hc : 0 < c)
    (hsCard : sCard = (p ^ q) * (u * c) * q) :
    (((u * q : ℕ) : ℝ) * ((u * q : ℕ) : ℝ)) / (sCard : ℝ) =
      ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [hsCard]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hpR, hqR, huR, hcR]

public theorem section13_tSourceTerm_of_card_formula
    {p q v tCard tDerivCard : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hvpos : 0 < v)
    (hTcard : tCard = p * (q ^ p) * v)
    (hTderiv : tDerivCard = (q ^ p) * v) :
    (((tDerivCard : ℝ) - (v : ℝ) ^ 2) / (tCard : ℝ)) =
      1 / (p : ℝ) - (v : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hvpos.ne'
  rw [hTcard, hTderiv]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hpR, hqR, hvR]

public theorem section13_qSharpTerm_of_tCard_formula
    {p q v tCard : ℕ}
    (hq : 0 < q)
    (hTcard : tCard = p * (q ^ p) * v) :
    (((q ^ p - 1 : ℕ) : ℝ) / (tCard : ℝ)) =
      (((q : ℝ) ^ p - 1) / ((p : ℝ) * ((q : ℝ) ^ p) * (v : ℝ))) := by
  have hone_le_pow : 1 ≤ q ^ p := Nat.one_le_pow p q hq
  rw [hTcard]
  rw [Nat.cast_sub hone_le_pow]
  norm_num [Nat.cast_mul, Nat.cast_pow]

@[expose] public def theorem_13_10_sourceEstimateRawFields
    (Gcard A B G0card Hsharp Lratio Tterm Qterm : ℝ) : Prop :=
  0 < Gcard ∧
    1 ≥ 1 / Gcard + A / Gcard + 1 - Lratio ∧
    1 ≥ 1 / Gcard + B / Gcard + Hsharp + Tterm ∧
    1 = 1 / Gcard + G0card / Gcard + Hsharp + Qterm ∧
    G0card ≤ A + B

@[expose] public def theorem_13_10_totalNormDecompositionData
    (Gcard A B G0card Hsharp Lratio Tterm Qterm : ℝ) : Prop :=
  1 ≥ 1 / Gcard + A / Gcard + 1 - Lratio ∧
    1 ≥ 1 / Gcard + B / Gcard + Hsharp + Tterm ∧
    1 = 1 / Gcard + G0card / Gcard + Hsharp + Qterm

public theorem section13_theorem_13_10_sourceEstimateRawFields_from_totalNormData
    {Gcard A B G0card Hsharp Lratio Tterm Qterm : ℝ}
    (hGpos : 0 < Gcard)
    (hdata : theorem_13_10_totalNormDecompositionData
      Gcard A B G0card Hsharp Lratio Tterm Qterm)
    (h9 : G0card ≤ A + B) :
    theorem_13_10_sourceEstimateRawFields
      Gcard A B G0card Hsharp Lratio Tterm Qterm := by
  rcases hdata with ⟨h1, h2, h3⟩
  exact ⟨hGpos, h1, h2, h3, h9⟩

@[expose] public def theorem_13_10_cardinalFormulaEstimateData
    (p q u c : ℕ) : Prop :=
  ∃ Gcard A B G0card Hsharp Lratio Tterm Qterm : ℝ,
    0 < Gcard ∧
      1 ≥ 1 / Gcard + A / Gcard + 1 - Lratio ∧
      1 ≥ 1 / Gcard + B / Gcard + Hsharp + Tterm ∧
      1 = 1 / Gcard + G0card / Gcard + Hsharp + Qterm ∧
      G0card ≤ A + B ∧
      Lratio = ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) ∧
      Tterm =
        1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) ∧
      Qterm = ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p))

public theorem section13_theorem_13_10_cardinalFormulaEstimateData_from_rawFields
    {p q u c : ℕ} {Gcard A B G0card Hsharp Lratio Tterm Qterm : ℝ}
    (hraw : theorem_13_10_sourceEstimateRawFields
      Gcard A B G0card Hsharp Lratio Tterm Qterm)
    (hLratio :
      Lratio = ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q))
    (hTterm :
      Tterm =
        1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)))
    (hQterm :
      Qterm = ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p))) :
    theorem_13_10_cardinalFormulaEstimateData p q u c := by
  rcases hraw with ⟨hGpos, h1, h2, h3, h9⟩
  exact ⟨Gcard, A, B, G0card, Hsharp, Lratio, Tterm, Qterm,
    hGpos, h1, h2, h3, h9, hLratio, hTterm, hQterm⟩

public theorem section13_theorem_13_10_strictComparison_from_estimates
    {Gcard A B G0card Hsharp Lratio Tterm Qterm : ℝ}
    (hGpos : 0 < Gcard)
    (h1 : 1 ≥ 1 / Gcard + A / Gcard + 1 - Lratio)
    (h2 : 1 ≥ 1 / Gcard + B / Gcard + Hsharp + Tterm)
    (h3 : 1 = 1 / Gcard + G0card / Gcard + Hsharp + Qterm)
    (h9 : G0card ≤ A + B) :
    Lratio > Tterm - Qterm := by
  have hGne : Gcard ≠ 0 := hGpos.ne'
  have h1sum : 1 / Gcard + A / Gcard ≤ Lratio := by
    linarith
  have h1' : (1 + A) / Gcard ≤ Lratio := by
    have hcast : (1 + A) / Gcard = 1 / Gcard + A / Gcard := by
      field_simp [hGne]
    rwa [hcast]
  have h2' : Tterm - Qterm ≤ (G0card - B) / Gcard := by
    have h3' : Hsharp = 1 - 1 / Gcard - G0card / Gcard - Qterm := by
      linarith
    rw [h3'] at h2
    have htmp : Tterm - Qterm ≤ G0card / Gcard - B / Gcard := by
      linarith
    have hcast : G0card / Gcard - B / Gcard = (G0card - B) / Gcard := by
      field_simp [hGne]
    rwa [← hcast]
  have h9' : (G0card - B) / Gcard ≤ A / Gcard := by
    have hsub : G0card - B ≤ A := by
      linarith
    exact div_le_div_of_nonneg_right hsub (le_of_lt hGpos)
  have hlt : A / Gcard < (1 + A) / Gcard := by
    have hone : (0 : ℝ) < 1 / Gcard := one_div_pos.mpr hGpos
    have hcast : (1 + A) / Gcard = A / Gcard + 1 / Gcard := by
      field_simp [hGne]
      ring
    rw [hcast]
    linarith
  calc
    Tterm - Qterm ≤ (G0card - B) / Gcard := h2'
    _ ≤ A / Gcard := h9'
    _ < (1 + A) / Gcard := hlt
    _ ≤ Lratio := h1'

public theorem section13_theorem_13_10_cardinalFormulaInequality_from_strictComparison
    {p q u c : ℕ} {Lratio Tterm Qterm : ℝ}
    (hstrict : Lratio > Tterm - Qterm)
    (hLratio :
      Lratio = ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q))
    (hTterm :
      Tterm =
        1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)))
    (hQterm :
      Qterm = ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p))) :
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
      (1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
        1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))) -
          ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
  rw [hLratio, hTterm, hQterm] at hstrict
  exact hstrict

public theorem section13_theorem_13_10_cardinalFormulaInequality_from_estimateData
    {p q u c : ℕ}
    (hdata : theorem_13_10_cardinalFormulaEstimateData p q u c) :
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
      (1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
        1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))) -
          ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
  rcases hdata with
    ⟨Gcard, A, B, G0card, Hsharp, Lratio, Tterm, Qterm, hGpos, h1,
      h2, h3, h9, hLratio, hTterm, hQterm⟩
  exact section13_theorem_13_10_cardinalFormulaInequality_from_strictComparison
    (section13_theorem_13_10_strictComparison_from_estimates hGpos h1 h2 h3 h9)
    hLratio hTterm hQterm

public theorem section13_theorem_13_10_rawSourceInequality_from_cardinalFormula
    {p q u c : ℕ}
    (hcard :
      ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
        (1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))) -
            ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p))) :
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
      1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) -
        ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := by
  linarith

public theorem section13_theorem_13_10_from_sourceEstimate
    {p q u c : ℕ} {m : ℝ}
    (hsource : theorem_13_10_sourceEstimate p q u c m) :
    (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ (q - 1)) / (q : ℝ) := by
  rcases hsource with ⟨hp, hq, hc, hineq⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hpRne : (p : ℝ) ≠ 0 := hpR.ne'
  have hqRne : (q : ℝ) ≠ 0 := hqR.ne'
  have hcRne : (c : ℝ) ≠ 0 := hcR.ne'
  have hpPowPos : (0 : ℝ) < (p : ℝ) ^ q := pow_pos hpR q
  have hscale_pos : (0 : ℝ) < (p : ℝ) ^ q / (q : ℝ) := div_pos hpPowPos hqR
  have hscaled := mul_lt_mul_of_pos_right hineq hscale_pos
  calc
    (u : ℝ) / (c : ℝ) =
        (((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q)) *
          (((p : ℝ) ^ q) / (q : ℝ)) := by
      field_simp [hpRne, hqRne, hcRne]
    _ > (m / (p : ℝ)) * (((p : ℝ) ^ q) / (q : ℝ)) := hscaled
    _ = (m * (p : ℝ) ^ (q - 1)) / (q : ℝ) := by
      have hqsucc : q = Nat.succ (q - 1) := by omega
      have hqcast : ((Nat.succ (q - 1) : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast hqsucc.symm
      conv_lhs => rw [hqsucc, pow_succ]
      field_simp [hpRne, hqRne]
      rw [hqcast]
end CFSG.Section13
