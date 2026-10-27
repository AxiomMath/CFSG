module

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_9
-/

noncomputable section

open scoped BigOperators Pointwise
open Polynomial

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.9) -/


private def theorem_13_9_EtaColumnModel
    {G : Type u}
    [Group G]
    (q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (ξ : Section1.ClassFunction G) : Prop :=
  ∃ b : ℕ, ξ = ((-1 : ℂ) ^ b) • (Finset.range q).sum (fun i => η i 1)


private def theorem_13_9_EtaColumnZeroRowAt
    {G : Type u}
    [Group G]
    (q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (x : G) : Prop :=
  ∀ i : ℕ, i < q → i ≠ 0 → (η i 0) x = 0


private def theorem_13_9_EtaColumnFirstColumnAt
    {G : Type u}
    [Group G]
    (q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (x : G) : Prop :=
  ∀ i : ℕ, i < q → i ≠ 0 → (η i 1) x = (η 0 1) x - 1


private def theorem_13_9_EtaColumnRowsAt
    {G : Type u}
    [Group G]
    (q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (x : G) : Prop :=
  theorem_13_9_EtaColumnZeroRowAt q η x ∧
    theorem_13_9_EtaColumnFirstColumnAt q η x


private theorem theorem_13_9_nonvanishing_eta_column_signed_model_row_of_signAlternative
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax : Subgroup G}
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (h1p : 1 < p)
    (halt : theorem_13_3_signAlternativeData p q (fun j => τS (μsum j)) η) :
    ∃ b j : ℕ, 0 < j ∧ j < p ∧
      τS (μsum j) = ((-1 : ℂ) ^ b) • (Finset.range q).sum (fun i => η i 1) := by
  rcases halt with hpos | hneg
  · refine ⟨0, 1, by norm_num, h1p, ?_⟩
    simpa using hpos 1 (by norm_num) h1p
  · rcases hneg with ⟨hp3, hpos⟩
    have h2p : 2 < p := by omega
    rcases hpos 2 (by norm_num) h2p with ⟨j', hset, hrow⟩
    have hj'_mem_right : j' ∈ ({1, 2} : Finset ℕ) := by
      rw [← hset]
      simp
    have hj' : j' = 1 := by
      have hj'_cases : j' = 1 ∨ j' = 2 := by simpa using hj'_mem_right
      rcases hj'_cases with h | h
      · exact h
      · have h1mem_left : 1 ∈ ({2, j'} : Finset ℕ) := by
          rw [hset]
          simp
        simp [h] at h1mem_left
    refine ⟨1, 2, by norm_num, h2p, ?_⟩
    simpa [hj'] using hrow

/- Checked wrapper obtaining the signed eta-column row from the source PF
`(13.3)` character-output package. -/
private theorem theorem_13_9_nonvanishing_eta_column_signed_model_row_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η) :
    ∃ b j : ℕ, 0 < j ∧ j < p ∧
      τ1 (μsum j) = ((-1 : ℂ) ^ b) • (Finset.range q).sum (fun i => η i 1) := by
  have h1p : 1 < p := by
    rcases hsource with
      ⟨hcaseB, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotationData⟩
    rcases hcaseB with
      ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
        _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
        _hSType, _hTType, _hmax⟩
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  exact theorem_13_9_nonvanishing_eta_column_signed_model_row_of_signAlternative
    τ1 p q μsum η h1p houtput.2

/- Checked induction-support wrapper: if a class function on `Smax` is supported
on the preimage of `H#`, then its induced class function is supported on the
ambient conjugates of `H#`. -/
private theorem theorem_13_9_inducedCFLinear_supportedOn_conjugates_of_supportedOn_preimage
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H : Subgroup G)
    (φ : Section1.ClassFunction Smax)
    (hφ : Section1.supportedOn φ
      (subgroupSetPreimage Smax (Section7.puncturedSubgroupSet H))) :
    Section1.supportedOn (Section1.inducedCFLinear Smax φ)
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) := by
  classical
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hg
  rw [Section1.inducedCFLinear_apply]
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      (∑ y : G,
        if hyS : y * g * y⁻¹ ∈ Smax then
          φ ⟨y * g * y⁻¹, hyS⟩
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y _hy
    by_cases hyS : y * g * y⁻¹ ∈ Smax
    · have hy_not_pre :
          (⟨y * g * y⁻¹, hyS⟩ : Smax) ∉
            subgroupSetPreimage Smax (Section7.puncturedSubgroupSet H) := by
        intro hy_pre
        have hyH : y * g * y⁻¹ ∈ Section7.puncturedSubgroupSet H := by
          simpa [subgroupSetPreimage] using hy_pre
        apply hg
        refine ⟨y * g * y⁻¹, hyH, y⁻¹, Set.mem_univ _, ?_⟩
        simp [mul_assoc]
      have hzero := hφ ⟨y * g * y⁻¹, hyS⟩ hy_not_pre
      simp [hyS, hzero]
    · simp [hyS]
  rw [hsum]
  simp

private theorem theorem_13_9_H_subgroupOf_Smax_normal_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    (H.subgroupOf Smax).Normal := by
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hptypeS
  have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
    simpa [hfit] using section8FittingSubgroup_normal_in Smax
  simpa [hH] using hPCnormal

private theorem theorem_13_9_supportedOn_H_of_inducedFromLinearCharacter
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H : Subgroup G)
    (χ : Section1.ClassFunction Smax)
    (hHnormal : (H.subgroupOf Smax).Normal)
    (hχ : inducedFromLinearCharacterForSection13 Smax H χ) :
    Section1.supportedOn χ (H.subgroupOf Smax : Set Smax) := by
  classical
  rcases hχ with ⟨_hHS, θ, _hθirr, _hθdeg, hχeq⟩
  rw [hχeq]
  letI : (H.subgroupOf Smax).Normal := hHnormal
  exact Section10.inducedCF_supportedOn_subgroup (H.subgroupOf Smax) θ

private theorem theorem_13_9_supportedOn_Hsharp_of_supportedOn_H_and_degree_eq
    {G : Type u}
    [Group G]
    (Smax H : Subgroup G)
    {φ ψ : Section1.ClassFunction Smax}
    (hφ : Section1.supportedOn φ (H.subgroupOf Smax : Set Smax))
    (hψ : Section1.supportedOn ψ (H.subgroupOf Smax : Set Smax))
    (hdeg : Section1.degree φ = Section1.degree ψ) :
    Section1.supportedOn (φ - ψ)
      (subgroupSetPreimage Smax (Section7.puncturedSubgroupSet H)) := by
  rw [Section1.supportedOn_iff] at hφ hψ ⊢
  intro x hx
  by_cases hxH : (x : G) ∈ H
  · have hxoneG : (x : G) = 1 := by
      by_contra hxne
      have hxneS : x ≠ 1 := by
        intro hxone
        exact hxne (by simpa using congrArg (fun y : Smax => (y : G)) hxone)
      exact hx (by
        simp [subgroupSetPreimage, Section7.puncturedSubgroupSet, hxH, hxneS])
    have hxone : x = 1 := Subtype.ext (by simpa using hxoneG)
    subst x
    change φ 1 - ψ 1 = 0
    simpa [Section1.degree_apply] using sub_eq_zero.mpr hdeg
  · have hxHsub : x ∉ (H.subgroupOf Smax : Set Smax) := by
      intro hxsub
      exact hxH (by simpa using (Subgroup.mem_subgroupOf.1 hxsub))
    simp [hφ x hxHsub, hψ x hxHsub]


private theorem theorem_13_9_nonvanishing_eta_column_row_difference_supportedOn_H_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hj0 : 0 < j)
    (hjp : j < p) :
    Section1.supportedOn (lam - μsum j)
      (subgroupSetPreimage Smax (Section7.puncturedSubgroupSet H)) := by
  rcases houtput.1 j hj0 hjp with
    ⟨_hμchar, hμdeg, hμlinearPC, _hμmem⟩
  rcases hhyp with ⟨_hG0, _hlam_mem, h6hyp⟩
  rcases h6hyp with ⟨hH, _hlam_irred, hlam_deg, hlam_linear, _hlamτ_eq⟩
  have hμlinearH : inducedFromLinearCharacterForSection13 Smax H (μsum j) := by
    simpa [hH] using hμlinearPC
  have hHnormal : (H.subgroupOf Smax).Normal :=
    theorem_13_9_H_subgroupOf_Smax_normal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hH
  have hlam_support :
      Section1.supportedOn lam (H.subgroupOf Smax : Set Smax) :=
    theorem_13_9_supportedOn_H_of_inducedFromLinearCharacter
      Smax H lam hHnormal hlam_linear
  have hμ_support :
      Section1.supportedOn (μsum j) (H.subgroupOf Smax : Set Smax) :=
    theorem_13_9_supportedOn_H_of_inducedFromLinearCharacter
      Smax H (μsum j) hHnormal hμlinearH
  have hdeg : Section1.degree lam = Section1.degree (μsum j) := by
    rw [hlam_deg, hμdeg]
  exact theorem_13_9_supportedOn_Hsharp_of_supportedOn_H_and_degree_eq
    Smax H hlam_support hμ_support hdeg


private theorem theorem_13_9_fitting_punctured_subset_centralizerUnion_of_typeP
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    section16NonidentityElements (section8FittingSubgroup M : Set G) ⊆
      Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF := by
  classical
  intro x hx
  rcases hx with ⟨hxF, hxne⟩
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      _hcompDU, hMFnotcyc, _hM2le, hFitEq, hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases hMF.1 with ⟨hMFM, hMFNormalM, _hMFnil, _hMFHallM⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  let C : Subgroup G := subgroupCentralizerIn M MF
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hFleM : section8FittingSubgroup M ≤ M := hFitLeD.trans hDleM
  have hCleM : C ≤ M := by
    intro y hy
    exact hy.1
  have hsupM :
      MF.subgroupOf M ⊔ C.subgroupOf M =
        (section8FittingSubgroup M).subgroupOf M := by
    calc
      MF.subgroupOf M ⊔ C.subgroupOf M = (MF ⊔ C).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := MF) (A' := C) (B := M) hMFM hCleM
      _ = (section8FittingSubgroup M).subgroupOf M := by
        rw [hFitEq]
  let xM : M := ⟨x, hFleM hxF⟩
  have hxSupM : xM ∈ MF.subgroupOf M ⊔ C.subgroupOf M := by
    rw [hsupM]
    exact hxF
  letI : (MF.subgroupOf M).Normal := hMFNormalM
  rcases (Subgroup.mem_sup_of_normal_left (s := MF.subgroupOf M)
      (t := C.subgroupOf M) (x := xM)).1 hxSupM with
    ⟨mM, hmMFsub, cM, hcCsub, hmulM⟩
  let m : G := mM
  let c : G := cM
  have hmMF : m ∈ MF := by
    simpa [m, Subgroup.mem_subgroupOf] using hmMFsub
  have hcC : c ∈ C := by
    simpa [c, C, Subgroup.mem_subgroupOf] using hcCsub
  have hmul : m * c = x := by
    simpa [m, c, xM] using congrArg Subtype.val hmulM
  have hxD : x ∈ D := hFitLeD hxF
  by_cases hmne : m = 1
  · have hMFne : MF ≠ ⊥ := by
      intro hbot
      exact hMFnotcyc (by subst hbot; infer_instance)
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hMFne with ⟨zMF, hzMFne⟩
    let z : G := zMF
    have hzMF : z ∈ MF := zMF.property
    have hzne : z ≠ 1 := by
      intro hz
      exact hzMFne (Subtype.ext hz)
    have hxc : x = c := by
      rw [← hmul, hmne, one_mul]
    have hcent : x ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hxc]
      exact (Subgroup.mem_centralizer_iff.mp hcC.2 z hzMF).symm
    refine ⟨z, ⟨hzMF, hzne⟩, ?_⟩
    exact ⟨by simpa [D, elementCentralizerIn] using And.intro hxD hcent, hxne⟩
  · have hcent_m : c * m = m * c :=
      (Subgroup.mem_centralizer_iff.mp hcC.2 m hmMF).symm
    have hxcent : x ∈ Subgroup.centralizer ({m} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hmul]
      calc
        (m * c) * m = m * (c * m) := by simp [mul_assoc]
        _ = m * (m * c) := by rw [hcent_m]
    refine ⟨m, ⟨hmMF, hmne⟩, ?_⟩
    exact ⟨by simpa [D, elementCentralizerIn] using And.intro hxD hxcent, hxne⟩


private theorem theorem_13_9_fitting_punctured_subset_typePFAZeroSet_source
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
    section16NonidentityElements (section8FittingSubgroup Smax : Set G) ⊆
      typePFAZeroSet Smax W1 W2 P := by
  intro x hx
  rw [typePFAZeroSet]
  exact Or.inl
    (theorem_13_9_fitting_punctured_subset_centralizerUnion_of_typeP
      (_hsource.2.1) hx)

/- Checked extraction of the PF `(13.9)` equality `H = F(Smax)` from
`H = P ⊔ C`, the source identity `C = C_U(P)`, and PF `(8.5.a)`. -/
private theorem theorem_13_9_H_eq_fitting_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    H = section8FittingSubgroup Smax := by
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
  calc
    H = P ⊔ C := hH
    _ = P ⊔ subgroupCentralizerIn U P := by rw [hC]
    _ = section8FittingSubgroup Smax := by
      exact (Section8.theorem_8_5_a Smax P U W1 W2 hptypeS).symm

/- Checked wrapper from the Fitting containment source theorem to the concrete
PF `(13.9)` subgroup `H = P ⊔ C`. -/
private theorem theorem_13_9_Hsharp_subset_typePFAZeroSet_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    Section7.puncturedSubgroupSet H ⊆ typePFAZeroSet Smax W1 W2 P := by
  rcases hhyp with
    ⟨_hG0, _hlam_mem, hH, _hlam_irred, _hlam_deg, _hlam_linear, _hlamτ_eq⟩
  have hHfit : H = section8FittingSubgroup Smax :=
    theorem_13_9_H_eq_fitting_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d hsource hH
  have hfit :
      section16NonidentityElements (section8FittingSubgroup Smax : Set G) ⊆
        typePFAZeroSet Smax W1 W2 P :=
    theorem_13_9_fitting_punctured_subset_typePFAZeroSet_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  intro x hx
  exact hfit (by
    simpa [Section7.puncturedSubgroupSet, section16NonidentityElements, hHfit] using hx)


private theorem theorem_13_9_nonvanishing_eta_column_row_difference_CFOn_AZero_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hj0 : 0 < j)
    (hjp : j < p) :
    Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) (lam - μsum j) := by
  rcases houtput.1 j hj0 hjp with
    ⟨hμchar, _hμdeg, _hμlin, _hμmem⟩
  rcases hhyp with ⟨hG0, hlam_mem, h6hyp⟩
  rcases h6hyp with ⟨hH, hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  have hhyp' :
      theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u :=
    ⟨hG0, hlam_mem, hH, hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  have hclass_lam : Section1.IsClassFunction lam :=
    Section1.isBookIrreducibleCharacter_isClassFunction lam
      (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hlam_irred)
  have hclass_mu : Section1.IsClassFunction (μsum j) :=
    Section1.isCharacter_isClassFunction (μsum j) hμchar
  constructor
  · unfold Section1.IsClassFunction at hclass_lam hclass_mu ⊢
    intro x g
    simp [hclass_lam x g, hclass_mu x g]
  · intro l hlA0
    have hsupport :
        Section1.supportedOn (lam - μsum j)
          (subgroupSetPreimage Smax (Section7.puncturedSubgroupSet H)) :=
      theorem_13_9_nonvanishing_eta_column_row_difference_supportedOn_H_source
        Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
        ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation
        hhyp' houtput hj0 hjp
    rw [Section1.supportedOn_iff] at hsupport
    apply hsupport l
    intro hlH
    exact hlA0
      (theorem_13_9_Hsharp_subset_typePFAZeroSet_source
        Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
        p q u v c d hsource hhyp'
        (by simpa [subgroupSetPreimage] using hlH))


private theorem theorem_13_9_nonvanishing_eta_column_row_difference_induced_eq_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hj0 : 0 < j)
    (hjp : j < p) :
    τS (lam - μsum j) = Section1.inducedCFLinear Smax (lam - μsum j) := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, hSTypeP, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hBetaSupportNorm, _hChoice, _hMin⟩
  have hCFOn :
      Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) (lam - μsum j) :=
    theorem_13_9_nonvanishing_eta_column_row_difference_CFOn_AZero_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d j hsourceOrig hnotation hhyp houtput hj0 hjp
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig with
    ⟨_hMF, _hType, _hTypeII, _hUcomm, _hFrob, _hPelem, _hPcard, _huBound,
      _hCoh, _hBookA0, hTauA0, _hNormU⟩
  exact hTauA0.2 (lam - μsum j) hCFOn


private theorem theorem_13_9_nonvanishing_eta_column_row_difference_support_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hj0 : 0 < j)
    (hjp : j < p) :
    Section1.supportedOn (τ1 (lam - μsum j))
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) := by
  have hlocal :
      Section1.supportedOn (lam - μsum j)
        (subgroupSetPreimage Smax (Section7.puncturedSubgroupSet H)) :=
    theorem_13_9_nonvanishing_eta_column_row_difference_supportedOn_H_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation hhyp houtput hj0 hjp
  have hind :
      τS (lam - μsum j) = Section1.inducedCFLinear Smax (lam - μsum j) :=
    theorem_13_9_nonvanishing_eta_column_row_difference_induced_eq_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation hhyp houtput hj0 hjp
  have hlam_mem : lam ∈ Sfam := hhyp.2.1
  have hμdata := houtput.1 j hj0 hjp
  have hμmem : μsum j ∈ Sfam := hμdata.2.2.2
  have hspan : Section5.integerSpan Sfam (lam - μsum j) :=
    Section5.integerSpan_sub
      (Section5.integerSpan_of_mem Sfam hlam_mem)
      (Section5.integerSpan_of_mem Sfam hμmem)
  have hspanOn : Section5.integerSpanOn Sfam Section5.puncturedSet
      (lam - μsum j) := by
    refine ⟨hspan, ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree lam - Section1.degree (μsum j) = 0
    rw [hhyp.2.2.2.2.1, hμdata.2.1]
    simp
  have hagree : τ1 (lam - μsum j) = τS (lam - μsum j) :=
    hcoh.2.2 (lam - μsum j) hspanOn
  rw [hagree, hind]
  exact theorem_13_9_inducedCFLinear_supportedOn_conjugates_of_supportedOn_preimage
    Smax H (lam - μsum j) hlocal


private theorem theorem_13_9_nonvanishing_eta_column_row_difference_vanishes_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hj0 : 0 < j)
    (hjp : j < p) :
    ∀ x : G, x ∈ G0 → (τ1 (lam - μsum j)) x = 0 := by
  intro x hx
  have hsupp :
      Section1.supportedOn (τ1 (lam - μsum j))
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) :=
    theorem_13_9_nonvanishing_eta_column_row_difference_support_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation hhyp hcoh houtput hj0 hjp
  rw [Section1.supportedOn_iff] at hsupp
  apply hsupp x
  rcases hhyp with ⟨hG0, _hlam_mem, _h6hyp⟩
  rw [theorem_13_9_G0Data] at hG0
  rw [hG0] at hx
  exact fun hxH => hx.2 (Or.inl hxH)


private theorem theorem_13_9_nonvanishing_eta_column_row_agreement_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hj0 : 0 < j)
    (hjp : j < p) :
    ∀ x : G, x ∈ G0 → lamτ x = (τ1 (μsum j)) x := by
  intro x hx
  rcases hhyp with ⟨hG0, hlam_mem, h6hyp⟩
  have hdiff : (τ1 (lam - μsum j)) x = 0 :=
    theorem_13_9_nonvanishing_eta_column_row_difference_vanishes_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation
      ⟨hG0, hlam_mem, h6hyp⟩ hcoh houtput hj0 hjp x hx
  rcases h6hyp with ⟨_hH, _hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  have hsub : (τ1 lam) x - (τ1 (μsum j)) x = 0 := by
    simpa [map_sub, Pi.sub_apply] using hdiff
  calc
    lamτ x = (τ1 lam) x := by rw [hlamτ_eq]
    _ = (τ1 (μsum j)) x := sub_eq_zero.mp hsub


private theorem theorem_13_9_nonvanishing_eta_column_signed_model_agreement_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η) :
    ∃ b : ℕ,
      ∀ x : G, x ∈ G0 →
        lamτ x = (((-1 : ℂ) ^ b) • (Finset.range q).sum (fun i => η i 1)) x := by
  rcases theorem_13_9_nonvanishing_eta_column_signed_model_row_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hhyp houtput with
    ⟨b, j, hj0, hjp, hrow⟩
  have hagreeRow :
      ∀ x : G, x ∈ G0 → lamτ x = (τ1 (μsum j)) x :=
    theorem_13_9_nonvanishing_eta_column_row_agreement_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation hhyp hcoh houtput hj0 hjp
  refine ⟨b, ?_⟩
  intro x hx
  calc
    lamτ x = (τ1 (μsum j)) x := hagreeRow x hx
    _ = (((-1 : ℂ) ^ b) • (Finset.range q).sum (fun i => η i 1)) x := by
      rw [hrow]


private theorem theorem_13_9_nonvanishing_eta_column_agreement_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η) :
    ∃ ξ : Section1.ClassFunction G,
      theorem_13_9_EtaColumnModel q η ξ ∧
        ∀ x : G, x ∈ G0 → lamτ x = ξ x := by
  rcases theorem_13_9_nonvanishing_eta_column_signed_model_agreement_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hhyp hcoh houtput with
    ⟨b, hagree⟩
  refine ⟨((-1 : ℂ) ^ b) • (Finset.range q).sum (fun i => η i 1), ?_, hagree⟩
  exact ⟨b, rfl⟩

private theorem theorem_13_9_q_prime_of_source
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
    Nat.Prime q := by
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with hcaseA | hcaseB
  · rcases hcaseA with
      ⟨_hBarU, _a, _h92, _hH0le, _hCentIn, _hpPrime, hqPrime,
        _hpdata, _hquot, _hcardQuot, _hadvd, _hinj⟩
    exact hqPrime
  · rcases hcaseB with
      ⟨_h92, _hH0le, _hCentIn, _hpPrime, hqPrime, _hpdata, _hquot,
        _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv,
        _hprimeField⟩
    exact hqPrime

private theorem theorem_13_9_zeroColumn_linearCharacter_right_eq_one
    {G : Type u}
    [Group G]
    [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I}
    (lin : W →* ℂˣ)
    (hlin : ω i j0 = fun w : W => (lin w : ℂ))
    (y : W2) :
    lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
      (MonoidHom.inr W1 W2 y)) = 1 := by
  apply Units.ext
  have hmem :
      (Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inr W1 W2 y) ∈ W2.subgroupOf W := by
    change
      (((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inr W1 W2 y) : W) : G) ∈ W2
    have hEq :
        (((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
            (MonoidHom.inr W1 W2 y) : W) : G) = y := by
      simpa using congrArg Subtype.val
        (Section3.internalDirectProductMulEquiv_apply_inr hIP y)
    rw [hEq]
    exact y.property
  have hker := hω.left_kernel i
    ⟨(Section3.internalDirectProductMulEquiv hIP).toMonoidHom
      (MonoidHom.inr W1 W2 y), hmem⟩
  have hval :
      ω i j0 ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
        (MonoidHom.inr W1 W2 y)) = 1 := by
    simpa [hω.degree_one i j0] using hker
  simpa [hlin] using hval

private theorem theorem_13_9_zeroColumn_linearCharacter_eq_leftComponent
    {G : Type u}
    [Group G]
    [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I}
    (lin : W →* ℂˣ)
    (hlin : ω i j0 = fun w : W => (lin w : ℂ))
    (w : W) :
    lin w =
      lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
        (MonoidHom.inl W1 W2
          (((Section3.internalDirectProductMulEquiv hIP).symm w).1))) := by
  let e : W1 × W2 ≃* W := Section3.internalDirectProductMulEquiv hIP
  let p : W1 × W2 := e.symm w
  have hp : MonoidHom.inl W1 W2 p.1 * MonoidHom.inr W1 W2 p.2 = p := by
    ext <;> simp [MonoidHom.inl_apply, MonoidHom.inr_apply]
  have hw :
      e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
          e.toMonoidHom (MonoidHom.inr W1 W2 p.2) = w := by
    calc
      e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
          e.toMonoidHom (MonoidHom.inr W1 W2 p.2) =
          e.toMonoidHom (MonoidHom.inl W1 W2 p.1 *
            MonoidHom.inr W1 W2 p.2) := by
            rw [map_mul]
      _ = e.toMonoidHom p := by rw [hp]
      _ = w := by
            change e p = w
            simp [p]
  have hright :
      lin (e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) = 1 := by
    simpa [e] using
      theorem_13_9_zeroColumn_linearCharacter_right_eq_one hIP hω lin hlin p.2
  calc
    lin w = lin (e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
        e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) := by rw [hw]
    _ = lin (e.toMonoidHom (MonoidHom.inl W1 W2 p.1)) *
        lin (e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) := by rw [map_mul]
    _ = lin (e.toMonoidHom (MonoidHom.inl W1 W2 p.1)) := by rw [hright, mul_one]
    _ = lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
        (MonoidHom.inl W1 W2
          (((Section3.internalDirectProductMulEquiv hIP).symm w).1))) := by
        rfl

private theorem theorem_13_9_zeroColumn_leftCharacter_ne_one
    {G : Type u}
    [Group G]
    [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I}
    (hi : i ≠ i0)
    (lin : W →* ℂˣ)
    (hlin : ω i j0 = fun w : W => (lin w : ℂ)) :
    lin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2)) ≠ 1 := by
  intro hres
  have hrow_principal : ω i j0 = Section1.principalCharacter W := by
    ext w
    have hleft :
        lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inl W1 W2
            (((Section3.internalDirectProductMulEquiv hIP).symm w).1))) = 1 := by
      have happ := congrArg
        (fun f : W1 →* ℂˣ =>
          f (((Section3.internalDirectProductMulEquiv hIP).symm w).1)) hres
      simpa using happ
    calc
      ω i j0 w = (lin w : ℂ) := by rw [hlin]
      _ =
          (lin ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
            (MonoidHom.inl W1 W2
              (((Section3.internalDirectProductMulEquiv hIP).symm w).1))) : ℂ) := by
            rw [theorem_13_9_zeroColumn_linearCharacter_eq_leftComponent hIP hω lin hlin w]
      _ = 1 := by
            exact congrArg (fun z : ℂˣ => (z : ℂ)) hleft
      _ = Section1.principalCharacter W w := rfl
  have hbase : ω i j0 = ω i0 j0 := by
    rw [hrow_principal, hω.principal]
  exact hi (hω.pairwise_eq hbase).1

private theorem theorem_13_9_exactCharacterValueOrder_of_leftCharacter
    {G : Type u}
    [Group G]
    [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {q : ℕ}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I}
    (lin : W →* ℂˣ)
    (hlin : ω i j0 = fun w : W => (lin w : ℂ))
    (horder : orderOf
      (lin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inl W1 W2))) = q)
    (hqpos : 0 < q) :
    Section3.exactCharacterValueOrder (ω i j0) q := by
  let leftHom : W1 →* ℂˣ :=
    lin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2))
  have hleft_order : orderOf leftHom = q := horder
  constructor
  · constructor
    · exact hqpos
    · intro w
      have hleft :
          lin w =
            leftHom (((Section3.internalDirectProductMulEquiv hIP).symm w).1) := by
        simpa [leftHom] using
          theorem_13_9_zeroColumn_linearCharacter_eq_leftComponent hIP hω lin hlin w
      have hpowLeft : leftHom ^ q = 1 := by
        rw [← hleft_order]
        exact pow_orderOf_eq_one leftHom
      have hval := congrArg
        (fun f : W1 →* ℂˣ => f (((Section3.internalDirectProductMulEquiv hIP).symm w).1))
        hpowLeft
      calc
        (ω i j0 w) ^ q = ((lin w : ℂ)) ^ q := by rw [hlin]
        _ = ((leftHom (((Section3.internalDirectProductMulEquiv hIP).symm w).1) : ℂ)) ^ q := by
              rw [hleft]
        _ = 1 := by
              simpa [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] using
                congrArg (fun z : ℂˣ => (z : ℂ)) hval
  · intro b hb
    have hpowLeft : leftHom ^ b = 1 := by
      ext x
      have hval := hb.2
        ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom
          (MonoidHom.inl W1 W2 x))
      simpa [leftHom, hlin, Units.val_pow_eq_pow_val] using hval
    rw [← hleft_order]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpowLeft

private theorem theorem_13_9_classFunctionValueZPow_of_leftCharacter_zpow
    {G : Type u}
    [Group G]
    [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {ibase itarget : I}
    {k : ℤ}
    (base target : W →* ℂˣ)
    (hbase : ω ibase j0 = fun w : W => (base w : ℂ))
    (htarget : ω itarget j0 = fun w : W => (target w : ℂ))
    (hres :
      target.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inl W1 W2)) =
        (base.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
          (MonoidHom.inl W1 W2))) ^ k) :
    Section3.classFunctionValueZPow (ω ibase j0) (ω itarget j0) k := by
  let leftBase : W1 →* ℂˣ :=
    base.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2))
  let leftTarget : W1 →* ℂˣ :=
    target.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2))
  have hres' : leftTarget = leftBase ^ k := by
    simpa [leftBase, leftTarget] using hres
  intro w
  have hbase_left :
      base w = leftBase (((Section3.internalDirectProductMulEquiv hIP).symm w).1) := by
    simpa [leftBase] using
      theorem_13_9_zeroColumn_linearCharacter_eq_leftComponent hIP hω base hbase w
  have htarget_left :
      target w = leftTarget (((Section3.internalDirectProductMulEquiv hIP).symm w).1) := by
    simpa [leftTarget] using
      theorem_13_9_zeroColumn_linearCharacter_eq_leftComponent hIP hω target htarget w
  have htarget_pow :
      target w = base w ^ k := by
    calc
      target w = leftTarget (((Section3.internalDirectProductMulEquiv hIP).symm w).1) :=
        htarget_left
      _ = (leftBase ^ k) (((Section3.internalDirectProductMulEquiv hIP).symm w).1) := by
        rw [hres']
      _ = leftBase (((Section3.internalDirectProductMulEquiv hIP).symm w).1) ^ k := by
        simp [MonoidHom.zpow_apply]
      _ = base w ^ k := by rw [hbase_left]
  calc
    ω itarget j0 w = (target w : ℂ) := by rw [htarget]
    _ = ((base w ^ k : ℂˣ) : ℂ) := by rw [htarget_pow]
    _ = ((base w : ℂ) ^ k) := by rw [Units.val_zpow_eq_zpow_val]
    _ = (ω ibase j0 w) ^ k := by rw [hbase]


private theorem theorem_13_9_omegaSystem_prime_zero_column_row_power_source
    {G : Type u}
    [Group G]
    [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hqprime : Nat.Prime q)
    (hqpos : 0 < q)
    (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin) :
    ∀ i : Fin q, i ≠ ⟨0, hqpos⟩ →
      ∃ k : ℤ,
        Section3.exactCharacterValueOrder
            (ωFin ⟨1, hqprime.one_lt⟩ ⟨0, hppos⟩) q ∧
          IsCoprime k (q : ℤ) ∧
    Section3.classFunctionValueZPow
              (ωFin ⟨1, hqprime.one_lt⟩ ⟨0, hppos⟩)
              (ωFin i ⟨0, hppos⟩) k := by
  classical
  rcases h31 with ⟨hW1le, _hW2le, hIP, _hcycW, _hodd, _hcard1, _hcard2, _hTI⟩
  intro i hi0
  have hcycW1 : IsCyclic W1 := Subgroup.isCyclic_of_le hW1le
  letI : CommGroup W1 := IsCyclic.commGroup
  letI : Fintype (W1 →* ℂˣ) := by
    let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity W1 ℂ).some
    exact Fintype.ofEquiv W1 e.toEquiv.symm
  have hcardW1 : Nat.card W1 = q := by
    calc
      Nat.card W1 = Fintype.card (Fin q) := hωFin.card_left.symm
      _ = q := Fintype.card_fin q
  have hcardLin : Nat.card (W1 →* ℂˣ) = q := by
    calc
      Nat.card (W1 →* ℂˣ) = Nat.card W1 :=
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity W1 ℂ
      _ = q := hcardW1
  let iBase : Fin q := ⟨1, hqprime.one_lt⟩
  let jBase : Fin p := ⟨0, hppos⟩
  rcases Section1.exists_linearCharacter_of_irreducible_degree_one
      (hωFin.irreducible iBase jBase) (hωFin.degree_one iBase jBase) with
    ⟨baseLin, hbaseLin⟩
  rcases Section1.exists_linearCharacter_of_irreducible_degree_one
      (hωFin.irreducible i jBase) (hωFin.degree_one i jBase) with
    ⟨targetLin, htargetLin⟩
  let leftBase : W1 →* ℂˣ :=
    baseLin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2))
  let leftTarget : W1 →* ℂˣ :=
    targetLin.comp ((Section3.internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2))
  have hbase_ne : leftBase ≠ 1 := by
    exact theorem_13_9_zeroColumn_leftCharacter_ne_one hIP hωFin
      (show iBase ≠ ⟨0, hqpos⟩ by
        exact Fin.ne_of_val_ne (by simp [iBase]))
      baseLin hbaseLin
  have htarget_ne : leftTarget ≠ 1 := by
    exact theorem_13_9_zeroColumn_leftCharacter_ne_one hIP hωFin
      (i := i) hi0 targetLin htargetLin
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hleftBase_gen : ∀ χ : W1 →* ℂˣ, χ ∈ Subgroup.zpowers leftBase := by
    intro χ
    exact mem_zpowers_of_prime_card (G := W1 →* ℂˣ) (p := q) hcardLin hbase_ne
  have hleftBase_order : orderOf leftBase = q := by
    calc
      orderOf leftBase = Nat.card (W1 →* ℂˣ) :=
        orderOf_eq_card_of_forall_mem_zpowers hleftBase_gen
      _ = q := hcardLin
  have htarget_mem : leftTarget ∈ Subgroup.zpowers leftBase :=
    hleftBase_gen leftTarget
  rcases Subgroup.mem_zpowers_iff.mp htarget_mem with ⟨k, hkpow⟩
  have hbase_mem_target : leftBase ∈ Subgroup.zpowers leftTarget :=
    mem_zpowers_of_prime_card (G := W1 →* ℂˣ) (p := q) hcardLin htarget_ne
  have hbase_mem_power : leftBase ∈ Subgroup.zpowers (leftBase ^ k) := by
    simpa [hkpow] using hbase_mem_target
  have hk_gcd : k.gcd (orderOf leftBase : ℤ) = 1 :=
    mem_zpowers_zpow_iff.mp hbase_mem_power
  have hk_coprime_order : IsCoprime k (orderOf leftBase : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hk_gcd
  have hk_coprime : IsCoprime k (q : ℤ) := by
    simpa [hleftBase_order] using hk_coprime_order
  have horder :
      Section3.exactCharacterValueOrder
        (ωFin iBase jBase) q :=
    theorem_13_9_exactCharacterValueOrder_of_leftCharacter hIP hωFin
      baseLin hbaseLin hleftBase_order hqpos
  have hpow :
      Section3.classFunctionValueZPow (ωFin iBase jBase) (ωFin i jBase) k :=
    theorem_13_9_classFunctionValueZPow_of_leftCharacter_zpow hIP hωFin
      baseLin targetLin hbaseLin htargetLin (by
        simpa [leftBase, leftTarget] using hkpow.symm)
  exact ⟨k, horder, hk_coprime, hpow⟩


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_row_power_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D _H : Subgroup G)
    (_G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_lam : Section1.ClassFunction Smax)
    (_lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i : ℕ, i < q → i ≠ 0 →
      ∃ k : ℤ,
        Section3.exactCharacterValueOrder (ω 1 0) q ∧
          IsCoprime k (q : ℤ) ∧
            Section3.classFunctionValueZPow (ω 1 0) (ω i 0) k := by
  classical
  intro i hi hi0
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero, _hνzero,
      _hμind, _hνind, _hμsum, _hνsum⟩
  rcases hωData with ⟨h31, hqpos, hppos, ωFin, hωFin, hωeq⟩
  have hqprime : Nat.Prime q :=
    theorem_13_9_q_prime_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  let iFin : Fin q := ⟨i, hi⟩
  have hiFin0 : iFin ≠ ⟨0, hqpos⟩ := by
    intro h
    exact hi0 (congrArg Fin.val h)
  rcases theorem_13_9_omegaSystem_prime_zero_column_row_power_source
      (W1 := W1) (W2 := W2) (W := W) (p := p) (q := q)
      h31 hqprime hqpos hppos ωFin hωFin iFin hiFin0 with
    ⟨k, hkpack⟩
  have horder := hkpack.1
  have hk : IsCoprime k (q : ℤ) := hkpack.2.1
  have hpow := hkpack.2.2
  have h1q : 1 < q := hqprime.one_lt
  have hbase :
      ω 1 0 = ωFin ⟨1, h1q⟩ ⟨0, hppos⟩ :=
    hωeq 1 0 h1q hppos
  have htarget :
      ω i 0 = ωFin iFin ⟨0, hppos⟩ :=
    hωeq i 0 hi hppos
  refine ⟨k, ?_, hk, ?_⟩
  · simpa [hbase] using horder
  · intro g
    calc
      (ω i 0) g = (ωFin iFin ⟨0, hppos⟩) g := by
        rw [htarget]
      _ = (ωFin ⟨1, h1q⟩ ⟨0, hppos⟩ g) ^ k := hpow g
      _ = ((ω 1 0) g) ^ k := by
        rw [hbase]


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_row_galois_transport_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i : ℕ, i < q → i ≠ 0 →
      ∃ γ : Gal(ℂ/ℚ),
        η i 0 = Section3.classFunctionGaloisConjugate γ (η 1 0) := by
  classical
  intro i hi hi0
  have h1q : 1 < q := by omega
  rcases hnotation with
    ⟨hωData, hσmap, hη, hδ, hδ', hμirr, hνirr, hμzero, hνzero,
      hμind, hνind, hμsum, hνsum⟩
  rcases hωData with ⟨h31, hqpos, hppos, ωFin, hωFin, hωeq⟩
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hωFin σ hσmap with
    ⟨χ, horth, hsigned, h00, hInd, hσeq⟩
  have hσ_eq : σ = Section3.sigmaOfPF35 ωFin χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hqpos⟩) (j0 := ⟨0, hppos⟩)
      (ω := ωFin) (χ := χ) h31 hωFin hσeq
  have hroot : ∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e := by
    intro c b e he
    exact Section5.complex_galois_aut_pow_on_roots he
  have hB :
      Section3.proposition_3_9_statement_b_complex_galois
        (Section3.sigmaOfPF35 ωFin χ) :=
    Section3.proposition_3_9_b_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hqpos⟩) (j0 := ⟨0, hppos⟩)
      (ω := ωFin) (χ := χ) h31 hωFin horth hsigned h00 hInd hroot
  have hω10_irred : Section1.IsIrreducibleCharacterOnGroup (ω 1 0) := by
    rw [hωeq 1 0 h1q hppos]
    exact hωFin.irreducible ⟨1, h1q⟩ ⟨0, hppos⟩
  rcases theorem_13_9_nonvanishing_eta_column_zero_eta10_row_power_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource
      ⟨⟨h31, hqpos, hppos, ωFin, hωFin, hωeq⟩, hσmap, hη, hδ, hδ',
        hμirr, hνirr, hμzero, hνzero, hμind, hνind, hμsum, hνsum⟩
      i hi hi0 with
    ⟨k, horder, hk, hpow_row⟩
  rcases hB (ω' := ω 1 0) (a := q) (k := k) hω10_irred horder hk with
    ⟨ωk, _hωk_irred, hpow, γ, _hγ, hσγ, _hpoint⟩
  have hωk_eq : ωk = ω i 0 := by
    ext g
    rw [hpow g, hpow_row g]
  refine ⟨γ, ?_⟩
  calc
    η i 0 = σ (ω i 0) := hη i 0 hi hppos
    _ = σ ωk := by rw [hωk_eq]
    _ = Section3.sigmaOfPF35 ωFin χ ωk := by rw [hσ_eq]
    _ = Section3.classFunctionGaloisConjugate γ
          (Section3.sigmaOfPF35 ωFin χ (ω 1 0)) := hσγ
    _ = Section3.classFunctionGaloisConjugate γ (σ (ω 1 0)) := by rw [← hσ_eq]
    _ = Section3.classFunctionGaloisConjugate γ (η 1 0) := by rw [hη 1 0 h1q hppos]


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_zero_row_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (_hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (_hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x = 0 →
      theorem_13_9_EtaColumnZeroRowAt q η x := by
  intro x _hx _hξzero hηzero i hi hi0
  rcases theorem_13_9_nonvanishing_eta_column_zero_eta10_row_galois_transport_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      i hi hi0 with
    ⟨γ, hγ⟩
  rw [hγ]
  simp [Section3.classFunctionGaloisConjugate, hηzero]


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_cyclicTI_exclusion_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D _H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_lam : Section1.ClassFunction Smax)
    (_lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ x : G, x ∈ G0 → (η 1 0) x = 0 →
      x ∉ Section2.conjugateSet (Section3.cyclicTISet W1 W2 W) := by
  intro x _hx hηzero hxconj
  rcases hxconj with ⟨y, hyV, g, hconj⟩
  rcases hnotation with
    ⟨homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμ0, _hν0, _hμdiff, _hνdiff, _hμsum, _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, hp0, ωFin, hωFin, hωeq⟩
  rcases hσmap with
    ⟨_hIso, _hMapsVirtual, _hInd, hMapsClass, _hσprincipal, hAgree, _hDetect⟩
  have hq1 : 1 < q := by
    rcases hsource with
      ⟨hcaseB, _hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotationData⟩
    rcases hcaseB with
      ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
        _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
        _hSType, _hTType, _hmax⟩
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  let i1 : Fin q := ⟨1, hq1⟩
  let j0 : Fin p := ⟨0, hp0⟩
  have hω10_irred : Section1.IsIrreducibleCharacterOnGroup (ω 1 0) := by
    rw [hωeq 1 0 hq1 hp0]
    exact hωFin.irreducible i1 j0
  have hω10_class : Section1.IsClassFunction (ω 1 0) := by
    rw [hωeq 1 0 hq1 hp0]
    exact hωFin.is_class i1 j0
  have hω10_degree : Section1.degree (ω 1 0) = 1 := by
    rw [hωeq 1 0 hq1 hp0]
    exact hωFin.degree_one i1 j0
  have hη10_sigma : η 1 0 = σ (ω 1 0) := hη 1 0 hq1 hp0
  have hη10_class : Section1.IsClassFunction (η 1 0) := by
    rw [hη10_sigma]
    exact hMapsClass (ω 1 0) hω10_class
  have hxy : (η 1 0) x = (η 1 0) y := by
    rw [← hconj]
    simpa [Section2.conjBy] using hη10_class g y
  have hyzero : (η 1 0) y = 0 := by
    rwa [hxy] at hηzero
  have hyη :
      (η 1 0) y =
        (ω 1 0) ⟨y, Section3.cyclicTISet_subset W1 W2 W hyV⟩ := by
    rw [hη10_sigma]
    exact hAgree (ω 1 0) hω10_class y hyV
  rcases Section1.exists_linearCharacter_of_irreducible_degree_one
      hω10_irred hω10_degree with
    ⟨χ, hχ⟩
  have hyω_ne :
      (ω 1 0) ⟨y, Section3.cyclicTISet_subset W1 W2 W hyV⟩ ≠ 0 := by
    rw [hχ]
    exact Units.ne_zero (χ ⟨y, Section3.cyclicTISet_subset W1 W2 W hyV⟩)
  exact hyω_ne (by
    rw [← hyη]
    exact hyzero)


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_alpha_vanishes_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (_hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (_hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x = 0 →
      ∀ i : ℕ, i < q → i ≠ 0 →
        (σ (Section3.alphaIJ W 0 0 ω i 1)) x = 0 := by
  intro x hx _hξzero hηzero i hi _hi0
  have hsourcePackage := hsource
  have hnotationPackage := hnotation
  rcases hnotation with
    ⟨homegaData, hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμ0, _hν0, _hμdiff, _hνdiff, _hμsum, _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωeq⟩
  rcases hσmap with
    ⟨_hIso, _hMapsVirtual, hInd, _hMapsClass, _hσprincipal, _hAgree, _hDetect⟩
  have hxnot : x ∉ Section2.conjugateSet (Section3.cyclicTISet W1 W2 W) :=
    theorem_13_9_nonvanishing_eta_column_zero_eta10_cyclicTI_exclusion_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsourcePackage hnotationPackage
      x hx hηzero
  have hp1 : 1 < p := by
    rcases hsourcePackage with
      ⟨hcaseB, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotationData⟩
    rcases hcaseB with
      ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
        _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
        _hSType, _hTType, _hmax⟩
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp1
  have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  let iFin : Fin q := ⟨i, hi⟩
  let zeroQ : Fin q := ⟨0, hq0⟩
  let oneP : Fin p := ⟨1, hp1⟩
  let zeroP : Fin p := ⟨0, hp0⟩
  let alphaNat : Section1.ClassFunction W := Section3.alphaIJ W 0 0 ω i 1
  have halpha_eq :
      alphaNat = Section3.alphaIJ W zeroQ zeroP ωFin iFin oneP := by
    ext y
    simp [alphaNat, Section3.alphaIJ, iFin, zeroQ, oneP, zeroP,
      hωeq i 0 hi hp0, hωeq 0 1 hq0 hp1,
      hωeq i 1 hi hp1]
  have halphaCFOn :
      Section2.CFOn W (Section3.cyclicTISet W1 W2 W) alphaNat := by
    have hfin :
        Section2.CFOn W (Section3.cyclicTISet W1 W2 W)
          (Section3.alphaIJ W zeroQ zeroP ωFin iFin oneP) :=
      Section3.alphaIJ_CFOn_cyclicTISet W1 W2 W (Fin q) (Fin p)
        zeroQ zeroP ωFin hωFin iFin oneP
    simpa [halpha_eq]
      using hfin
  calc
    (σ (Section3.alphaIJ W 0 0 ω i 1)) x = (σ alphaNat) x := rfl
    _ = Section1.inducedCF W alphaNat x := by rw [hInd alphaNat halphaCFOn]
    _ = 0 :=
      Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
        W alphaNat halphaCFOn hxnot


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_first_column_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x = 0 →
      theorem_13_9_EtaColumnZeroRowAt q η x →
        theorem_13_9_EtaColumnFirstColumnAt q η x := by
  intro x hx hξzero hηzero hzeroRows i hi hi0
  have hnotationPackage := hnotation
  rcases hnotation with
    ⟨_homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμ0, _hν0, _hμdiff, _hνdiff, _hμsum, _hνsum⟩
  rcases hσmap with
    ⟨_hIso, _hMapsVirtual, _hInd, _hMapsClass, hσprincipal, _hAgree, _hDetect⟩
  have hp1 : 1 < p := by
    rcases hsource with
      ⟨hcaseB, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotationData⟩
    rcases hcaseB with
      ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
        _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
        _hSType, _hTType, _hmax⟩
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp1
  have hq0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hηi0 : η i 0 = σ (ω i 0) := hη i 0 hi hp0
  have hη01 : η 0 1 = σ (ω 0 1) := hη 0 1 hq0 hp1
  have hηi1 : η i 1 = σ (ω i 1) := hη i 1 hi hp1
  have hαzero :
      (σ (Section3.alphaIJ W 0 0 ω i 1)) x = 0 :=
    theorem_13_9_nonvanishing_eta_column_zero_eta10_alpha_vanishes_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource
      hnotationPackage
      ξ hξmodel hξeq x hx hξzero hηzero i hi hi0
  have hαeval :
      (σ (Section3.alphaIJ W 0 0 ω i 1)) x =
        1 - (η i 0) x - (η 0 1) x + (η i 1) x := by
    simp [Section3.alphaIJ, hσprincipal, hηi0, hη01, hηi1,
      Section1.principalCharacter_apply]
  have hηi0zero : (η i 0) x = 0 := hzeroRows i hi hi0
  rw [hαeval, hηi0zero] at hαzero
  linear_combination hαzero


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_rows_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x = 0 →
      theorem_13_9_EtaColumnRowsAt q η x := by
  intro x hx hξzero hηzero
  have hzero : theorem_13_9_EtaColumnZeroRowAt q η x :=
    theorem_13_9_nonvanishing_eta_column_zero_eta10_zero_row_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      ξ hξmodel hξeq x hx hξzero hηzero
  have hfirst : theorem_13_9_EtaColumnFirstColumnAt q η x :=
    theorem_13_9_nonvanishing_eta_column_zero_eta10_first_column_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      ξ hξmodel hξeq x hx hξzero hηzero hzero
  exact ⟨hzero, hfirst⟩


private theorem theorem_13_9_nonvanishing_eta_column_eta11_value_of_rows
    {G : Type u}
    [Group G]
    (q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (ξ : Section1.ClassFunction G)
    (x : G)
    (hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (hrows : theorem_13_9_EtaColumnRowsAt q η x)
    (hξzero : ξ x = 0)
    (h1q : 1 < q) :
    (η 1 1) x = -((q : ℂ)⁻¹) := by
  classical
  rcases hξmodel with ⟨b, rfl⟩
  rcases hrows with ⟨_hzeroRows, hfirstColumn⟩
  have hsign_ne : ((-1 : ℂ) ^ b) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsum_zero : ((Finset.range q).sum (fun i => η i 1)) x = 0 := by
    simpa using (mul_eq_zero.mp (by simpa using hξzero)).resolve_left hsign_ne
  have hsum_zero' : (Finset.range q).sum (fun i => (η i 1) x) = 0 := by
    simpa using hsum_zero
  have h0mem : 0 ∈ Finset.range q :=
    Finset.mem_range.mpr (Nat.zero_lt_of_lt h1q)
  have hsum_split :
      (Finset.range q).sum (fun i => (η i 1) x) =
        (η 0 1) x + ((Finset.range q).erase 0).sum (fun i => (η i 1) x) := by
    rw [← Finset.sum_erase_add _ _ h0mem]
    ring
  have hsum_erase :
      ((Finset.range q).erase 0).sum (fun i => (η i 1) x) =
        ((Finset.range q).erase 0).sum (fun _ => (η 0 1) x - 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hfirstColumn i (Finset.mem_range.mp (Finset.mem_of_mem_erase hi)) (by
      intro h
      subst h
      exact Finset.notMem_erase 0 _ hi)
  have hcard_erase : ((Finset.range q).erase 0).card = q - 1 := by
    simpa using Finset.card_erase_of_mem h0mem
  have hsum_formula :
      (Finset.range q).sum (fun i => (η i 1) x) =
        (η 0 1) x + ((q - 1 : ℕ) : ℂ) * ((η 0 1) x - 1) := by
    rw [hsum_split, hsum_erase, Finset.sum_const, nsmul_eq_mul, hcard_erase]
  have hqsub_cast : ((q - 1 : ℕ) : ℂ) + 1 = (q : ℂ) := by
    have hle : 1 ≤ q := le_of_lt h1q
    exact_mod_cast (Nat.sub_add_cancel hle)
  have hqsub : ((q - 1 : ℕ) : ℂ) = (q : ℂ) - 1 := by
    linear_combination hqsub_cast
  have hmain : (q : ℂ) * ((η 0 1) x - 1) = -1 := by
    have h := hsum_zero'
    rw [hsum_formula, hqsub] at h
    linear_combination h
  have hq_ne : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt h1q))
  have hη01 : (η 0 1) x - 1 = -((q : ℂ)⁻¹) := by
    calc
      (η 0 1) x - 1 =
          ((q : ℂ)⁻¹) * ((q : ℂ) * ((η 0 1) x - 1)) := by
        field_simp [hq_ne]
      _ = ((q : ℂ)⁻¹) * (-1) := by rw [hmain]
      _ = -((q : ℂ)⁻¹) := by ring
  have h1_ne : (1 : ℕ) ≠ 0 := by norm_num
  simpa [hfirstColumn 1 h1q h1_ne] using hη01

private theorem theorem_13_9_q_gt_one_of_source
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
    1 < q := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
      _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
      _hSType, _hTType, _hmax⟩
  have hW1card : 1 < Nat.card W1 :=
    (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
  simpa [hq_card] using hW1card

private theorem theorem_13_9_p_gt_one_of_source
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
    1 < p := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
      _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
      _hSType, _hTType, _hmax⟩
  have hW2card : 1 < Nat.card W2 :=
    (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
  simpa [hp_card] using hW2card

private theorem theorem_13_9_eta_signedIrreducible_of_notation
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {i j : ℕ} (hi : i < q) (hj : j < p) :
    Section3.IsSignedIrreducibleCharacter (η i j) := by
  rcases hnotation with
    ⟨homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμ0, _hν0, _hμdiff, _hνdiff, _hμsum, _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωeq⟩
  let iFin : Fin q := ⟨i, hi⟩
  let jFin : Fin p := ⟨j, hj⟩
  have hω_irred : Section1.IsIrreducibleCharacterOnGroup (ω i j) := by
    rw [hωeq i j hi hj]
    exact hωFin.irreducible iFin jFin
  have hω_class : Section1.IsClassFunction (ω i j) := by
    rw [hωeq i j hi hj]
    exact hωFin.is_class iFin jFin
  have hvirtW : Theory.Character.IsVirtualCharacter (ω i j) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hω_irred
  have hvirtG : Theory.Character.IsVirtualCharacter (σ (ω i j)) :=
    hσmap.2.1 (ω i j) hvirtW
  have hself : Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
    calc
      Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
          Section1.scalarProduct W (ω i j) (ω i j) :=
        hσmap.1 (ω i j) (ω i j) hω_class hω_class
      _ = Section1.scalarProduct W (ωFin iFin jFin) (ωFin iFin jFin) := by
        rw [hωeq i j hi hj]
      _ = 1 := by
        simpa using hωFin.orthonormal (iFin, jFin) (iFin, jFin)
  have hη_sigma : η i j = σ (ω i j) := hη i j hi hj
  rw [hη_sigma]
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirtG hself

private theorem theorem_13_9_isIntegral_value_of_signedIrreducible
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) (g : G) :
    IsIntegral ℤ (χ g) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hμ with ⟨n, ρ, _hirr, hchar⟩
  rcases hε with rfl | rfl
  · simpa [hchar] using Theory.Character.representation_character_isIntegral (ρ := ρ) g
  · simpa [hchar] using
      (Theory.Character.representation_character_isIntegral (ρ := ρ) g).neg

private theorem theorem_13_9_int_ne_neg_inv_nat_complex
    (q : ℕ) (h1q : 1 < q) :
    ∀ n : ℤ, (n : ℂ) ≠ -((q : ℂ)⁻¹) := by
  intro n h
  have hq_ne : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt h1q))
  have hmul : ((q : ℤ) * n : ℂ) = -1 := by
    calc
      ((q : ℤ) * n : ℂ) = (q : ℂ) * (n : ℂ) := by norm_num
      _ = (q : ℂ) * (-((q : ℂ)⁻¹)) := by rw [h]
      _ = -1 := by field_simp [hq_ne]
  have hmul_int : (q : ℤ) * n = -1 := by
    exact_mod_cast hmul
  have habs : Int.natAbs ((q : ℤ) * n) = 1 := by
    rw [hmul_int]
    norm_num
  rw [Int.natAbs_mul] at habs
  have hqabs : Int.natAbs (q : ℤ) = q := by simp
  rw [hqabs] at habs
  have hq_ge_two : 2 ≤ q := by omega
  have hn_abs_pos : 0 < Int.natAbs n := by
    by_contra h
    have hn0 : Int.natAbs n = 0 := by omega
    rw [hn0, mul_zero] at habs
    norm_num at habs
  have hn_abs_ge_one : 1 ≤ Int.natAbs n := Nat.succ_le_of_lt hn_abs_pos
  have hprod_ge_two : 2 ≤ q * Int.natAbs n :=
    Nat.mul_le_mul hq_ge_two hn_abs_ge_one
  omega


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_eta11_value_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x = 0 →
      (η 1 1) x = -((q : ℂ)⁻¹) := by
  intro x hx hξzero hηzero
  have hrows : theorem_13_9_EtaColumnRowsAt q η x :=
    theorem_13_9_nonvanishing_eta_column_zero_eta10_rows_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      ξ hξmodel hξeq x hx hξzero hηzero
  have h1q : 1 < q := by
    exact theorem_13_9_q_gt_one_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  exact theorem_13_9_nonvanishing_eta_column_eta11_value_of_rows
    q η ξ x hξmodel hrows hξzero h1q


private theorem theorem_13_9_nonvanishing_eta_column_eta11_neg_value_integral_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D _H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_lam : Section1.ClassFunction Smax)
    (_lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ x : G, x ∈ G0 → (η 1 1) x = -((q : ℂ)⁻¹) →
      ∃ n : ℤ, - (η 1 1) x = (n : ℂ) := by
  intro x _hx hη
  have h1q : 1 < q := by
    exact theorem_13_9_q_gt_one_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  have h1p : 1 < p := by
    exact theorem_13_9_p_gt_one_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  have hsigned : Section3.IsSignedIrreducibleCharacter (η 1 1) :=
    theorem_13_9_eta_signedIrreducible_of_notation
      Smax Tmax W W1 W2 ω η μ ν μsum νsum δ δ' σ p q hnotation h1q h1p
  have hint : IsIntegral ℤ (- (η 1 1) x) :=
    (theorem_13_9_isIntegral_value_of_signedIrreducible hsigned x).neg
  have hrat : ∃ r : ℚ, - (η 1 1) x = (r : ℂ) := by
    refine ⟨((q : ℚ)⁻¹), ?_⟩
    rw [hη]
    norm_num
  exact Theory.Character.isaacs_lemma_3_2_core hint hrat


private theorem theorem_13_9_nonvanishing_eta_column_eta11_value_integral_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ x : G, x ∈ G0 → (η 1 1) x = -((q : ℂ)⁻¹) →
      ∃ n : ℤ, (η 1 1) x = (n : ℂ) := by
  intro x hx hη
  rcases theorem_13_9_nonvanishing_eta_column_eta11_neg_value_integral_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      x hx hη with
    ⟨n, hn⟩
  refine ⟨-n, ?_⟩
  simpa using congrArg Neg.neg hn


private theorem theorem_13_9_nonvanishing_eta_column_eta11_value_impossible_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ x : G, x ∈ G0 → (η 1 1) x = -((q : ℂ)⁻¹) → False := by
  intro x hx hη
  rcases theorem_13_9_nonvanishing_eta_column_eta11_value_integral_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      x hx hη with
    ⟨n, hn⟩
  have h1q : 1 < q :=
    theorem_13_9_q_gt_one_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  exact theorem_13_9_int_ne_neg_inv_nat_complex q h1q n (by
    rw [← hn, hη])


private theorem theorem_13_9_nonvanishing_eta_column_zero_eta10_contradiction_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x = 0 → False := by
  intro x hx hξzero hηzero
  have hη11 : (η 1 1) x = -((q : ℂ)⁻¹) :=
    theorem_13_9_nonvanishing_eta_column_zero_eta10_eta11_value_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      ξ hξmodel hξeq x hx hξzero hηzero
  exact theorem_13_9_nonvanishing_eta_column_eta11_value_impossible_source
    Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
    ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
    x hx hη11


private theorem theorem_13_9_nonvanishing_eta_column_zero_forces_eta10_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (ξ : Section1.ClassFunction G)
    (hξmodel : theorem_13_9_EtaColumnModel q η ξ)
    (hξeq : ∀ x : G, x ∈ G0 → lamτ x = ξ x) :
    ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x ≠ 0 := by
  intro x hx hξzero hηzero
  exact theorem_13_9_nonvanishing_eta_column_zero_eta10_contradiction_source
    Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
    ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
    ξ hξmodel hξeq x hx hξzero hηzero

/- Checked package for PF `(13.9)(a)`: combine the model construction and the
model-zero contradiction into the nonvanishing source package consumed below. -/
private theorem theorem_13_9_nonvanishing_eta_column_model_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    ∃ ξ : Section1.ClassFunction G,
      (∀ x : G, x ∈ G0 → lamτ x = ξ x) ∧
        ∀ x : G, x ∈ G0 → ξ x = 0 → (η 1 0) x ≠ 0 := by
  rcases theorem_13_9_nonvanishing_eta_column_agreement_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hhyp hcoh houtput with
    ⟨ξ, hξmodel, hξeq⟩
  exact ⟨ξ, hξeq,
    theorem_13_9_nonvanishing_eta_column_zero_forces_eta10_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      ξ hξmodel hξeq⟩

private theorem theorem_13_9_nonvanishing_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    ∀ x : G, x ∈ G0 → lamτ x ≠ 0 ∨ (η 1 0) x ≠ 0 := by
  rcases theorem_13_9_nonvanishing_eta_column_model_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hcoh houtput hhyp with
    ⟨ξ, hLamEq, hEta⟩
  intro x hx
  by_cases hLam : lamτ x = 0
  · exact Or.inr (hEta x hx ((hLamEq x hx).symm.trans hLam))
  · exact Or.inl hLam

private theorem theorem_13_9_supportEnergy_add_ge_card_of_nonzero_supports
    {G : Type u}
    [Group G]
    [Finite G]
    (X : Set G)
    (χ ψ : Section1.ClassFunction G)
    (hcover : ∀ x : G, x ∈ X → χ x ≠ 0 ∨ ψ x ≠ 0)
    (hχ : (Nat.card ({x : G | x ∈ X ∧ χ x ≠ 0} : Set G) : ℝ) ≤
      Section7.supportEnergy X χ)
    (hψ : (Nat.card ({x : G | x ∈ X ∧ ψ x ≠ 0} : Set G) : ℝ) ≤
      Section7.supportEnergy X ψ) :
    (Nat.card X : ℝ) ≤ Section7.supportEnergy X χ + Section7.supportEnergy X ψ := by
  classical
  let A : Set G := {x : G | x ∈ X ∧ χ x ≠ 0}
  let B : Set G := {x : G | x ∈ X ∧ ψ x ≠ 0}
  have hX_subset : X ⊆ A ∪ B := by
    intro x hx
    rcases hcover x hx with hχx | hψx
    · exact Or.inl ⟨hx, hχx⟩
    · exact Or.inr ⟨hx, hψx⟩
  have hcard_nat : X.ncard ≤ A.ncard + B.ncard := by
    exact le_trans (Set.ncard_le_ncard hX_subset) (Set.ncard_union_le A B)
  have hcard : (Nat.card X : ℝ) ≤ (Nat.card A : ℝ) + (Nat.card B : ℝ) := by
    have hcard_real : (X.ncard : ℝ) ≤ (A.ncard : ℝ) + (B.ncard : ℝ) := by
      exact_mod_cast hcard_nat
    simpa [← Nat.card_coe_set_eq] using hcard_real
  have hχ' : (Nat.card A : ℝ) ≤ Section7.supportEnergy X χ := by
    simpa [A] using hχ
  have hψ' : (Nat.card B : ℝ) ≤ Section7.supportEnergy X ψ := by
    simpa [B] using hψ
  exact le_trans hcard (add_le_add hχ' hψ')

private theorem theorem_13_9_supportEnergy_eq_sum_subtype
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (χ : Section1.ClassFunction G) :
    Section7.supportEnergy X χ =
      ∑ x : {g : G // g ∈ X}, Complex.normSq (χ x.1) := by
  classical
  rw [Section7.supportEnergy]
  have hfilter :
      (∑ g : G, (if g ∈ X then Complex.normSq (χ g) else 0)) =
        ∑ g ∈ (Finset.univ.filter (fun g : G => g ∈ X)), Complex.normSq (χ g) := by
    simp [Finset.sum_filter]
  rw [hfilter]
  exact Finset.sum_subtype (s := Finset.univ.filter (fun g : G => g ∈ X))
    (p := fun g : G => g ∈ X) (f := fun g : G => Complex.normSq (χ g)) (by simp)

private theorem theorem_13_9_sum_subtype_mono_of_subset
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (P : G → Prop) (χ : Section1.ClassFunction G) :
    (∑ x : {g : G // g ∈ X ∧ P g}, Complex.normSq (χ x.1)) ≤
      ∑ x : {g : G // g ∈ X}, Complex.normSq (χ x.1) := by
  classical
  let sXP : Finset G := Finset.univ.filter (fun g : G => g ∈ X ∧ P g)
  let sX : Finset G := Finset.univ.filter (fun g : G => g ∈ X)
  rw [← Finset.sum_subtype (s := sXP)
      (p := fun g : G => g ∈ X ∧ P g)
      (f := fun g : G => Complex.normSq (χ g)) (by simp [sXP])]
  rw [← Finset.sum_subtype (s := sX)
      (p := fun g : G => g ∈ X)
      (f := fun g : G => Complex.normSq (χ g)) (by simp [sX])]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro g hg
      simp [sXP, sX] at hg ⊢
      exact hg.1)
    (by
      intro g _hgX _hgnot
      exact Complex.normSq_nonneg (χ g))

private theorem theorem_13_9_supportEnergy_cycle_partition
    {G : Type u} [Group G] [Finite G]
    (G0 : Set G) (χ : Section1.ClassFunction G) :
    (∑ L : Subgroup G,
      Section7.supportEnergy ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = L} : Set G)
        χ) = Section7.supportEnergy G0 χ := by
  classical
  simp only [Section7.supportEnergy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g ∈ G0
  · simp [hg]
  · simp [hg]

private theorem theorem_13_9_mem_conjugates_punctured_of_mem_zpowers
    {G : Type u} [Group G]
    (K : Subgroup G) {x y : G}
    (hy : y ∈ section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet K) Set.univ)
    (hxmem : x ∈ Subgroup.zpowers y) (hxne : x ≠ 1) :
    x ∈ section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet K) Set.univ := by
  rcases hy with ⟨a, ha, g, _hg, rfl⟩
  rcases ha with ⟨haK, _hane⟩
  rcases Subgroup.mem_zpowers_iff.mp hxmem with ⟨n, hn⟩
  have hconj : (g * a * g⁻¹) ^ n = g * (a ^ n) * g⁻¹ := by
    simpa [mul_assoc] using (conj_zpow (a := g) (b := a) (i := n))
  refine ⟨a ^ n, ⟨K.zpow_mem haK n, ?_⟩, g, Set.mem_univ g, ?_⟩
  · intro ha1
    apply hxne
    calc
      x = (g * a * g⁻¹) ^ n := hn.symm
      _ = g * (a ^ n) * g⁻¹ := hconj
      _ = 1 := by simp [ha1]
  · calc
      x = (g * a * g⁻¹) ^ n := hn.symm
      _ = g * (a ^ n) * g⁻¹ := hconj

private theorem theorem_13_9_G0_mem_of_zpowers_eq
    {G : Type u} [Group G]
    (H Q : Subgroup G) (G0 : Set G)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    ∀ {x y : G}, x ∈ G0 → Subgroup.zpowers y = Subgroup.zpowers x → y ∈ G0 := by
  intro x y hx hcycle
  rw [hG0] at hx ⊢
  have hxne : x ≠ 1 := by
    simpa [section16NonidentityElements] using hx.1.2
  have hxy : x ∈ Subgroup.zpowers y := by
    simp [hcycle]
  constructor
  · constructor
    · simp
    · intro hy1
      rcases Subgroup.mem_zpowers_iff.mp hxy with ⟨n, hn⟩
      apply hxne
      calc
        x = y ^ n := hn.symm
        _ = 1 := by simp [hy1]
  · intro hybad
    apply hx.2
    rcases hybad with hyH | hyQ
    · exact Or.inl
        (theorem_13_9_mem_conjugates_punctured_of_mem_zpowers H hyH hxy hxne)
    · exact Or.inr
        (theorem_13_9_mem_conjugates_punctured_of_mem_zpowers Q hyQ hxy hxne)

private theorem theorem_13_9_signed_character_value_ne_zero_of_pow_coprime_natCard
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (hχsigned : Section3.IsSignedIrreducibleCharacter χ)
    {x : G} {e : ℕ} (he : e.Coprime (Nat.card G)) :
    χ x ≠ 0 → χ (x ^ e) ≠ 0 := by
  intro hχx hzero
  rcases hχsigned with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hμ with ⟨n, ρ, _hirr, hμeq⟩
  rcases Section5.complex_galois_aut_pow_on_roots
      (n := Nat.card G) (e := e) he with
    ⟨τ, hτroot⟩
  have hτμ : τ (μ x) = μ (x ^ e) := by
    have h := Section1.representation_character_apply_galois_eq_argumentPow
      (G := G) (V := Fin n → ℂ) (N := Nat.card G) (e := e)
      (τ := τ) hτroot ρ (dvd_refl (Nat.card G)) x
    simpa [hμeq] using h
  rcases hε with rfl | rfl
  · apply hχx
    have hz : τ (μ x) = 0 := by
      rw [hτμ]
      simpa using hzero
    have hpre := congrArg τ.symm hz
    simpa using hpre
  · apply hχx
    have hτχ : τ ((-1 : ℂ) * μ x) = (-1 : ℂ) * μ (x ^ e) := by
      simp [hτμ]
    have hz : τ ((-1 : ℂ) * μ x) = 0 := by
      rw [hτχ]
      simpa using hzero
    have hpre := congrArg τ.symm hz
    simpa using hpre


private theorem theorem_13_9_signed_nonzero_support_cycle_character_nonzero_source
    {G : Type u}
    [Group G]
    [Finite G]
    (χ : Section1.ClassFunction G)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, χ x ≠ 0 →
      ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → χ y ≠ 0 := by
  intro x hχx y hycycle
  have hy_mem : y ∈ Subgroup.zpowers x := by
    simp [← hycycle]
  rcases Subgroup.mem_zpowers_iff.mp hy_mem with ⟨k, hk⟩
  have hx_mem_y : x ∈ Subgroup.zpowers y := by
    rw [hycycle]
    simp
  have hx_mem_pow : x ∈ Subgroup.zpowers (x ^ k) := by
    simpa [← hk] using hx_mem_y
  have hk_gcd : k.gcd (orderOf x : ℤ) = 1 :=
    mem_zpowers_zpow_iff.mp hx_mem_pow
  have hk_coprime : IsCoprime k (orderOf x : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hk_gcd
  obtain ⟨e, he, hmod⟩ :=
    Section6.theorem_6_8_exists_coprime_natCard_intModEq_orderOf
      (G := G) x hk_coprime
  have hpow : x ^ e = x ^ k := by
    rw [← zpow_natCast]
    exact (zpow_eq_zpow_iff_modEq).2 hmod
  have hy_eq : y = x ^ e := by
    calc
      y = x ^ k := hk.symm
      _ = x ^ e := hpow.symm
  simpa [hy_eq] using
    theorem_13_9_signed_character_value_ne_zero_of_pow_coprime_natCard
      (G := G) (χ := χ) _hχsigned (x := x) (e := e) he hχx


private theorem theorem_13_9_signed_nonzero_support_cycle_generators_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H Q : Subgroup G)
    (G0 : Set G)
    (χ : Section1.ClassFunction G)
    (_hG0 : theorem_13_9_G0Data H Q G0)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, x ∈ G0 → χ x ≠ 0 →
      ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x →
        y ∈ G0 ∧ χ y ≠ 0 := by
  intro x hx hχx y hycycle
  exact ⟨theorem_13_9_G0_mem_of_zpowers_eq H Q G0 _hG0 hx hycycle,
    theorem_13_9_signed_nonzero_support_cycle_character_nonzero_source
      χ _hχsigned x hχx y hycycle⟩

private theorem theorem_13_9_zpowers_subtype_eq_top_iff
    {G : Type u}
    [Group G]
    {H : Subgroup G}
    (y : H) :
    Subgroup.zpowers y = (⊤ : Subgroup H) ↔
      Subgroup.zpowers (y : G) = H := by
  constructor
  · intro hy
    apply le_antisymm
    · exact (Subgroup.zpowers_le).2 y.2
    · intro g hg
      have htop : (⟨g, hg⟩ : H) ∈ (⊤ : Subgroup H) := by simp
      have hmem : (⟨g, hg⟩ : H) ∈ Subgroup.zpowers y := by
        rw [hy]; exact htop
      rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  · intro hy
    apply le_antisymm
    · exact le_top
    · intro h _hh
      have hmemG : (h : G) ∈ Subgroup.zpowers (y : G) := by
        simp [hy]
      rcases Subgroup.mem_zpowers_iff.mp hmemG with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

private noncomputable def theorem_13_9_cycleGeneratorSubtypeEquiv
    {G : Type u}
    [Group G]
    (x : G) :
    {y : G // Subgroup.zpowers y = Subgroup.zpowers x} ≃
      {y : Subgroup.zpowers x //
        Subgroup.zpowers y = (⊤ : Subgroup (Subgroup.zpowers x))} where
  toFun y := by
    have hy_mem : y.1 ∈ Subgroup.zpowers x := by
      have hle : Subgroup.zpowers y.1 ≤ Subgroup.zpowers x := by
        rw [y.2]
      exact hle (Subgroup.mem_zpowers y.1)
    exact ⟨⟨y.1, hy_mem⟩,
      (theorem_13_9_zpowers_subtype_eq_top_iff
        (H := Subgroup.zpowers x)
        ⟨y.1, hy_mem⟩).2
        (by simpa using y.2)⟩
  invFun y :=
    ⟨y.1.1,
      (theorem_13_9_zpowers_subtype_eq_top_iff
        (H := Subgroup.zpowers x) y.1).1 y.2⟩
  left_inv y := by
    ext
    rfl
  right_inv y := by
    ext
    rfl

private theorem theorem_13_9_weightedLinearSum_eq_repeatedLinearSum
    {H ι : Type*}
    [Group H]
    [Finite ι]
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ)
    (y : H) :
    Section1.weightedFamilySum (fun i : ι => (e i : ℂ))
      (fun i : ι => fun h : H => (lam i h : ℂ)) y =
        ∑ i : ι, ∑ _ : Fin (e i), (lam i y : ℂ) := by
  simp [Section1.weightedFamilySum, Finset.sum_const, nsmul_eq_mul]

private theorem theorem_13_9_sum_normSq_ge_card_of_prod_normSq_ge_one
    {α : Type*}
    [Fintype α]
    (f : α → ℂ)
    (hprod : (1 : ℝ) ≤ ∏ a : α, Complex.normSq (f a)) :
    (Nat.card α : ℝ) ≤ ∑ a : α, Complex.normSq (f a) := by
  classical
  by_cases hα : Nonempty α
  · have hcard_pos_nat : 0 < Nat.card α := Nat.card_pos
    have hcard_pos : 0 < (Nat.card α : ℝ) := by
      exact_mod_cast hcard_pos_nat
    have hsum_one : (∑ _a : α, (1 : ℝ)) = (Nat.card α : ℝ) := by
      simp
    have hgeom := Real.geom_mean_le_arith_mean (Finset.univ : Finset α)
      (fun _ : α => (1 : ℝ)) (fun a : α => Complex.normSq (f a))
      (fun _ _ => by norm_num) (by simpa [hsum_one] using hcard_pos)
      (fun a _ => Complex.normSq_nonneg (f a))
    have hgeom' :
        (∏ a : α, Complex.normSq (f a)) ^ ((∑ _a : α, (1 : ℝ))⁻¹) ≤
          (∑ a : α, (1 : ℝ) * Complex.normSq (f a)) /
            ∑ _a : α, (1 : ℝ) := by
      simpa using hgeom
    have hone_le_geom : (1 : ℝ) ≤
        (∏ a : α, Complex.normSq (f a)) ^ ((∑ _a : α, (1 : ℝ))⁻¹) := by
      have hexp_nonneg : 0 ≤ (∑ _a : α, (1 : ℝ))⁻¹ := by
        rw [hsum_one]
        exact inv_nonneg.mpr hcard_pos.le
      have hraw :=
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod hexp_nonneg
      simpa using hraw
    have hone_le_arith : (1 : ℝ) ≤
        (∑ a : α, (1 : ℝ) * Complex.normSq (f a)) / ∑ _a : α, (1 : ℝ) :=
      hone_le_geom.trans hgeom'
    have hmul := mul_le_mul_of_nonneg_right hone_le_arith hcard_pos.le
    rw [hsum_one] at hmul
    have hcard_ne : (Nat.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
    field_simp [hcard_ne] at hmul
    simpa using hmul
  · have hsub : IsEmpty α := not_nonempty_iff.mp hα
    letI : IsEmpty α := hsub
    simp

private theorem theorem_13_9_cyclotomic_resultant_eq_primitiveRoot_eval_prod
    {n : ℕ}
    (hn : 0 < n)
    (P : ℤ[X]) :
    ((Polynomial.cyclotomic n ℤ).resultant P : ℂ) =
      (primitiveRoots n ℂ).prod
        (fun z => Polynomial.eval z (P.map (Int.castRingHom ℂ))) := by
  classical
  haveI : NeZero n := NeZero.of_gt hn
  haveI : NeZero (n : ℂ) := inferInstance
  have hmap : ((Polynomial.cyclotomic n ℤ).resultant P : ℂ) =
      (Polynomial.cyclotomic n ℂ).resultant (P.map (Int.castRingHom ℂ)) := by
    have h := Polynomial.resultant_map_map (φ := Int.castRingHom ℂ)
      (f := Polynomial.cyclotomic n ℤ) (g := P)
      (m := (Polynomial.cyclotomic n ℤ).natDegree) (n := P.natDegree)
    rw [Polynomial.map_cyclotomic_int] at h
    change (Int.castRingHom ℂ) ((Polynomial.cyclotomic n ℤ).resultant P) =
      (Polynomial.cyclotomic n ℂ).resultant (P.map (Int.castRingHom ℂ))
    rw [← h]
    have hm : (Polynomial.cyclotomic n ℤ).natDegree =
        (Polynomial.cyclotomic n ℂ).natDegree := by
      rw [← Polynomial.map_cyclotomic_int n ℂ]
      exact (Polynomial.natDegree_map_eq_of_injective
        (Int.castRingHom ℂ).injective_int _).symm
    have hP : P.natDegree = (P.map (Int.castRingHom ℂ)).natDegree := by
      exact (Polynomial.natDegree_map_eq_of_injective
        (Int.castRingHom ℂ).injective_int _).symm
    rw [hm, hP]
  have hprod := Polynomial.resultant_eq_prod_eval (Polynomial.cyclotomic n ℂ)
    (P.map (Int.castRingHom ℂ)) (P.map (Int.castRingHom ℂ)).natDegree le_rfl
    (IsAlgClosed.splits (Polynomial.cyclotomic n ℂ))
  rw [hmap, hprod]
  simp [Polynomial.cyclotomic.monic, Polynomial.cyclotomic.roots_eq_primitiveRoots_val]

private theorem theorem_13_9_prod_normSq_primitiveRoots_eval_intCast_ge_one
    {n : ℕ}
    (hn : 0 < n)
    (P : ℤ[X]) :
    (∀ z ∈ primitiveRoots n ℂ,
      Polynomial.eval z (P.map (Int.castRingHom ℂ)) ≠ 0) →
      (1 : ℝ) ≤
        (primitiveRoots n ℂ).prod
          (fun z => Complex.normSq (Polynomial.eval z (P.map (Int.castRingHom ℂ)))) := by
  classical
  intro hnonzero
  let r : ℤ := (Polynomial.cyclotomic n ℤ).resultant P
  have hres := theorem_13_9_cyclotomic_resultant_eq_primitiveRoot_eval_prod hn P
  have hprod_ne :
      (primitiveRoots n ℂ).prod
        (fun z => Polynomial.eval z (P.map (Int.castRingHom ℂ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro z hz
      exact hnonzero z hz)
  have hr_ne : r ≠ 0 := by
    intro hr
    apply hprod_ne
    rw [← hres]
    simp [r, hr]
  have hnorm_prod :
      (primitiveRoots n ℂ).prod
          (fun z => Complex.normSq (Polynomial.eval z (P.map (Int.castRingHom ℂ)))) =
        Complex.normSq
          ((primitiveRoots n ℂ).prod
            (fun z => Polynomial.eval z (P.map (Int.castRingHom ℂ)))) := by
    exact (map_prod Complex.normSq
      (fun z => Polynomial.eval z (P.map (Int.castRingHom ℂ))) (primitiveRoots n ℂ)).symm
  rw [hnorm_prod, ← hres]
  change (1 : ℝ) ≤ Complex.normSq ((r : ℂ))
  rw [Complex.normSq_intCast]
  have habs : (1 : ℝ) ≤ |(r : ℝ)| := by
    exact_mod_cast Int.one_le_abs hr_ne
  have hsq : (1 : ℝ) * (1 : ℝ) ≤ |(r : ℝ)| * |(r : ℝ)| := by
    exact mul_le_mul habs habs zero_le_one (abs_nonneg (r : ℝ))
  simpa [abs_mul_abs_self] using hsq


private theorem theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_cyclotomic_character_source
    {H : Type u}
    [Group H]
    [Finite H]
    {ι : Type*}
    [Finite ι]
    (x : H)
    (_hx : Subgroup.zpowers x = (⊤ : Subgroup H))
    (_e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
      ∃ (n : ℕ) (_hn : 0 < n) (χ : H →* ℂˣ) (k : ι → ℕ)
        (reindex :
          {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} ≃
            {z : ℂ // z ∈ primitiveRoots n ℂ}),
        (∀ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          (reindex y).1 = (χ y.1 : ℂ)) ∧
        (∀ i : ι, lam i = χ ^ k i) := by
  classical
  let n : ℕ := Nat.card H
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.card_pos
  have hn_ne : n ≠ 0 := hn.ne'
  haveI : NeZero n := ⟨hn_ne⟩
  have hxmem : ∀ y : H, y ∈ Subgroup.zpowers x := by
    intro y
    exact _hx.ge (Subgroup.mem_top y)
  haveI : IsCyclic H := (isCyclic_iff_exists_zpowers_eq_top (α := H)).2 ⟨x, _hx⟩
  have hcardRoots : Nat.card (rootsOfUnity n ℂ) = n :=
    Complex.card_rootsOfUnity n
  have hcard : Nat.card H = Nat.card (rootsOfUnity n ℂ) := by
    rw [hcardRoots]
  let rootEquiv : H ≃* rootsOfUnity n ℂ :=
    mulEquivOfCyclicCardEq (G := H) (G' := rootsOfUnity n ℂ) hcard
  let χ : H →* ℂˣ := (rootsOfUnity n ℂ).subtype.comp rootEquiv.toMonoidHom
  have hxorder : orderOf x = n := by
    dsimp [n]
    exact orderOf_eq_card_of_zpowers_eq_top _hx
  have hχx_order : orderOf (χ x) = n := by
    change orderOf ((rootsOfUnity n ℂ).subtype (rootEquiv x)) = n
    rw [orderOf_injective (rootsOfUnity n ℂ).subtype Subtype.coe_injective (rootEquiv x)]
    rw [rootEquiv.orderOf_eq, hxorder]
  have hχx_prim : IsPrimitiveRoot (χ x) n := by
    simpa [hχx_order] using IsPrimitiveRoot.orderOf (χ x)
  have hexp : ∀ i : ι, ∃ k : ℕ, lam i = χ ^ k := by
    intro i
    have hlam_root : lam i x ∈ rootsOfUnity n ℂ := by
      rw [mem_rootsOfUnity]
      change (lam i x) ^ n = 1
      rw [← map_pow]
      have hxpow : x ^ n = 1 := by
        rw [← hxorder]
        exact pow_orderOf_eq_one x
      rw [hxpow, map_one]
    have hmem_z : lam i x ∈ Subgroup.zpowers (χ x) := by
      rw [hχx_prim.zpowers_eq]
      exact hlam_root
    have hmem_p : lam i x ∈ Submonoid.powers (χ x) :=
      (hχx_prim.isOfFinOrder hn_ne).mem_powers_iff_mem_zpowers.mpr hmem_z
    rcases (Submonoid.mem_powers_iff (lam i x) (χ x)).mp hmem_p with ⟨k, hk⟩
    refine ⟨k, (MonoidHom.eq_iff_eq_on_generator hxmem (lam i) (χ ^ k)).mpr ?_⟩
    simpa using hk.symm
  let k : ι → ℕ := fun i => Classical.choose (hexp i)
  have hk : ∀ i : ι, lam i = χ ^ k i := fun i => Classical.choose_spec (hexp i)
  let reindexFun :
      {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} →
        {z : ℂ // z ∈ primitiveRoots n ℂ} := fun y =>
    ⟨((rootEquiv y.1 : ℂˣ) : ℂ), by
      have hyorder : orderOf y.1 = n := by
        dsimp [n]
        exact orderOf_eq_card_of_zpowers_eq_top y.2
      have hroot_order : orderOf (rootEquiv y.1) = n := by
        rw [rootEquiv.orderOf_eq, hyorder]
      have hunit_order : orderOf ((rootEquiv y.1 : rootsOfUnity n ℂ) : ℂˣ) = n :=
        (orderOf_injective (rootsOfUnity n ℂ).subtype Subtype.coe_injective
          (rootEquiv y.1)).trans hroot_order
      have hunit_prim : IsPrimitiveRoot ((rootEquiv y.1 : rootsOfUnity n ℂ) : ℂˣ) n := by
        simpa [hunit_order] using
          IsPrimitiveRoot.orderOf ((rootEquiv y.1 : rootsOfUnity n ℂ) : ℂˣ)
      exact (mem_primitiveRoots hn).mpr (IsPrimitiveRoot.coe_units_iff.mpr hunit_prim)⟩
  have hreindex_bij : Function.Bijective reindexFun := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply rootEquiv.injective
      apply Subtype.ext
      apply Units.ext
      exact congr_arg Subtype.val hab
    · intro z
      have hzprim : IsPrimitiveRoot z.1 n := (mem_primitiveRoots hn).mp z.2
      let zr : rootsOfUnity n ℂ := hzprim.toRootsOfUnity
      let y0 : H := rootEquiv.symm zr
      have hzr_val : (((zr : rootsOfUnity n ℂ) : ℂˣ) : ℂ) = z.1 := by
        simp [zr]
      have hzunit_prim : IsPrimitiveRoot ((zr : rootsOfUnity n ℂ) : ℂˣ) n := by
        exact IsPrimitiveRoot.coe_units_iff.mp (by simpa [hzr_val] using hzprim)
      have hzr_order_units : orderOf ((zr : rootsOfUnity n ℂ) : ℂˣ) = n := by
        exact hzunit_prim.eq_orderOf.symm
      have hzr_order : orderOf (zr : rootsOfUnity n ℂ) = n :=
        (orderOf_injective (rootsOfUnity n ℂ).subtype Subtype.coe_injective zr).symm.trans
          hzr_order_units
      have hy0_order : orderOf y0 = n := by
        rw [← rootEquiv.orderOf_eq y0]
        simp [y0, hzr_order]
      have hy0_top : Subgroup.zpowers y0 = (⊤ : Subgroup H) := by
        apply (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers y0)).mp
        rw [Nat.card_zpowers, hy0_order]
      refine ⟨⟨y0, hy0_top⟩, ?_⟩
      apply Subtype.ext
      change (((rootEquiv y0 : rootsOfUnity n ℂ) : ℂˣ) : ℂ) = z.1
      simp [y0, hzr_val]
  let reindex :
      {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} ≃
        {z : ℂ // z ∈ primitiveRoots n ℂ} := Equiv.ofBijective reindexFun hreindex_bij
  refine ⟨n, hn, χ, k, reindex, ?_, hk⟩
  intro y
  change (reindexFun y).1 = (χ y.1 : ℂ)
  rfl

/- Checked construction of the integer polynomial once the faithful cyclic
character and exponent data have been chosen. -/
private theorem theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_cyclotomic_values_source
    {H : Type u}
    [Group H]
    [Finite H]
    {ι : Type*}
    [Finite ι]
    (x : H)
    (_hx : Subgroup.zpowers x = (⊤ : Subgroup H))
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
      ∃ (n : ℕ) (_hn : 0 < n) (P : ℤ[X])
        (reindex :
          {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} ≃
            {z : ℂ // z ∈ primitiveRoots n ℂ}),
        (∀ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) =
            Polynomial.eval (reindex y).1 (P.map (Int.castRingHom ℂ))) := by
  classical
  rcases theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_cyclotomic_character_source
      x _hx e lam with
    ⟨n, hn, χ, k, reindex, hindex, hlam⟩
  let P : ℤ[X] := ∑ i : ι, ∑ _ : Fin (e i), Polynomial.X ^ k i
  refine ⟨n, hn, P, reindex, ?_⟩
  intro y
  calc
    (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) =
        ∑ i : ι, ∑ _ : Fin (e i), ((χ ^ k i) y.1 : ℂ) := by
          simp [hlam]
    _ = Polynomial.eval (χ y.1 : ℂ) (P.map (Int.castRingHom ℂ)) := by
          rw [Polynomial.eval_map]
          simp [P, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
            Polynomial.eval₂_X_pow, Polynomial.eval₂_natCast]
    _ = Polynomial.eval (reindex y).1 (P.map (Int.castRingHom ℂ)) := by
          rw [hindex y]

/- Checked nonvanishing transfer from the original generator-side hypothesis to
the primitive-root polynomial model.  The remaining source content is only the
construction of the value model above. -/
private theorem theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_cyclotomic_model_source
    {H : Type u}
    [Group H]
    [Finite H]
    {ι : Type*}
    [Finite ι]
    (x : H)
    (_hx : Subgroup.zpowers x = (⊤ : Subgroup H))
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
      (∑ i : ι, ∑ _ : Fin (e i), (lam i y : ℂ)) ≠ 0) →
      ∃ (n : ℕ) (_hn : 0 < n) (P : ℤ[X])
        (reindex :
          {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} ≃
            {z : ℂ // z ∈ primitiveRoots n ℂ}),
        (∀ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) =
            Polynomial.eval (reindex y).1 (P.map (Int.castRingHom ℂ))) ∧
        (∀ z ∈ primitiveRoots n ℂ,
          Polynomial.eval z (P.map (Int.castRingHom ℂ)) ≠ 0) := by
  classical
  intro hnonzero
  rcases theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_cyclotomic_values_source
      x _hx e lam with
    ⟨n, hn, P, reindex, hvalue⟩
  refine ⟨n, hn, P, reindex, hvalue, ?_⟩
  intro z hz
  let y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} := reindex.symm ⟨z, hz⟩
  have hy_nonzero :
      (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) ≠ 0 :=
    hnonzero y.1 y.2
  intro hzero
  apply hy_nonzero
  have hzy : (reindex y).1 = z := by
    simp [y]
  rw [hvalue y, hzy, hzero]


private theorem theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_product_source
    {H : Type u}
    [Group H]
    [Finite H]
    {ι : Type*}
    [Finite ι]
    (x : H)
    (_hx : Subgroup.zpowers x = (⊤ : Subgroup H))
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
      (∑ i : ι, ∑ _ : Fin (e i), (lam i y : ℂ)) ≠ 0) →
      (1 : ℝ) ≤
        ∏ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq
            (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) := by
  classical
  intro hnonzero
  rcases theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_cyclotomic_model_source
      x _hx e lam hnonzero with
    ⟨n, hn, P, reindex, hvalue, hPnonzero⟩
  letI : Fintype {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} := Fintype.ofFinite _
  have hprimitive :
      (1 : ℝ) ≤
        (primitiveRoots n ℂ).prod
          (fun z => Complex.normSq (Polynomial.eval z (P.map (Int.castRingHom ℂ)))) :=
    theorem_13_9_prod_normSq_primitiveRoots_eval_intCast_ge_one hn P hPnonzero
  have hmodelProd :
      (primitiveRoots n ℂ).prod
          (fun z => Complex.normSq (Polynomial.eval z (P.map (Int.castRingHom ℂ)))) =
        ∏ z : {z : ℂ // z ∈ primitiveRoots n ℂ},
          Complex.normSq (Polynomial.eval z.1 (P.map (Int.castRingHom ℂ))) := by
    simpa using (Finset.prod_attach (s := primitiveRoots n ℂ)
      (f := fun z : ℂ =>
        Complex.normSq (Polynomial.eval z (P.map (Int.castRingHom ℂ))))).symm
  have hreindex :
      (∏ z : {z : ℂ // z ∈ primitiveRoots n ℂ},
          Complex.normSq (Polynomial.eval z.1 (P.map (Int.castRingHom ℂ)))) =
        ∏ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq (Polynomial.eval (reindex y).1 (P.map (Int.castRingHom ℂ))) := by
    exact (reindex.prod_comp
      (fun z : {z : ℂ // z ∈ primitiveRoots n ℂ} =>
        Complex.normSq (Polynomial.eval z.1 (P.map (Int.castRingHom ℂ))))).symm
  have hvalues :
      (∏ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq (Polynomial.eval (reindex y).1 (P.map (Int.castRingHom ℂ)))) =
        ∏ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq
            (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) := by
    exact Fintype.prod_congr _ _ fun y => by
      rw [hvalue y]
  simpa [hmodelProd.trans (hreindex.trans hvalues)] using hprimitive


private theorem theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_source
    {H : Type u}
    [Group H]
    [Finite H]
    {ι : Type*}
    [Finite ι]
    (x : H)
    (_hx : Subgroup.zpowers x = (⊤ : Subgroup H))
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
      (∑ i : ι, ∑ _ : Fin (e i), (lam i y : ℂ)) ≠ 0) →
      (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) ≤
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq
            (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) := by
  intro hnonzero
  have hprod :
      (1 : ℝ) ≤
        ∏ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq
            (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) :=
    theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_product_source
      x _hx e lam hnonzero
  exact theorem_13_9_sum_normSq_ge_card_of_prod_normSq_ge_one
    (fun y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} =>
      ∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) hprod

/- Checked wrapper extracting a concrete generator from the cyclic typeclass. -/
private theorem theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_core_source
    {H : Type u}
    [Group H]
    [Finite H]
    [IsCyclic H]
    {ι : Type*}
    [Finite ι]
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
      (∑ i : ι, ∑ _ : Fin (e i), (lam i y : ℂ)) ≠ 0) →
      (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) ≤
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq
            (∑ i : ι, ∑ _ : Fin (e i), (lam i y.1 : ℂ)) := by
  intro hnonzero
  rcases (isCyclic_iff_exists_zpowers_eq_top (α := H)).1
      (inferInstance : IsCyclic H) with
    ⟨x, hx⟩
  exact theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_generator_source
    x hx e lam hnonzero

/- Checked transport wrapper from natural multiplicities to repeated
unweighted linear characters. -/
private theorem theorem_13_9_sum_normSq_cyclic_weighted_linear_characters_core_source
    {H : Type u}
    [Group H]
    [Finite H]
    [IsCyclic H]
    {ι : Type*}
    [Finite ι]
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
      Section1.weightedFamilySum (fun i : ι => (e i : ℂ))
        (fun i : ι => fun h : H => (lam i h : ℂ)) y ≠ 0) →
      (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) ≤
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq
            (Section1.weightedFamilySum (fun i : ι => (e i : ℂ))
              (fun i : ι => fun h : H => (lam i h : ℂ)) y.1) := by
  intro hnonzero
  have hrepNonzero :
      ∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
        (∑ i : ι, ∑ _ : Fin (e i), (lam i y : ℂ)) ≠ 0 := by
    intro y hy
    rw [← theorem_13_9_weightedLinearSum_eq_repeatedLinearSum e lam y]
    exact hnonzero y hy
  have hcore :=
    theorem_13_9_sum_normSq_cyclic_repeated_linear_characters_core_source
      e lam hrepNonzero
  simpa [theorem_13_9_weightedLinearSum_eq_repeatedLinearSum] using hcore

/- Checked transport wrapper allowing downstream code to keep an arbitrary name
for the weighted linear-character sum. -/
private theorem theorem_13_9_sum_normSq_cyclic_weighted_linear_characters_source
    {H : Type u}
    [Group H]
    [Finite H]
    [IsCyclic H]
    {ι : Type*}
    [Fintype ι]
    (e : ι → ℕ)
    (lam : ι → H →* ℂˣ)
    (χ : Section1.ClassFunction H)
    (_hχlin :
      χ = Section1.weightedFamilySum (fun i : ι => (e i : ℂ))
        (fun i : ι => fun h : H => (lam i h : ℂ))) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) → χ y ≠ 0) →
      (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) ≤
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq (χ y.1) := by
  intro hχnonzero
  have hnonzero :
      ∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) →
        Section1.weightedFamilySum (fun i : ι => (e i : ℂ))
          (fun i : ι => fun h : H => (lam i h : ℂ)) y ≠ 0 := by
    intro y hy
    rw [← _hχlin]
    exact hχnonzero y hy
  have hcore :=
    theorem_13_9_sum_normSq_cyclic_weighted_linear_characters_core_source
      e lam hnonzero
  simpa [_hχlin] using hcore


private theorem theorem_13_9_sum_normSq_cyclic_character_generators_source
    {H : Type u}
    [Group H]
    [Finite H]
    [IsCyclic H]
    (χ : Section1.ClassFunction H)
    (_hχchar : Section1.IsCharacter χ) :
    (∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) → χ y ≠ 0) →
      (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) ≤
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq (χ y.1) := by
  classical
  intro hχnonzero
  rcases Section1.character_irreducible_decomposition_all χ _hχchar with
    ⟨ι, hι, hιdec, e, ψ, hψbook, _hψpair, hχdecomp⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  letI : CommGroup H := IsCyclic.commGroup
  haveI : IsMulCommutative H := ⟨⟨mul_comm⟩⟩
  choose lam hlam using fun i : ι =>
    Section1.exists_linearCharacter_of_irreducible_degree_one
      (Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
        (ψ i) (hψbook i))
      (Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative
        (Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (ψ i) (hψbook i)))
  have hχlin :
      χ = Section1.weightedFamilySum (fun i : ι => (e i : ℂ))
        (fun i : ι => fun h : H => (lam i h : ℂ)) := by
    exact hχdecomp.trans
      (Section1.weightedFamilySum_congr
        (fun i : ι => (e i : ℂ))
        ψ
        (fun i : ι => fun h : H => (lam i h : ℂ))
        hlam)
  exact theorem_13_9_sum_normSq_cyclic_weighted_linear_characters_source
    (H := H) (ι := ι) e lam χ hχlin hχnonzero


private theorem theorem_13_9_sum_normSq_character_generators_source
    {G : Type u}
    [Group G]
    [Finite G]
    (χ : Section1.ClassFunction G)
    (_hχchar : Section1.IsCharacter χ) :
    ∀ x : G, (∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → χ y ≠ 0) →
      (Nat.card {y : G // Subgroup.zpowers y = Subgroup.zpowers x} : ℝ) ≤
        ∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
          Complex.normSq (χ y.1) := by
  classical
  intro x hnonzero
  let H : Subgroup G := Subgroup.zpowers x
  let χH : Section1.ClassFunction H := Section1.subgroupRestriction H χ
  letI : Fintype {g : G // Subgroup.zpowers g = Subgroup.zpowers x} :=
    Fintype.ofFinite _
  letI : Fintype {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)} :=
    Fintype.ofFinite _
  have hχHchar : Section1.IsCharacter χH := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        H χ _hχchar with
      ⟨V, hVadd, hVmod, hVfd, ρ, hρ⟩
    exact ⟨V, hVadd, hVmod, hVfd, ρ, hρ⟩
  have hHnonzero :
      ∀ y : H, Subgroup.zpowers y = (⊤ : Subgroup H) → χH y ≠ 0 := by
    intro y hy
    exact hnonzero y
      ((theorem_13_9_zpowers_subtype_eq_top_iff (H := H) y).1 hy)
  have hcyclic :=
    theorem_13_9_sum_normSq_cyclic_character_generators_source
      χH hχHchar hHnonzero
  have hcyclic' :
      (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) ≤
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq (χH y.1) := by
    simpa using hcyclic
  let e := theorem_13_9_cycleGeneratorSubtypeEquiv x
  have hcard :
      Nat.card {y : G // Subgroup.zpowers y = Subgroup.zpowers x} =
        Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} :=
    Nat.card_congr e
  have hcard_real :
      (Nat.card {y : G // Subgroup.zpowers y = Subgroup.zpowers x} : ℝ) =
        (Nat.card {y : H // Subgroup.zpowers y = (⊤ : Subgroup H)} : ℝ) := by
    exact_mod_cast hcard
  have hsum :
      (∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
          Complex.normSq (χ y.1)) =
        ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
          Complex.normSq (χH y.1) := by
    calc
      (∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
          Complex.normSq (χ y.1)) =
          ∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
            Complex.normSq (χH (e y).1) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            rfl
      _ =
          ∑ y : {g : H // Subgroup.zpowers g = (⊤ : Subgroup H)},
            Complex.normSq (χH y.1) := by
            exact Equiv.sum_comp e (fun y =>
              Complex.normSq (χH y.1))
  exact (le_of_eq hcard_real).trans
    (hcyclic'.trans (le_of_eq hsum.symm))


private theorem theorem_13_9_signed_nonzero_support_cycle_generator_sum_normSq_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H Q : Subgroup G)
    (G0 : Set G)
    (χ : Section1.ClassFunction G)
    (_hG0 : theorem_13_9_G0Data H Q G0)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, x ∈ G0 → χ x ≠ 0 →
      (Nat.card {y : G // Subgroup.zpowers y = Subgroup.zpowers x} : ℝ) ≤
        ∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
          Complex.normSq (χ y.1) := by
  classical
  intro x _hx hχx
  rcases _hχsigned with ⟨ε, hε, μ, hμ, rfl⟩
  have hμchar : Section1.IsCharacter μ :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hμ
  have hχnonzero :
      ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → (ε • μ) y ≠ 0 :=
    theorem_13_9_signed_nonzero_support_cycle_character_nonzero_source
      (ε • μ) ⟨ε, hε, μ, hμ, rfl⟩ x hχx
  have hμnonzero :
      ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → μ y ≠ 0 := by
    intro y hy hμy
    exact hχnonzero y hy (by
      rcases hε with rfl | rfl
      · simp [Pi.smul_apply, hμy]
      · simp [Pi.smul_apply, hμy])
  have hordinary :=
    theorem_13_9_sum_normSq_character_generators_source μ hμchar x hμnonzero
  rcases hε with rfl | rfl
  · simpa [Pi.smul_apply] using hordinary
  · simpa [Pi.smul_apply, Complex.normSq_neg] using hordinary


private theorem theorem_13_9_signed_nonzero_support_cycle_representative_nonzero_sum_normSq_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H Q : Subgroup G)
    (G0 : Set G)
    (χ : Section1.ClassFunction G)
    (_hG0 : theorem_13_9_G0Data H Q G0)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, x ∈ G0 → χ x ≠ 0 →
      (Nat.card {y : G //
          y ∈ ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} :
            Set G) ∧ χ y ≠ 0} : ℝ) ≤
        ∑ y : {g : G //
            g ∈ ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} :
              Set G) ∧ χ g ≠ 0},
          Complex.normSq (χ y.1) := by
  classical
  intro x hx hχx
  let supportFiber :=
    {g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x}
  let e :
      {y : G // y ∈ supportFiber ∧ χ y ≠ 0} ≃
        {g : G // Subgroup.zpowers g = Subgroup.zpowers x} :=
    { toFun := fun y => ⟨y.1, y.2.1.2⟩
      invFun := fun y =>
        ⟨y.1,
          ⟨(theorem_13_9_signed_nonzero_support_cycle_generators_source
              H Q G0 χ _hG0 _hχsigned x hx hχx y.1 y.2).1, y.2⟩,
          (theorem_13_9_signed_nonzero_support_cycle_generators_source
              H Q G0 χ _hG0 _hχsigned x hx hχx y.1 y.2).2⟩
      left_inv := by
        intro y
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl }
  letI : Fintype {g : G // Subgroup.zpowers g = Subgroup.zpowers x} :=
    Fintype.ofFinite _
  letI : Fintype {g : G // g ∈ supportFiber ∧ χ g ≠ 0} :=
    Fintype.ofFinite _
  have hgenerators :=
    theorem_13_9_signed_nonzero_support_cycle_generator_sum_normSq_source
      H Q G0 χ _hG0 _hχsigned x hx hχx
  calc
    (Nat.card {y : G // y ∈ supportFiber ∧ χ y ≠ 0} : ℝ) =
        (Nat.card {g : G // Subgroup.zpowers g = Subgroup.zpowers x} : ℝ) := by
      exact_mod_cast (Nat.card_congr e)
    _ ≤ ∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
          Complex.normSq (χ y.1) := by
      simpa using hgenerators
    _ ≤ ∑ y : {g : G // g ∈ supportFiber ∧ χ g ≠ 0},
          Complex.normSq (χ y.1) := by
      have hsum :
          (∑ y : {g : G // g ∈ supportFiber ∧ χ g ≠ 0},
              Complex.normSq (χ (e y).1)) =
            ∑ y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x},
              Complex.normSq (χ y.1) :=
        Equiv.sum_comp e
          (fun y : {g : G // Subgroup.zpowers g = Subgroup.zpowers x} =>
            Complex.normSq (χ y.1))
      have hpoint :
          (∑ y : {g : G // g ∈ supportFiber ∧ χ g ≠ 0},
              Complex.normSq (χ y.1)) =
            ∑ y : {g : G // g ∈ supportFiber ∧ χ g ≠ 0},
              Complex.normSq (χ (e y).1) := by
        refine Finset.sum_congr rfl ?_
        intro y _hy
        rfl
      exact le_of_eq (hpoint.trans hsum).symm

/- Checked wrapper from the nonzero cycle-support square-sum source leaf to the
full raw cycle square-sum. -/
private theorem theorem_13_9_signed_nonzero_support_cycle_representative_sum_normSq_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H Q : Subgroup G)
    (G0 : Set G)
    (χ : Section1.ClassFunction G)
    (_hG0 : theorem_13_9_G0Data H Q G0)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, x ∈ G0 → χ x ≠ 0 →
      (Nat.card {y : {z : G // z ∈ G0 ∧ χ z ≠ 0} //
          Subgroup.zpowers y.1 = Subgroup.zpowers x} : ℝ) ≤
        ∑ y : {g : G // g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x},
          Complex.normSq (χ y.1) := by
  classical
  intro x hx hχx
  let α := {z : G // z ∈ G0 ∧ χ z ≠ 0}
  let e :
      {y : α // Subgroup.zpowers y.1 = Subgroup.zpowers x} ≃
        {g : G //
          g ∈ ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} :
            Set G) ∧ χ g ≠ 0} :=
    { toFun := fun y => ⟨y.1.1, ⟨y.1.2.1, y.2⟩, y.1.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1.1, y.2.2⟩, y.2.1.2⟩
      left_inv := by
        intro y
        rfl
      right_inv := by
        intro y
        rfl }
  have hcard_eq :
      Nat.card {y : α // Subgroup.zpowers y.1 = Subgroup.zpowers x} =
        Nat.card {g : G //
          g ∈ ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} :
            Set G) ∧ χ g ≠ 0} :=
    Nat.card_congr e
  have hsource :=
    theorem_13_9_signed_nonzero_support_cycle_representative_nonzero_sum_normSq_source
      H Q G0 χ _hG0 _hχsigned x hx hχx
  have hmono :=
      theorem_13_9_sum_subtype_mono_of_subset
        ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} : Set G)
        (fun g : G => χ g ≠ 0) χ
  rw [hcard_eq]
  exact hsource.trans hmono

/- Checked wrapper from the raw representative-cycle square-sum bound to the
`supportEnergy` form consumed by the cycle-fiber aggregation. -/
private theorem theorem_13_9_signed_nonzero_support_cycle_representative_core_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H Q : Subgroup G)
    (G0 : Set G)
    (χ : Section1.ClassFunction G)
    (hG0 : theorem_13_9_G0Data H Q G0)
    (hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, x ∈ G0 → χ x ≠ 0 →
      (Nat.card {y : {z : G // z ∈ G0 ∧ χ z ≠ 0} //
          Subgroup.zpowers y.1 = Subgroup.zpowers x} : ℝ) ≤
        Section7.supportEnergy
          ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} : Set G)
          χ := by
  intro x hx hχx
  rw [theorem_13_9_supportEnergy_eq_sum_subtype]
  apply
    theorem_13_9_signed_nonzero_support_cycle_representative_sum_normSq_source
      H Q G0 χ hG0 hχsigned x hx hχx

private theorem theorem_13_9_signed_nonzero_support_cycle_representative_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hG0 : theorem_13_9_G0Data H Q G0)
    (hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ x : G, x ∈ G0 → χ x ≠ 0 →
      (Nat.card {y : {z : G // z ∈ G0 ∧ χ z ≠ 0} //
          Subgroup.zpowers y.1 = Subgroup.zpowers x} : ℝ) ≤
        Section7.supportEnergy
          ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = Subgroup.zpowers x} : Set G)
          χ := by
  exact theorem_13_9_signed_nonzero_support_cycle_representative_core_source
    H Q G0 χ hG0 hχsigned

private theorem theorem_13_9_signed_nonzero_support_cycle_fiber_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hG0 : theorem_13_9_G0Data H Q G0)
    (hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    ∀ L : Subgroup G,
      L ∈ Set.range
          (fun y : {z : G // z ∈ G0 ∧ χ z ≠ 0} =>
            Subgroup.zpowers y.1) →
        (Nat.card {y : {z : G // z ∈ G0 ∧ χ z ≠ 0} //
            Subgroup.zpowers y.1 = L} : ℝ) ≤
          Section7.supportEnergy
            ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = L} : Set G) χ := by
  intro L hL
  rcases hL with ⟨x, rfl⟩
  exact theorem_13_9_signed_nonzero_support_cycle_representative_lower_source
    Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT χ p q u v c d
    hsource hG0 hχsigned x.1 x.2.1 x.2.2

private theorem theorem_13_9_signed_nonzero_support_energy_lower_of_cycle_fibers
    {G : Type u} [Group G] [Finite G]
    (G0 : Set G) (χ : Section1.ClassFunction G)
    (hfiber : ∀ L : Subgroup G,
      L ∈ Set.range
          (fun y : {z : G // z ∈ G0 ∧ χ z ≠ 0} =>
            Subgroup.zpowers y.1) →
        (Nat.card {y : {z : G // z ∈ G0 ∧ χ z ≠ 0} //
            Subgroup.zpowers y.1 = L} : ℝ) ≤
          Section7.supportEnergy
            ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = L} : Set G) χ) :
    (Nat.card ({x : G | x ∈ G0 ∧ χ x ≠ 0} : Set G) : ℝ) ≤
      Section7.supportEnergy G0 χ := by
  classical
  let α := {z : G // z ∈ G0 ∧ χ z ≠ 0}
  let cycα : α → Subgroup G := fun y => Subgroup.zpowers y.1
  have hcard_eq :
      (Nat.card ({x : G | x ∈ G0 ∧ χ x ≠ 0} : Set G) : ℝ) =
        ∑ L : Subgroup G,
          (Nat.card {y : α // cycα y = L} : ℝ) := by
    calc
      (Nat.card ({x : G | x ∈ G0 ∧ χ x ≠ 0} : Set G) : ℝ) =
          ∑ _y : α, (1 : ℝ) := by
        simp [α, Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ = ∑ L : Subgroup G,
          ∑ y ∈ (Finset.univ : Finset α).filter (fun y => cycα y = L),
            (1 : ℝ) := by
        rw [← Finset.sum_fiberwise
          (s := (Finset.univ : Finset α))
          (g := cycα)
          (f := fun _y : α => (1 : ℝ))]
      _ = ∑ L : Subgroup G,
          (Nat.card {y : α // cycα y = L} : ℝ) := by
        apply Finset.sum_congr rfl
        intro L _
        simp [α, cycα, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hle_mid :
      (∑ L : Subgroup G, (Nat.card {y : α // cycα y = L} : ℝ)) ≤
        ∑ L : Subgroup G,
          Section7.supportEnergy
            ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = L} : Set G) χ := by
    apply Finset.sum_le_sum
    intro L _
    by_cases hL : L ∈ Set.range cycα
    · have hL' : L ∈ Set.range
          (fun y : {z : G // z ∈ G0 ∧ χ z ≠ 0} =>
            Subgroup.zpowers y.1) := by
        rcases hL with ⟨y, hy⟩
        exact ⟨y, hy⟩
      simpa [α, cycα] using hfiber L hL'
    · have hzero : (Nat.card {y : α // cycα y = L} : ℝ) = 0 := by
        have hempty : IsEmpty {y : α // cycα y = L} := by
          refine ⟨?_⟩
          intro y
          exact hL ⟨y.1, y.2⟩
        simp [Nat.card_eq_fintype_card]
      rw [hzero]
      rw [Section7.supportEnergy]
      exact Finset.sum_nonneg (by
        intro g _
        by_cases hg :
            g ∈ ({g : G | g ∈ G0 ∧ Subgroup.zpowers g = L} : Set G)
        · simp [hg, Complex.normSq_nonneg]
        · simp [hg])
  exact (le_of_eq hcard_eq).trans
    (hle_mid.trans
      (le_of_eq (theorem_13_9_supportEnergy_cycle_partition G0 χ)))


private theorem theorem_13_9_signed_nonzero_support_sum_normSq_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hG0 : theorem_13_9_G0Data H Q G0)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    (Nat.card ({x : G | x ∈ G0 ∧ χ x ≠ 0} : Set G) : ℝ) ≤
      ∑ x : {g : G // g ∈ G0}, Complex.normSq (χ x.1) := by
  rw [← theorem_13_9_supportEnergy_eq_sum_subtype]
  exact theorem_13_9_signed_nonzero_support_energy_lower_of_cycle_fibers G0 χ
    (theorem_13_9_signed_nonzero_support_cycle_fiber_lower_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT χ p q u v c d
      _hsource _hG0 _hχsigned)


private theorem theorem_13_9_signed_nonzero_support_energy_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hG0 : theorem_13_9_G0Data H Q G0)
    (_hχsigned : Section3.IsSignedIrreducibleCharacter χ) :
    (Nat.card ({x : G | x ∈ G0 ∧ χ x ≠ 0} : Set G) : ℝ) ≤
      Section7.supportEnergy G0 χ := by
  rw [theorem_13_9_supportEnergy_eq_sum_subtype]
  exact theorem_13_9_signed_nonzero_support_sum_normSq_lower_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT χ p q u v c d
      _hsource _hG0 _hχsigned

private theorem theorem_13_9_lambda_signedIrreducible_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    Section3.IsSignedIrreducibleCharacter lamτ := by
  rcases hhyp with ⟨_hG0, hlam_mem, h6hyp⟩
  rcases h6hyp with ⟨_hH, hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  rw [hlamτ_eq]
  exact Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
    hcoh hlam_mem hlam_irred

private theorem theorem_13_9_eta10_signedIrreducible_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    Section3.IsSignedIrreducibleCharacter (η 1 0) := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax, _hSFP,
      _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
      _hSType, _hTType, _hmax⟩
  rcases hnotation with
    ⟨homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμ0, _hν0, _hμdiff, _hνdiff, _hμsum, _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωeq⟩
  have h1q : 1 < q := by
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  have h0p : 0 < p := by
    simpa [hp_card] using (Nat.card_pos (α := W2))
  let i1 : Fin q := ⟨1, h1q⟩
  let j0 : Fin p := ⟨0, h0p⟩
  have hω_irred : Section1.IsIrreducibleCharacterOnGroup (ω 1 0) := by
    rw [hωeq 1 0 h1q h0p]
    exact hωFin.irreducible i1 j0
  have hω_class : Section1.IsClassFunction (ω 1 0) := by
    rw [hωeq 1 0 h1q h0p]
    exact hωFin.is_class i1 j0
  have hvirtW : Theory.Character.IsVirtualCharacter (ω 1 0) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hω_irred
  have hvirtG : Theory.Character.IsVirtualCharacter (σ (ω 1 0)) :=
    hσmap.2.1 (ω 1 0) hvirtW
  have hself : Section1.scalarProduct G (σ (ω 1 0)) (σ (ω 1 0)) = 1 := by
    calc
      Section1.scalarProduct G (σ (ω 1 0)) (σ (ω 1 0)) =
          Section1.scalarProduct W (ω 1 0) (ω 1 0) :=
        hσmap.1 (ω 1 0) (ω 1 0) hω_class hω_class
      _ = Section1.scalarProduct W (ωFin i1 j0) (ωFin i1 j0) := by
        rw [hωeq 1 0 h1q h0p]
      _ = 1 := by
        simpa using hωFin.orthonormal (i1, j0) (i1, j0)
  have heta10_sigma : η 1 0 = σ (ω 1 0) := hη 1 0 h1q h0p
  rw [heta10_sigma]
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirtG hself

/- Source leaf for PF `(13.9)(b)`: Isaacs Lemma 3.14 applied to the
nonzero support of `λ^τ₁` over `G₀`. -/
private theorem theorem_13_9_lambda_nonzero_support_energy_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    (Nat.card ({x : G | x ∈ G0 ∧ lamτ x ≠ 0} : Set G) : ℝ) ≤
      Section7.supportEnergy G0 lamτ := by
  exact theorem_13_9_signed_nonzero_support_energy_lower_source
    Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lamτ
    p q u v c d hsource hhyp.1
    (theorem_13_9_lambda_signedIrreducible_of_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      p q u v c d hsource hcoh hhyp)

/- Source leaf for PF `(13.9)(b)`: Isaacs Lemma 3.14 applied to the
nonzero support of `η₁₀` over `G₀`. -/
private theorem theorem_13_9_eta10_nonzero_support_energy_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    (Nat.card ({x : G | x ∈ G0 ∧ (η 1 0) x ≠ 0} : Set G) : ℝ) ≤
      Section7.supportEnergy G0 (η 1 0) := by
  exact theorem_13_9_signed_nonzero_support_energy_lower_source
    Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT (η 1 0)
    p q u v c d hsource hhyp.1
    (theorem_13_9_eta10_signedIrreducible_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation)

/- Checked package collecting the two PF `(13.9)(b)` support-set lower
bounds from the source proof. -/
private theorem theorem_13_9_nonzero_support_energy_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u) :
    ((Nat.card ({x : G | x ∈ G0 ∧ lamτ x ≠ 0} : Set G) : ℝ) ≤
        Section7.supportEnergy G0 lamτ) ∧
      (Nat.card ({x : G | x ∈ G0 ∧ (η 1 0) x ≠ 0} : Set G) : ℝ) ≤
        Section7.supportEnergy G0 (η 1 0) := by
  exact ⟨
    theorem_13_9_lambda_nonzero_support_energy_lower_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hcoh hhyp,
    theorem_13_9_eta10_nonzero_support_energy_lower_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hhyp⟩

/- Source leaf for PF `(13.9)(b)`: Isaacs Lemma 3.14 applied to the two
power-closed nonzero support sets from `(13.9)(a)` gives the lower bound. -/
private theorem theorem_13_9_supportEnergy_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hhyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u)
    (hnonvanishing : ∀ x : G, x ∈ G0 → lamτ x ≠ 0 ∨ (η 1 0) x ≠ 0) :
    (Nat.card G0 : ℝ) ≤
      Section7.supportEnergy G0 lamτ + Section7.supportEnergy G0 (η 1 0) := by
  rcases theorem_13_9_nonzero_support_energy_lower_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hcoh hhyp with
    ⟨hlamτ, heta10⟩
  exact theorem_13_9_supportEnergy_add_ge_card_of_nonzero_supports
    G0 lamτ (η 1 0) hnonvanishing hlamτ heta10

public theorem theorem_13_9
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        Section6.coherentExtension Sfam τS τ1 →
          theorem_13_3_characterOutputFor Smax P C Sfam τ1 p q u μsum η →
            theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u →
              (∀ x : G, x ∈ G0 → lamτ x ≠ 0 ∨ (η 1 0) x ≠ 0) ∧
                (Nat.card G0 : ℝ) ≤
                  Section7.supportEnergy G0 lamτ + Section7.supportEnergy G0 (η 1 0) := by
  intro hsource hnotation hcoh houtput hhyp
  have hnonvanishing :
      ∀ x : G, x ∈ G0 → lamτ x ≠ 0 ∨ (η 1 0) x ≠ 0 :=
    theorem_13_9_nonvanishing_source
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hcoh houtput hhyp
  refine ⟨hnonvanishing, ?_⟩
  exact theorem_13_9_supportEnergy_lower_source
    Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τ1 τT lam lamτ
    ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hcoh hhyp hnonvanishing
end CFSG.Section13
