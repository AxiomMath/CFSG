module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_19
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.19) -/


section theorem_13_19_source

variable {G : Type u} [Group G] [Finite G]
variable (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
variable (Sfam : Finset (Section1.ClassFunction Smax))
variable (Tfam : Finset (Section1.ClassFunction Tmax))
variable (Lfam : Finset (Section1.ClassFunction L))
variable (R : G → Subgroup G)
variable (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
variable (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
variable (τL τL1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
variable (φL : Section1.ClassFunction L)
variable (βL βS φ : Section1.ClassFunction G)
variable (ω : ℕ → ℕ → Section1.ClassFunction W)
variable (η : ℕ → ℕ → Section1.ClassFunction G)
variable (μ : ℕ → ℕ → Section1.ClassFunction Smax)
variable (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
variable (μsum : ℕ → Section1.ClassFunction Smax)
variable (νsum : ℕ → Section1.ClassFunction Tmax)
variable (δ δ' : ℕ → ℤ)
variable (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
variable (p q u v c d e : ℕ)


private theorem theorem_13_19_H_card_coprime_pq
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    Nat.Coprime (Nat.card H) p ∧ Nat.Coprime (Nat.card H) q := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨hcase, htypePS, htypePT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, hMin, _hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := hMin
  rcases h19 with
    ⟨hLmax, hHMF, hTypeI, _he, _hDadeL, _hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWhat,
      hSmax, hTmax, hSMF, hTMF, _hSeq, _hTeq,
      _hSdisj, _hTdisj, _hST, _hII, hStypes, hTtypes, _hclass⟩
  have htypePSOrig := htypePS
  have htypePTOrig := htypePT
  rcases htypePS with
    ⟨_hSMF', _hW1cyc, _hW1ne', _hW1hall, _hScomp, _hUle, _hUnil,
      _hW1norm, _hDcomp, _hPnotcyc, _hsecond, _hfit, _hfitD,
      hW2lePinf, _hW2cyc, _hW2ne', _hcentS, _hnormS⟩
  rcases htypePT with
    ⟨_hTMF', _hW2cyc', _hW2ne'', _hW2hall, _hTcomp, _hVle, _hVnil,
      _hW2norm, _hDcompT, _hQnotcyc, _hsecondT, _hfitT, _hfitDT,
      hW1leQinf, _hW1cyc', _hW1ne'', _hcentT, _hnormT⟩
  have hp : Nat.Prime p :=
    section13_prime_q_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c (section13_hypothesis_13_1_sourceData_swap hsourceOrig)
  have hq : Nat.Prime q :=
    section13_prime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  constructor
  · exact section13_coprime_card_typeI_mf_of_typeP_prime
      hChoice hLmax hHMF hTypeI hSmax hSMF htypePSOrig hStypes
      (hW2lePinf.trans inf_le_left) hp hp_card.symm
  · exact section13_coprime_card_typeI_mf_of_typeP_prime
      hChoice hLmax hHMF hTypeI hTmax hTMF htypePTOrig hTtypes
      (hW1leQinf.trans inf_le_left) hq hq_card.symm

/-- Source leaf for PF `(13.19)(a)`: the Type-I Dade support
`\widetilde A(L)` avoids `P^G ∪ W^G`. -/
private theorem theorem_13_19_support_disjoint_source
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    Disjoint (Section2.dadeSupport (Section12.typeIASet L H) R)
      (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
        section16ConjugatesOfSetBySet (W : Set G) Set.univ) := by
  classical
  have hsourceOrig := _hsource
  have h19Orig := _h19
  rcases _hsource with
    ⟨hcase, _htypePS, _htypePT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := hMin
  rcases _h19 with
    ⟨hLmax, hHMF, hTypeI, _he, hDadeL, _hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  rcases hcase with
    ⟨hWprod, _hWcyc, _hW1ne, _hW2ne, _hWhat,
      _hSmax, _hTmax, _hSMF, _hTMF, _hSeq, _hTeq,
      _hSdisj, _hTdisj, _hST, _hII, _hStypes, _hTtypes, _hclass⟩
  rcases theorem_13_19_H_card_coprime_pq
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ μ p q u v c d e hsourceOrig h19Orig with
    ⟨hcopHp, hcopHq⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hAeq :
      Section12.typeIASet L H = section16NonidentityElements (H : Set G) :=
    Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrob
  have hHyp2 :
      Section2.Hypothesis2 (Section12.typeIASet L H) L R :=
    hDadeL.1
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig with
    ⟨_hSMF', _hStype, _hStypeLarge, _hUcomm, _hfrobUW1, _hPelem,
      hPcard, _huBound, _hcohS, _hBook, _hTau, _hNorm⟩
  have hWint : Section2.IsInternalDirectProduct W W1 W2 :=
    section13_isInternalDirectProduct_of_section12InternalDirectProduct hWprod
  have hWcard : Nat.card W = Nat.card W1 * Nat.card W2 := by
    simpa using
      (Nat.card_congr (Section3.internalDirectProductMulEquiv hWint).toEquiv).symm
  have hcopHP : Nat.Coprime (Nat.card H) (Nat.card P) := by
    rw [hPcard]
    exact hcopHp.pow_right q
  have hcopHW : Nat.Coprime (Nat.card H) (Nat.card W) := by
    rw [hWcard, ← hq_card, ← hp_card]
    exact hcopHq.mul_right hcopHp
  have horderConj : ∀ g y : G, orderOf (g * y * g⁻¹) = orderOf y := by
    intro g y
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq y
  rw [Set.disjoint_left]
  intro x hxDade hxPW
  rcases hxDade with ⟨a, haA, r, hrR, hconj⟩
  have haHsharp : a ∈ section16NonidentityElements (H : Set G) := by
    simpa only [hAeq] using haA
  have hrCent : r ∈ Section2.elementCentralizer a :=
    (hHyp2.centralizer_eq_product haA).left_le hrR
  have har : Commute a r := by
    unfold Section2.elementCentralizer at hrCent
    rw [Subgroup.mem_centralizer_iff] at hrCent
    exact hrCent a (by simp)
  have haCL : a ∈ Section2.centralizerIn L a := by
    refine Subgroup.mem_inf.mpr ⟨hHyp2.subset_L a haA, ?_⟩
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    simp
  have hordaC : orderOf a ∣ Nat.card (Section2.centralizerIn L a) :=
    Subgroup.orderOf_dvd_natCard (Section2.centralizerIn L a) haCL
  have hordrR : orderOf r ∣ Nat.card (R a) :=
    Subgroup.orderOf_dvd_natCard (R a) hrR
  have hcopar : Nat.Coprime (orderOf a) (orderOf r) :=
    Nat.Coprime.of_dvd_right hordrR
      (Nat.Coprime.of_dvd_left hordaC
        (hHyp2.coprime_orders haA haA).symm)
  have hordar : orderOf (a * r) = orderOf a * orderOf r :=
    har.orderOf_mul_eq_mul_orderOf_of_coprime hcopar
  rcases hconj with ⟨g, hg⟩
  have hordarX : orderOf (a * r) = orderOf x := by
    calc
      orderOf (a * r) = orderOf (Section2.conjBy g x) :=
        congrArg orderOf hg.symm
      _ = orderOf x := by
        simpa [Section2.conjBy] using horderConj g x
  have hordaX : orderOf a ∣ orderOf x := by
    rw [← hordarX, hordar]
    exact dvd_mul_right _ _
  have hordaH : orderOf a ∣ Nat.card H :=
    Subgroup.orderOf_dvd_natCard H haHsharp.1
  rcases hxPW with hxP | hxW
  · rcases hxP with ⟨y, hyP, g, _hg, hxy⟩
    have hordxP : orderOf x ∣ Nat.card P := by
      rw [hxy, horderConj]
      exact Subgroup.orderOf_dvd_natCard P hyP
    have hordaP : orderOf a ∣ Nat.card P := hordaX.trans hordxP
    have horda1 : orderOf a = 1 :=
      Nat.eq_one_of_dvd_coprimes hcopHP hordaH hordaP
    exact haHsharp.2 (orderOf_eq_one_iff.mp horda1)
  · rcases hxW with ⟨y, hyW, g, _hg, hxy⟩
    have hordxW : orderOf x ∣ Nat.card W := by
      rw [hxy, horderConj]
      exact Subgroup.orderOf_dvd_natCard W hyW
    have hordaW : orderOf a ∣ Nat.card W := hordaX.trans hordxW
    have horda1 : orderOf a = 1 :=
      Nat.eq_one_of_dvd_coprimes hcopHW hordaH hordaW
    exact haHsharp.2 (orderOf_eq_one_iff.mp horda1)


private theorem theorem_13_19_Lfam_sub_conj_integerSpanOn
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section5.integerSpanOn Lfam Section5.puncturedSet
      (ψ - Section1.conjugateCharacter ψ) := by
  rcases h19 with
    ⟨_hLmax, hMF, _hTypeI, _he, _hDadeL, hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hψconj :
      Section1.conjugateCharacter ψ ∈ Lfam :=
    Section12.puncturedInducedFamily_conjugate_mem
      L H Lfam hHnormal hPunctL ψ hψ
  have hψchar : Section1.IsCharacter ψ := by
    rcases (hPunctL ψ).mp hψ with ⟨θ, hθirr, _hθne, hψeq⟩
    rw [hψeq]
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  refine ⟨Section5.integerSpan_sub
      (Section5.integerSpan_of_mem Lfam hψ)
      (Section5.integerSpan_of_mem Lfam hψconj), ?_⟩
  apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
  change Section1.degree ψ -
      Section1.degree (Section1.conjugateCharacter ψ) = 0
  rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hψchar]
  simp


private theorem theorem_13_19_Lfam_conj_orthogonal
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct L ψ (Section1.conjugateCharacter ψ) = 0 := by
  rcases h19 with
    ⟨_hLmax, hMF, hTypeI, _he, _hDadeL, hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hoddL : Odd (Nat.card L) :=
    Section12.odd_card_of_typeIDefinitionData L H hTypeI
  letI : (H.subgroupOf L).Normal := hHnormal
  rcases (hPunctL ψ).mp hψ with ⟨θ, hθirr, hθne, hψeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθrep_ne_principal :
      ρ.character ≠ Section1.principalCharacter (H.subgroupOf L) := by
    intro hρprincipal
    exact hθne (by rw [hθeq, hρprincipal])
  have horth :
      Section1.scalarProduct L
        (Section1.inducedCF (H.subgroupOf L) ρ.character)
        (Section1.conjugateCharacter
          (Section1.inducedCF (H.subgroupOf L) ρ.character)) = 0 := by
    simpa [Section1.orthogonal] using
      (Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        (H.subgroupOf L) ρ hoddL hρirr hθrep_ne_principal)
  simpa [hψeq, hθeq] using horth

/-- Symmetric form of `theorem_13_19_Lfam_conj_orthogonal`. -/
private theorem theorem_13_19_Lfam_conj_orthogonal_swap
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct L (Section1.conjugateCharacter ψ) ψ = 0 := by
  have horth :
      Section1.scalarProduct L ψ (Section1.conjugateCharacter ψ) = 0 :=
    theorem_13_19_Lfam_conj_orthogonal
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  simpa [Section1.scalarProduct_star_swap] using congrArg star horth


private theorem theorem_13_19_Lfam_irreducible_of_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.IsIrreducibleCharacterOnGroup ψ := by
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  rcases h19 with
    ⟨hLmax, hMF, hTypeI, _he, hDadeL, hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  letI : IsMinCE G := hMin
  have h12 :
      Section12.hypothesis_12_1_data L H Lfam R τL :=
    ⟨hLmax, hMF, hTypeI, hPunctL, hDadeL⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hMF hTypeI
  exact Section12.theorem_12_6_irreducible_of_frobenius
    L H Lfam R τL h12 hfrob ψ hψ


private theorem theorem_13_19_Lfam_scalarProduct_self
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct L ψ ψ = 1 := by
  exact Section1.scalarProduct_irreducibleCharacter_self
    (theorem_13_19_Lfam_irreducible_of_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsource h19 hψ)


private theorem theorem_13_19_Lfam_sub_conj_scalarProduct_self
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct L
      (ψ - Section1.conjugateCharacter ψ)
      (ψ - Section1.conjugateCharacter ψ) =
        Section1.scalarProduct L ψ ψ +
          Section1.scalarProduct L
            (Section1.conjugateCharacter ψ) (Section1.conjugateCharacter ψ) := by
  have horth :
      Section1.scalarProduct L ψ (Section1.conjugateCharacter ψ) = 0 :=
    theorem_13_19_Lfam_conj_orthogonal
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  have horth' :
      Section1.scalarProduct L (Section1.conjugateCharacter ψ) ψ = 0 :=
    theorem_13_19_Lfam_conj_orthogonal_swap
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
    Section5.scalarProduct_sub_right, horth, horth']
  ring


private theorem theorem_13_19_tauL1_eq_tauL_on_sub_conj
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    τL1 (ψ - Section1.conjugateCharacter ψ) =
      τL (ψ - Section1.conjugateCharacter ψ) := by
  have h19Full := h19
  rcases h19 with
    ⟨_hLmax, _hMF, _hTypeI, _he, _hDadeL, _hPunctL, hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  exact hcohL.2.2 (ψ - Section1.conjugateCharacter ψ)
    (theorem_13_19_Lfam_sub_conj_integerSpanOn
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Full hψ)


private theorem theorem_13_19_tauL1_sub_conj_virtualCharacter
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Theory.Character.IsVirtualCharacter
      (τL1 (ψ - Section1.conjugateCharacter ψ)) := by
  have h19Full := h19
  rcases h19 with
    ⟨_hLmax, _hMF, _hTypeI, _he, _hDadeL, _hPunctL, hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  exact hcohL.2.1 (ψ - Section1.conjugateCharacter ψ)
    (theorem_13_19_Lfam_sub_conj_integerSpanOn
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Full hψ).1


private theorem theorem_13_19_tauL1_sub_conj_scalarProduct_self
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct G
      (τL1 (ψ - Section1.conjugateCharacter ψ))
      (τL1 (ψ - Section1.conjugateCharacter ψ)) =
        Section1.scalarProduct L
          (ψ - Section1.conjugateCharacter ψ)
          (ψ - Section1.conjugateCharacter ψ) := by
  have h19Full := h19
  rcases h19 with
    ⟨_hLmax, _hMF, _hTypeI, _he, _hDadeL, _hPunctL, hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  have hZ :
      Section5.integerSpanOn Lfam Section5.puncturedSet
        (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_Lfam_sub_conj_integerSpanOn
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Full hψ
  exact hcohL.1
    (ψ - Section1.conjugateCharacter ψ)
    (ψ - Section1.conjugateCharacter ψ) hZ.1 hZ.1


private theorem theorem_13_19_Lfam_sub_conj_scalarProduct_self_two
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct L
      (ψ - Section1.conjugateCharacter ψ)
      (ψ - Section1.conjugateCharacter ψ) = 2 := by
  have hsum :
      Section1.scalarProduct L
        (ψ - Section1.conjugateCharacter ψ)
        (ψ - Section1.conjugateCharacter ψ) =
          Section1.scalarProduct L ψ ψ +
            Section1.scalarProduct L
              (Section1.conjugateCharacter ψ) (Section1.conjugateCharacter ψ) :=
    theorem_13_19_Lfam_sub_conj_scalarProduct_self
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  have hψself : Section1.scalarProduct L ψ ψ = 1 :=
    theorem_13_19_Lfam_scalarProduct_self
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsource h19 hψ
  have hconjself :
      Section1.scalarProduct L
        (Section1.conjugateCharacter ψ) (Section1.conjugateCharacter ψ) = 1 := by
    rw [Section12.scalarProduct_conjugateCharacter_conjugateCharacter]
    exact hψself
  rw [hsum, hψself, hconjself]
  norm_num


private theorem theorem_13_19_tauL1_sub_conj_scalarProduct_self_two
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct G
      (τL1 (ψ - Section1.conjugateCharacter ψ))
      (τL1 (ψ - Section1.conjugateCharacter ψ)) = 2 := by
  rw [theorem_13_19_tauL1_sub_conj_scalarProduct_self
        (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
        (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
        (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
        h19 hψ,
      theorem_13_19_Lfam_sub_conj_scalarProduct_self_two
        (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
        (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
        (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
        (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
        (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
        (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
        hsource h19 hψ]


private theorem theorem_13_19_tauL1_Lfam_signed_irreducible
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section3.IsSignedIrreducibleCharacter (τL1 ψ) := by
  have h19Full := h19
  have hψspan : Section5.integerSpan Lfam ψ :=
    Section5.integerSpan_of_mem Lfam hψ
  have hvirt : Theory.Character.IsVirtualCharacter (τL1 ψ) := by
    rcases h19 with
      ⟨_hLmax, _hMF, _hTypeI, _he, _hDadeL, _hPunctL, hcohL,
        _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
    exact hcohL.2.1 ψ hψspan
  have hself : Section1.scalarProduct G (τL1 ψ) (τL1 ψ) = 1 := by
    rcases h19 with
      ⟨_hLmax, _hMF, _hTypeI, _he, _hDadeL, _hPunctL, hcohL,
        _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
    calc
      Section1.scalarProduct G (τL1 ψ) (τL1 ψ) =
          Section1.scalarProduct L ψ ψ := hcohL.1 ψ ψ hψspan hψspan
      _ = 1 :=
          theorem_13_19_Lfam_scalarProduct_self
            (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
            (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
            (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam)
            (Lfam := Lfam) (R := R) (τS := τS) (τT := τT)
            (τL := τL) (τL1 := τL1) (φL := φL) (βL := βL)
            (βS := βS) (φ := φ) (μ := μ) (p := p) (q := q)
            (u := u) (v := v) (c := c) (d := d) (e := e)
            hsource h19Full hψ
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt hself


private theorem theorem_13_19_sigma_omega_signed_irreducible
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {i j : ℕ} (hi : i < q) (hj : j < p) :
    Section3.IsSignedIrreducibleCharacter (σ (ω i j)) := by
  rcases hnotation with
    ⟨hωData, hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩
  rcases hωData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  let iFin : Fin q := ⟨i, hi⟩
  let jFin : Fin p := ⟨j, hj⟩
  have hω_irred : Section1.IsIrreducibleCharacterOnGroup (ω i j) := by
    rw [hωNat i j hi hj]
    exact hωFin.irreducible iFin jFin
  have hω_class : Section1.IsClassFunction (ω i j) := by
    rw [hωNat i j hi hj]
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
            rw [hωNat i j hi hj]
      _ = 1 := by
            simpa using hωFin.orthonormal (iFin, jFin) (iFin, jFin)
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirtG hself


private theorem theorem_13_19_signed_eq_or_neg_of_scalarProduct_ne_zero
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hχψ : Section1.scalarProduct G χ ψ ≠ 0) :
    ψ = χ ∨ ψ = -χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, hχeq⟩
  rcases hψ with ⟨δ, hδ, ν, hν, hψeq⟩
  by_cases hμν : μ = ν
  · subst hμν
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · left
      simp [hχeq, hψeq]
    · right
      simp [hχeq, hψeq]
    · right
      simp [hχeq, hψeq]
    · left
      simp [hχeq, hψeq]
  · have horth : Section1.scalarProduct G μ ν = 0 := by
      exact Section1.scalarProduct_isBookIrreducible_ne μ ν
        (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hμ)
        (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hν)
        hμν
    exfalso
    apply hχψ
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · simpa [hχeq, hψeq] using horth
    · have hzero : Section1.scalarProduct G μ ((-1 : ℂ) • ν) = 0 := by
        rw [Section1.scalarProduct_smul_right, horth]
        simp
      simpa [hχeq, hψeq] using hzero
    · have hzero : Section1.scalarProduct G ((-1 : ℂ) • μ) ν = 0 := by
        rw [Section1.scalarProduct_smul_left, horth]
        simp
      simpa [hχeq, hψeq] using hzero
    · have hzero :
        Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • ν) = 0 := by
        rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, horth]
        simp
      simpa [hχeq, hψeq] using hzero


private theorem theorem_13_19_tauL1_sub_conj_scalarProduct_tauL1_self
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.scalarProduct G
      (τL1 (ψ - Section1.conjugateCharacter ψ)) (τL1 ψ) = 1 := by
  have h19Full := h19
  have hsubspan :
      Section5.integerSpan Lfam (ψ - Section1.conjugateCharacter ψ) :=
    (theorem_13_19_Lfam_sub_conj_integerSpanOn
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Full hψ).1
  have hψspan : Section5.integerSpan Lfam ψ :=
    Section5.integerSpan_of_mem Lfam hψ
  have hψself : Section1.scalarProduct L ψ ψ = 1 :=
    theorem_13_19_Lfam_scalarProduct_self
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam)
      (Lfam := Lfam) (R := R) (τS := τS) (τT := τT)
      (τL := τL) (τL1 := τL1) (φL := φL) (βL := βL)
      (βS := βS) (φ := φ) (μ := μ) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) (e := e)
      hsource h19Full hψ
  have hconjOrth :
      Section1.scalarProduct L (Section1.conjugateCharacter ψ) ψ = 0 :=
    theorem_13_19_Lfam_conj_orthogonal_swap
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Full hψ
  rcases h19 with
    ⟨_hLmax, _hMF, _hTypeI, _he, _hDadeL, _hPunctL, hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  calc
    Section1.scalarProduct G
        (τL1 (ψ - Section1.conjugateCharacter ψ)) (τL1 ψ) =
        Section1.scalarProduct L (ψ - Section1.conjugateCharacter ψ) ψ :=
          hcohL.1 (ψ - Section1.conjugateCharacter ψ) ψ hsubspan hψspan
    _ = Section1.scalarProduct L ψ ψ -
          Section1.scalarProduct L (Section1.conjugateCharacter ψ) ψ := by
          rw [Section5.scalarProduct_sub_left]
    _ = 1 := by
          rw [hψself, hconjOrth]
          norm_num


private theorem theorem_13_19_tauL1_sub_conj_sigma_omega_ne_zero_of_signed
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam)
    {i j : ℕ}
    (hsign : σ (ω i j) = τL1 ψ ∨ σ (ω i j) = -τL1 ψ) :
    Section1.scalarProduct G
      (τL1 (ψ - Section1.conjugateCharacter ψ)) (σ (ω i j)) ≠ 0 := by
  have hmain :
      Section1.scalarProduct G
        (τL1 (ψ - Section1.conjugateCharacter ψ)) (τL1 ψ) = 1 :=
    theorem_13_19_tauL1_sub_conj_scalarProduct_tauL1_self
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsource h19 hψ
  rcases hsign with hsign | hsign
  · rw [hsign, hmain]
    norm_num
  · rw [hsign]
    have hneg :
        Section1.scalarProduct G
          (τL1 (ψ - Section1.conjugateCharacter ψ)) (-τL1 ψ) = -1 := by
      rw [show -τL1 ψ = (-1 : ℂ) • τL1 ψ by ext x; simp]
      rw [Section1.scalarProduct_smul_right, hmain]
      norm_num
    rw [hneg]
    norm_num


private theorem theorem_13_19_sub_conj_CFOn_typeIASet
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section2.CFOn L (Section12.typeIASet L H)
      (ψ - Section1.conjugateCharacter ψ) := by
  rcases h19 with
    ⟨_hLmax, hMF, _hTypeI, _he, _hDadeL, hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le hMF
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  letI : (H.subgroupOf L).Normal := hHnormal
  have hψchar : Section1.IsCharacter ψ := by
    rcases (hPunctL ψ).mp hψ with ⟨θ, hθirr, _hθne, hψeq⟩
    rw [hψeq]
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hψclass : Section1.IsClassFunction ψ := by
    rcases (hPunctL ψ).mp hψ with ⟨θ, _hθirr, _hθne, hψeq⟩
    rw [hψeq]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θ
  refine ⟨?_, ?_⟩
  · intro x g
    simp [Pi.sub_apply, Section1.conjugateCharacter, hψclass x g]
  · intro l hlA
    by_cases hl1 : l = 1
    · subst hl1
      change Section1.degree ψ -
          Section1.degree (Section1.conjugateCharacter ψ) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hψchar]
      simp
    · have hlH : l ∉ H.subgroupOf L := by
        intro hlH
        have hlg_ne : (l : G) ≠ 1 := by
          intro hlg
          exact hl1 (Subtype.ext hlg)
        exact hlA
          (Section12.nonidentity_kernel_subset_typeIASet L H hHleL
            ⟨hlH, hlg_ne⟩)
      have hψ0 : ψ l = 0 :=
        Section12.puncturedInducedFamily_eq_zero_of_not_mem
          (H.subgroupOf L) hPunctL hψ hlH
      simp [Pi.sub_apply, Section1.conjugateCharacter, hψ0]


private theorem theorem_13_19_tauL1_sub_conj_supportedOn_dadeSupport
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.supportedOn
      (τL1 (ψ - Section1.conjugateCharacter ψ))
      (Section2.dadeSupport (Section12.typeIASet L H) R) := by
  have h19Full := h19
  have hDtau1 :
      τL1 (ψ - Section1.conjugateCharacter ψ) =
        τL (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_tauL1_eq_tauL_on_sub_conj
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  rcases h19 with
    ⟨_hLmax, _hMF, _hTypeI, _he, hDadeL, _hPunctL, _hcohL,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  rcases hDadeL with ⟨_h22L, hτpackL⟩
  rcases hτpackL with ⟨hALG_L, hτeqL⟩
  have hCFOn :
      Section2.CFOn L (Section12.typeIASet L H)
        (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_sub_conj_CFOn_typeIASet
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Full hψ
  rw [hDtau1, hτeqL (ψ - Section1.conjugateCharacter ψ) hCFOn]
  exact Section12.supportedOn_dadeTransform_dadeSupport hALG_L
    (ψ - Section1.conjugateCharacter ψ)


private theorem theorem_13_19_finite_orthonormal_virtual_coeff_support_card_le_two
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (hχvirt : ∀ i, Theory.Character.IsVirtualCharacter (χ i))
    {Y : Section1.ClassFunction G}
    (hYvirt : Theory.Character.IsVirtualCharacter Y)
    (hYnorm : Section5.cfNormSq Y = 2) :
    Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} ≤ 2 := by
  classical
  let nz : Finset ι :=
    Finset.univ.filter fun i : ι => Section1.scalarProduct G Y (χ i) ≠ 0
  have hterms : ∀ i ∈ nz,
      (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G Y (χ i)) := by
    intro i hi
    have hi_ne : Section1.scalarProduct G Y (χ i) ≠ 0 := by
      change i ∈ Finset.univ.filter
        (fun i : ι => Section1.scalarProduct G Y (χ i) ≠ 0) at hi
      exact (Finset.mem_filter.mp hi).2
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int
        hYvirt (hχvirt i) with
      ⟨z, hz⟩
    have hz_ne : (z : ℂ) ≠ 0 := by
      intro hz0
      exact hi_ne (by simpa [hz] using hz0)
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hz_ne (by simp [hz0])
    have hzz : (1 : ℤ) ≤ z * z := by
      have hpos : 0 < z * z := (mul_self_pos).2 hz0
      omega
    have hreal : (1 : ℝ) ≤ (z : ℝ) * (z : ℝ) := by
      exact_mod_cast hzz
    rw [hz]
    simpa [Complex.normSq, pow_two] using hreal
  have hcard_le_sum :
      (nz.card : ℝ) ≤
        ∑ i ∈ nz, Complex.normSq (Section1.scalarProduct G Y (χ i)) := by
    calc
      (nz.card : ℝ) = ∑ _i ∈ nz, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ nz, Complex.normSq (Section1.scalarProduct G Y (χ i)) :=
        Finset.sum_le_sum (fun i hi => hterms i hi)
  have hsum_subset :
      ∑ i ∈ nz, Complex.normSq (Section1.scalarProduct G Y (χ i)) ≤
        ∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp)
      (by intro i _hiuniv _hinz; exact Complex.normSq_nonneg _)
  have hsum_bound :
      ∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i)) ≤ 2 := by
    have hBessel :=
      theorem_13_18_finite_orthonormal_coeff_normSq_sum_le_cfNormSq χ horth Y
    rwa [hYnorm] at hBessel
  have hcard_real : (nz.card : ℝ) ≤ 2 :=
    le_trans hcard_le_sum (le_trans hsum_subset hsum_bound)
  have hcard_nat : nz.card ≤ 2 := by
    exact_mod_cast hcard_real
  have hcard_eq :
      Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} = nz.card := by
    dsimp [nz]
    rw [Fintype.card_subtype]
  simpa [hcard_eq] using hcard_nat

/-- Checked pointwise form of the PF `(13.19)(b)` cyclic-TI `NC` count:
`tau1 (ψ - ψ^*)` has no nonzero `σ(ωᵢⱼ)` coefficient. -/
private theorem theorem_13_19_tauL1_sub_conj_sigma_omega_count_zero_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ ψ : Section1.ClassFunction L, ψ ∈ Lfam →
      ∀ i j : ℕ, i < q → j < p →
        Section1.scalarProduct G
          (τL1 (ψ - Section1.conjugateCharacter ψ)) (σ (ω i j)) = 0 := by
  classical
  intro ψ hψ
  rcases hnotation with
    ⟨⟨h31, hq, hp, ωFin, hωFin, hωNat⟩, hσmap, _hη, _hδ, _hδ',
      _hμirr, _hνirr, _hμzero, _hνzero, _hμind, _hνind,
      _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩
  let Ψ : Section1.ClassFunction G :=
    τL1 (ψ - Section1.conjugateCharacter ψ)
  have hΨvirt : Theory.Character.IsVirtualCharacter Ψ := by
    dsimp [Ψ]
    exact theorem_13_19_tauL1_sub_conj_virtualCharacter
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  have hΨself : Section1.scalarProduct G Ψ Ψ = 2 := by
    dsimp [Ψ]
    exact theorem_13_19_tauL1_sub_conj_scalarProduct_self_two
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsource h19 hψ
  have hΨnorm : Section5.cfNormSq Ψ = 2 := by
    unfold Section5.cfNormSq
    rw [hΨself]
    norm_num
  let χ : Fin q × Fin p → Section1.ClassFunction G :=
    fun ij => σ (ωFin ij.1 ij.2)
  have hχorth : ∀ ij kl : Fin q × Fin p,
      Section1.scalarProduct G (χ ij) (χ kl) = if ij = kl then 1 else 0 := by
    intro ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    dsimp [χ]
    calc
      Section1.scalarProduct G (σ (ωFin i j)) (σ (ωFin k l)) =
          Section1.scalarProduct W (ωFin i j) (ωFin k l) :=
        hσmap.1 (ωFin i j) (ωFin k l)
          (hωFin.is_class i j) (hωFin.is_class k l)
      _ = if (i, j) = (k, l) then 1 else 0 := hωFin.orthonormal (i, j) (k, l)
  have hχvirt : ∀ ij : Fin q × Fin p,
      Theory.Character.IsVirtualCharacter (χ ij) := by
    intro ij
    exact hσmap.2.1 (ωFin ij.1 ij.2)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hωFin.irreducible ij.1 ij.2))
  let a : Fin q → Fin p → ℂ :=
    fun i j => Section1.scalarProduct G Ψ (σ (ωFin i j))
  have hacount : Section3.coefficientNonzeroCount a ≤ 2 := by
    have hcount :=
      theorem_13_19_finite_orthonormal_virtual_coeff_support_card_le_two
        χ hχorth hχvirt hΨvirt hΨnorm
    simpa [Section3.coefficientNonzeroCount, a, χ] using hcount
  have hΨsupport : Section1.supportedOn Ψ
      (Section2.dadeSupport (Section12.typeIASet L H) R) := by
    dsimp [Ψ]
    exact theorem_13_19_tauL1_sub_conj_supportedOn_dadeSupport
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  have hdisj :
      Disjoint (Section2.dadeSupport (Section12.typeIASet L H) R)
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) :=
    theorem_13_19_support_disjoint_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource
      ⟨⟨h31, hq, hp, ωFin, hωFin, hωNat⟩, hσmap, _hη, _hδ, _hδ',
        _hμirr, _hνirr, _hμzero, _hνzero, _hμind, _hνind,
        _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩ h19
  have hΨvanish : Section3.VanishesOn Ψ (Section3.cyclicTISet W1 W2 W) := by
    rw [Section1.supportedOn_iff] at hΨsupport
    intro g hg
    apply hΨsupport g
    intro hgSupport
    have hgWconj :
        g ∈ section16ConjugatesOfSetBySet (W : Set G) Set.univ := by
      refine ⟨g, Section3.cyclicTISet_subset W1 W2 W hg,
        1, Set.mem_univ _, ?_⟩
      simp
    exact (Set.disjoint_left.mp hdisj hgSupport) (Or.inr hgWconj)
  have hΨclass : Section1.IsClassFunction Ψ :=
    Section1.isVirtualCharacter_isClassFunction hΨvirt
  have harect : ∀ i i' j j', a i j + a i' j' = a i j' + a i' j := by
    intro i i' j j'
    have hzero :=
      Section3.scalarProduct_vanishes_rectangle_eq_zero_of_agrees
        hωFin hσmap.2.2.1 hΨclass hΨvanish i i' j j'
    have hzero' :
        Section1.scalarProduct G Ψ (σ (ωFin i j)) +
            Section1.scalarProduct G Ψ (σ (ωFin i' j')) -
            Section1.scalarProduct G Ψ (σ (ωFin i j')) -
            Section1.scalarProduct G Ψ (σ (ωFin i' j)) = 0 := by
      simpa [Section3.omegaRectangle, Section5.scalarProduct_add_right,
        Section5.scalarProduct_sub_right] using hzero
    dsimp [a]
    linear_combination hzero'
  have haZero : ∀ i j, a i j = 0 :=
    Section3.coefficients_zero_of_rectangle_count_le_two
      W1 W2 W (Fin q) (Fin p) ⟨0, hq⟩ ⟨0, hp⟩ ωFin a
      h31 hωFin harect hacount
  intro i j hi hj
  have hij := haZero ⟨i, hi⟩ ⟨j, hj⟩
  change Section1.scalarProduct G Ψ (σ (ωFin ⟨i, hi⟩ ⟨j, hj⟩)) = 0 at hij
  rw [← hωNat i j hi hj] at hij
  simpa [Ψ] using hij


private theorem theorem_13_19_tauL1_sub_conj_orthogonal_of_supportedOn_PWG
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam)
    (χ : Section1.ClassFunction G)
    (hχ : Section1.supportedOn χ
      (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
        section16ConjugatesOfSetBySet (W : Set G) Set.univ)) :
    Section1.scalarProduct G
      (τL1 (ψ - Section1.conjugateCharacter ψ)) χ = 0 := by
  have hPsiSupp :
      Section1.supportedOn
        (τL1 (ψ - Section1.conjugateCharacter ψ))
        (Section2.dadeSupport (Section12.typeIASet L H) R) :=
    theorem_13_19_tauL1_sub_conj_supportedOn_dadeSupport
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19 hψ
  have hdisj :
      Disjoint (Section2.dadeSupport (Section12.typeIASet L H) R)
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) :=
    theorem_13_19_support_disjoint_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19
  exact Section12.scalarProduct_eq_zero_of_supportedOn_disjoint
    hPsiSupp hχ hdisj


private theorem theorem_13_19_tauL1_sigma_omega_table_source
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ ψ : Section1.ClassFunction L, ψ ∈ Lfam →
      ∀ i j : ℕ, i < q → j < p →
        Section1.scalarProduct G (τL1 ψ) (σ (ω i j)) = 0 := by
  intro ψ hψ i j hiq hjp
  have hZsubL :
      Section5.integerSpanOn Lfam Section5.puncturedSet
        (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_Lfam_sub_conj_integerSpanOn
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hSourceConjOrth :
      Section1.scalarProduct L ψ (Section1.conjugateCharacter ψ) = 0 :=
    theorem_13_19_Lfam_conj_orthogonal
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hSourceConjOrth' :
      Section1.scalarProduct L (Section1.conjugateCharacter ψ) ψ = 0 :=
    theorem_13_19_Lfam_conj_orthogonal_swap
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hTau1SubConjSelf :
      Section1.scalarProduct G
        (τL1 (ψ - Section1.conjugateCharacter ψ))
        (τL1 (ψ - Section1.conjugateCharacter ψ)) =
          Section1.scalarProduct L
            (ψ - Section1.conjugateCharacter ψ)
            (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_tauL1_sub_conj_scalarProduct_self
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hSourceSubConjSelf :
      Section1.scalarProduct L
        (ψ - Section1.conjugateCharacter ψ)
        (ψ - Section1.conjugateCharacter ψ) =
          Section1.scalarProduct L ψ ψ +
            Section1.scalarProduct L
              (Section1.conjugateCharacter ψ) (Section1.conjugateCharacter ψ) :=
    theorem_13_19_Lfam_sub_conj_scalarProduct_self
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hDtau1 :
      τL1 (ψ - Section1.conjugateCharacter ψ) =
        τL (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_tauL1_eq_tauL_on_sub_conj
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hZtau1 :
      Theory.Character.IsVirtualCharacter
        (τL1 (ψ - Section1.conjugateCharacter ψ)) :=
    theorem_13_19_tauL1_sub_conj_virtualCharacter
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hPsiSupp :
      Section1.supportedOn
        (τL1 (ψ - Section1.conjugateCharacter ψ))
        (Section2.dadeSupport (Section12.typeIASet L H) R) :=
    theorem_13_19_tauL1_sub_conj_supportedOn_dadeSupport
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      _h19 hψ
  have hSubConjOrthPWG :
      ∀ χ : Section1.ClassFunction G,
        Section1.supportedOn χ
          (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
            section16ConjugatesOfSetBySet (W : Set G) Set.univ) →
          Section1.scalarProduct G
            (τL1 (ψ - Section1.conjugateCharacter ψ)) χ = 0 :=
    theorem_13_19_tauL1_sub_conj_orthogonal_of_supportedOn_PWG
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (ω := ω) (η := η)
      (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum) (δ := δ)
      (δ' := δ') (σ := σ) (p := p) (q := q) (u := u) (v := v)
      (c := c) (d := d) (e := e) _hsource _hnotation _h19 hψ
  have hTau1SubConjSelfTwo :
      Section1.scalarProduct G
        (τL1 (ψ - Section1.conjugateCharacter ψ))
        (τL1 (ψ - Section1.conjugateCharacter ψ)) = 2 :=
    theorem_13_19_tauL1_sub_conj_scalarProduct_self_two
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      _hsource _h19 hψ
  have hTau1PsiSigned :
      Section3.IsSignedIrreducibleCharacter (τL1 ψ) :=
    theorem_13_19_tauL1_Lfam_signed_irreducible
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      _hsource _h19 hψ
  have hSigmaOmegaSigned :
      Section3.IsSignedIrreducibleCharacter (σ (ω i j)) :=
    theorem_13_19_sigma_omega_signed_irreducible
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (ω := ω) (η := η) (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
      (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q)
      _hnotation hiq hjp
  have hSignedDeta_of_nonzero :
      Section1.scalarProduct G (τL1 ψ) (σ (ω i j)) ≠ 0 →
        σ (ω i j) = τL1 ψ ∨ σ (ω i j) = -τL1 ψ := by
    intro hnonzero
    exact theorem_13_19_signed_eq_or_neg_of_scalarProduct_ne_zero
      hTau1PsiSigned hSigmaOmegaSigned hnonzero
  -- concrete `w_ i j` table entry, now with the checked `PsiV0`/PWG
  -- orthogonality consequence available as `hSubConjOrthPWG`.
  by_contra hnonzero
  have hsign : σ (ω i j) = τL1 ψ ∨ σ (ω i j) = -τL1 ψ :=
    hSignedDeta_of_nonzero hnonzero
  have hcoeff_ne :
      Section1.scalarProduct G
        (τL1 (ψ - Section1.conjugateCharacter ψ)) (σ (ω i j)) ≠ 0 :=
    theorem_13_19_tauL1_sub_conj_sigma_omega_ne_zero_of_signed
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (ω := ω) (σ := σ) (p := p) (q := q) (u := u) (v := v)
      (c := c) (d := d) (e := e) _hsource _h19 hψ hsign
  have hcoeff_zero :
      Section1.scalarProduct G
        (τL1 (ψ - Section1.conjugateCharacter ψ)) (σ (ω i j)) = 0 :=
    theorem_13_19_tauL1_sub_conj_sigma_omega_count_zero_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (ω := ω)
      (η := η) (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
      (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q) (u := u)
      (v := v) (c := c) (d := d) (e := e) _hsource _hnotation _h19
      ψ hψ i j hiq hjp
  exact hcoeff_ne hcoeff_zero


private theorem theorem_13_19_tauL1_sigma_omega_orthogonality_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ ψ : Section1.ClassFunction L, ψ ∈ Lfam →
      ∀ i j : ℕ, i < q → j < p →
        Section1.scalarProduct G (τL1 ψ) (σ (ω i j)) = 0 := by
  exact theorem_13_19_tauL1_sigma_omega_table_source
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
    τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
    p q u v c d e hsource hnotation h19


private theorem theorem_13_19_orthogonality_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ ψ : Section1.ClassFunction L, ψ ∈ Lfam →
      ∀ i j : ℕ, i < q → j < p →
        Section1.scalarProduct G (τL1 ψ) (η i j) = 0 := by
  intro ψ hψ i j hiq hjp
  rcases hnotation with
    ⟨_hωData, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩
  have hω :
      Section1.scalarProduct G (τL1 ψ) (σ (ω i j)) = 0 :=
    theorem_13_19_tauL1_sigma_omega_orthogonality_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource
      ⟨_hωData, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩ h19
      ψ hψ i j hiq hjp
  simpa [hη i j hiq hjp] using hω

/-- Checked PF `(13.19)` zero-row Dade-difference rewrite.  This is the
displayed textbook identity
`η_0j - η_01 = (μ_0j - μ_01)^τ`, obtained from the Section 13
Dade-difference data and the sign normalization from `(13.3)`. -/
private theorem theorem_13_19_tauS_mu_zero_row_difference_source_bridge
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (j : ℕ) (hj0 : 0 < j) (hjp : j < p) :
    τS (μ 0 j - μ 0 1) = η 0 j - η 0 1 := by
  classical
  have hsourceFull := hsource
  have hnotationFull := hnotation
  rcases hnotation with
    ⟨hωData, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD,
      _hc_card, _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS,
      _hDadeT, _hnotationData, hDadeDiff, hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, _hMin, _hFourSixS,
      _hFourSixT⟩
  have hp1 : 1 < p := by omega
  have hsign :
      theorem_13_3_signNormalizationFor p q δ δ' :=
    ((theorem_13_3 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceFull).1
      ω η μ ν μsum νsum δ δ' σ hnotationFull).1
  have hdeg :
      Section1.degree (μ 0 j) = Section1.degree (μ 0 1) :=
    (hZeroDegree ω η μ ν μsum νsum δ δ' σ hnotationFull).1
      j 1 hj0 hjp zero_lt_one hp1
  have hdiff :
      τS (μ 0 j - μ 0 1) =
        (((δ j : ℤ) : ℂ) • (σ (ω 0 j) - σ (ω 0 1))) :=
    (hDadeDiff ω η μ ν μsum νsum δ δ' σ hnotationFull).1
      0 j 1 hqpos hj0 hjp zero_lt_one hp1 hdeg
  have hδj : δ j = 1 := hsign.1 j hjp
  have hηj : η 0 j = σ (ω 0 j) := hη 0 j hqpos hjp
  have hη1 : η 0 1 = σ (ω 0 1) := hη 0 1 hqpos hp1
  calc
    τS (μ 0 j - μ 0 1)
        = (((δ j : ℤ) : ℂ) • (σ (ω 0 j) - σ (ω 0 1))) := hdiff
    _ = η 0 j - η 0 1 := by
          rw [hδj]
          simp [hηj, hη1]

/-- The Type-I beta input `Ind_H^L 1 - φ` is defined on `A(L)`.  This is the
local PF13 version of the support calculation used later in Section 14. -/
private theorem theorem_13_19_betaInput_CFOn_typeIASet
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {φL : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hPunct : Section7.puncturedInducedFamily (H.subgroupOf L) Lfam)
    (hφmem : φL ∈ Lfam)
    (hφdeg : Section1.degree φL = (H.relIndex L : ℂ)) :
    Section2.CFOn L (Section12.typeIASet L H)
      (Section7.theorem_7_8_betaInput L H φL) := by
  classical
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le hMF
  haveI : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  rcases (hPunct φL).mp hφmem with ⟨θφ, _hθφ, _hθφne, hφeq⟩
  have hprincipalClass :
      Section1.IsClassFunction (Section7.principalInducedCharacter L H) := by
    unfold Section7.principalInducedCharacter
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L)
      (Section1.principalCharacter (H.subgroupOf L))
  have hφclass : Section1.IsClassFunction φL := by
    rw [hφeq]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θφ
  constructor
  · intro x g
    simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
      hprincipalClass x g, hφclass x g]
  · intro l hlA
    have hprincipal_degree :
        Section1.degree (Section7.principalInducedCharacter L H) =
          (H.relIndex L : ℂ) := by
      unfold Section7.principalInducedCharacter
      rw [Section1.degree_inducedClassFunction]
      simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
    have hprincipal_one :
        Section7.principalInducedCharacter L H (1 : L) = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hprincipal_degree
    have hφ_one : φL 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hφdeg
    have hβ_one : Section7.theorem_7_8_betaInput L H φL (1 : L) = 0 := by
      simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
        hprincipal_one, hφ_one]
    by_cases hl_one : l = 1
    · simpa [hl_one] using hβ_one
    · have hl_ne_oneG : (l : G) ≠ 1 := by
        intro hG
        apply hl_one
        ext
        exact hG
      have hlnotH : (l : G) ∉ H := by
        intro hlH
        apply hlA
        exact Section12.nonidentity_kernel_subset_typeIASet L H hHleL
          ⟨hlH, hl_ne_oneG⟩
      have hlnotHsub : l ∉ H.subgroupOf L := by
        intro hlHsub
        exact hlnotH hlHsub
      have hprincipal_zero :
          Section7.principalInducedCharacter L H l = 0 := by
        unfold Section7.principalInducedCharacter
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) (Section1.principalCharacter (H.subgroupOf L)) hlnotHsub
      have hφ_zero : φL l = 0 := by
        rw [hφeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θφ hlnotHsub
      simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
        hprincipal_zero, hφ_zero]

/-- Checked support of the PF `(13.19)` Type-I beta transform on the Type-I
Dade support. -/
private theorem theorem_13_19_betaL_supportedOn_dadeSupport
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    Section1.supportedOn βL (Section2.dadeSupport (Section12.typeIASet L H) R) := by
  rcases h19 with
    ⟨_hLmax, hMF, _hTypeI, he, hDadeL, hPunctL, _hcohL, hφmem,
      hφdeg_e, _hφτ, hβL, _hβS⟩
  let betaInput : Section1.ClassFunction L :=
    Section7.theorem_7_8_betaInput L H φL
  have hβL_eq : βL = τL betaInput := by
    simpa [betaInput, Section7.theorem_7_8_betaInput,
      Section7.principalInducedCharacter] using hβL
  have hCFOn :
      Section2.CFOn L (Section12.typeIASet L H) betaInput :=
    theorem_13_19_betaInput_CFOn_typeIASet hMF hPunctL hφmem (by
      simpa [he] using hφdeg_e)
  rcases hDadeL with ⟨_h22L, hτpackL⟩
  rcases hτpackL with ⟨hALG_L, hτeqL⟩
  rw [hβL_eq, hτeqL betaInput hCFOn]
  exact Section12.supportedOn_dadeTransform_dadeSupport hALG_L betaInput

private theorem theorem_13_19_isClassFunction_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρ, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private theorem theorem_13_19_betaPre_isClassFunction
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {k : ℕ} (hk : k < p) :
    Section1.IsClassFunction
      (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 k) := by
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  have hμclass : Section1.IsClassFunction (μ 0 k) :=
    theorem_13_19_isClassFunction_of_irreducible (hμirr 0 k hqpos hk)
  have hindClass :
      Section1.IsClassFunction
        (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) :=
    Section1.inducedCF_isClassFunction ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
  intro x g
  simp [hindClass x g, hμclass x g]

private theorem theorem_13_19_MF_le_derived_of_typeP
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 : Subgroup G}
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2) :
    P ≤ ambientDerivedSubgroup Smax := by
  rcases hTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hComp, _hUleD, _hUnil,
      _hW1normU, _hDerComp, _hPnotCyc, _hSecondLe, hFittingEq, hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormHatW⟩
  intro x hx
  exact hFittingLeD (by
    rw [← hFittingEq]
    exact (le_sup_left : P ≤ P ⊔ subgroupCentralizerIn Smax P) hx)

private theorem theorem_13_19_betaSupport_subset_typePFAZeroSet
    {G : Type u} [Group G] [Finite G]
    {Smax W W1 W2 P U : Subgroup G}
    (hW : section12InternalDirectProduct W1 W2 W)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2) :
    theorem_13_18_betaSupportSet Smax W W1 W2 P ⊆
      typePFAZeroSet Smax W1 W2 P := by
  intro x hx
  rcases hx with hxP | hxV
  · left
    refine ⟨x, hxP, ?_⟩
    refine ⟨?_, hxP.2⟩
    change x ∈ elementCentralizerIn (ambientDerivedSubgroup Smax) x
    rw [elementCentralizerIn]
    refine ⟨theorem_13_19_MF_le_derived_of_typeP hTypeP hxP.1, ?_⟩
    simp [Subgroup.mem_centralizer_iff]
  · right
    rcases hxV with ⟨w, hw, s, hs, rfl⟩
    refine ⟨w, ?_, s, hs, rfl⟩
    exact ⟨by simpa [← hW.2.2.1] using hw.1, hw.2⟩

private theorem theorem_13_19_betaSupportSet_subset_PWG
    {G : Type u} [Group G] [Finite G]
    (Smax W W1 W2 P : Subgroup G) :
    section16ConjugatesOfSetBySet
        (theorem_13_18_betaSupportSet Smax W W1 W2 P) Set.univ ⊆
      (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
        section16ConjugatesOfSetBySet (W : Set G) Set.univ) := by
  intro x hx
  rcases hx with ⟨z, hz, g, _hg, rfl⟩
  rcases hz with hzP | hzW
  · left
    exact ⟨z, hzP.1, g, Set.mem_univ g, rfl⟩
  · right
    rcases hzW with ⟨w, hw, s, _hs, rfl⟩
    refine ⟨w, hw.1, g * s, Set.mem_univ (g * s), ?_⟩
    group

private theorem theorem_13_19_inducedCFLinear_supportedOn_conjugatesOfSet
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {A : Set G}
    (χ : Section1.ClassFunction M)
    (hχ : Section2.CFOn M A χ) :
    Section1.supportedOn (Section1.inducedCFLinear M χ)
      (section16ConjugatesOfSetBySet A Set.univ) := by
  rw [Section1.supportedOn_iff]
  intro g hg
  rw [Section1.inducedCFLinear_apply]
  exact Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn M χ hχ (by
    intro hgconj
    apply hg
    rcases hgconj with ⟨a, ha, hga⟩
    rcases hga with ⟨x, hx⟩
    exact ⟨a, ha, x, Set.mem_univ x, by simpa [Section2.conjBy] using hx.symm⟩)

private theorem theorem_13_19_tauS_betaPre_supportedOn_PWG
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {k : ℕ} (hk0 : 0 < k) (hk : k < p) :
    Section1.supportedOn
      (τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 k))
      (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
        section16ConjugatesOfSetBySet (W : Set G) Set.univ) := by
  classical
  let β : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 k
  have hsourceFull := hsource
  rcases hsource with
    ⟨hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD,
      _hc_card, _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS,
      _hDadeT, _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, _hMin, _hFourSixS,
      _hFourSixT⟩
  have hβdef :
      β = Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 k := rfl
  have hBetaSupportNorm := hypothesis_13_1_betaSupportNormDataFor_of_sourceData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsourceFull
  have hβsupp :
      Section1.supportedOn β
        (subgroupSetPreimage Smax
          (theorem_13_18_betaSupportSet Smax W W1 W2 P)) :=
    (hBetaSupportNorm.1 ω η μ ν μsum νsum δ δ' σ β k
      hnotation hk0 hk hβdef).1
  have hβclass : Section1.IsClassFunction β := by
    simpa [β] using
      theorem_13_19_betaPre_isClassFunction
        (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
        (P := P) (ω := ω) (η := η) (μ := μ) (ν := ν)
        (μsum := μsum) (νsum := νsum) (δ := δ) (δ' := δ') (σ := σ)
        (p := p) (q := q) hnotation hk
  have hβCFOnSupport :
      Section2.CFOn Smax (theorem_13_18_betaSupportSet Smax W W1 W2 P) β := by
    refine ⟨hβclass, ?_⟩
    intro l hl
    exact (Section1.supportedOn_iff.mp hβsupp) l
      (by simpa [subgroupSetPreimage] using hl)
  have hβA0 :
      Section1.supportedOn β (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) := by
    rw [Section1.supportedOn_iff] at hβsupp ⊢
    intro x hx
    exact hβsupp x (by
      intro hxβ
      apply hx
      exact theorem_13_19_betaSupport_subset_typePFAZeroSet hcase.1 hSTypeP hxβ)
  have hβCFOnA0 : Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) β := by
    refine ⟨hβclass, ?_⟩
    intro l hl
    exact (Section1.supportedOn_iff.mp hβA0) l
      (by simpa [subgroupSetPreimage] using hl)
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceFull with
    ⟨_hMF, _hType, _hTypeII, _hUcomm, _hFrob, _hPelem, _hPcard,
      _huBound, _hcoh, _hBookA0, hTauA0, _hNormU⟩
  have hτeq : τS β = Section1.inducedCFLinear Smax β :=
    hTauA0.2 β hβCFOnA0
  have hIndSupp :
      Section1.supportedOn (Section1.inducedCFLinear Smax β)
        (section16ConjugatesOfSetBySet
          (theorem_13_18_betaSupportSet Smax W W1 W2 P) Set.univ) :=
    theorem_13_19_inducedCFLinear_supportedOn_conjugatesOfSet Smax β hβCFOnSupport
  rw [hτeq]
  rw [Section1.supportedOn_iff] at hIndSupp ⊢
  intro g hg
  exact hIndSupp g (by
    intro hgbeta
    exact hg (theorem_13_19_betaSupportSet_subset_PWG Smax W W1 W2 P hgbeta))


private theorem theorem_13_19_tauS_mu_zero_row_difference_supported_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ j : ℕ, 0 < j → j < p →
      Section1.supportedOn (τS (μ 0 j - μ 0 1))
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) := by
  intro j hj0 hjp
  let β1 : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 1
  let βj : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 j
  have hp1 : 1 < p := by omega
  have hβ1 :
      Section1.supportedOn (τS β1)
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) :=
    theorem_13_19_tauS_betaPre_supportedOn_PWG
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      zero_lt_one hp1
  have hβj :
      Section1.supportedOn (τS βj)
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) :=
    theorem_13_19_tauS_betaPre_supportedOn_PWG
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      hj0 hjp
  have harg : μ 0 j - μ 0 1 = β1 - βj := by
    ext x
    simp [β1, βj, Pi.sub_apply]
  rw [harg, map_sub]
  exact Section5.supportedOn_sub hβ1 hβj


private theorem theorem_13_19_betaL_tauS_mu_zero_row_difference_orthogonal_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct G βL (τS (μ 0 j - μ 0 1)) = 0 := by
  intro j hj0 hjp
  have hβsupp :
      Section1.supportedOn βL
        (Section2.dadeSupport (Section12.typeIASet L H) R) :=
    theorem_13_19_betaL_supportedOn_dadeSupport
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e) h19
  have hμsupp :
      Section1.supportedOn (τS (μ 0 j - μ 0 1))
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) :=
    theorem_13_19_tauS_mu_zero_row_difference_supported_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19 j hj0 hjp
  have hdisj :
      Disjoint (Section2.dadeSupport (Section12.typeIASet L H) R)
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) :=
    theorem_13_19_support_disjoint_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19
  exact Section12.scalarProduct_eq_zero_of_supportedOn_disjoint
    hβsupp hμsupp hdisj


private theorem theorem_13_19_betaL_eta_difference_orthogonal_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct G βL (η 0 j - η 0 1) = 0 := by
  intro j hj0 hjp
  have hdiff :
      τS (μ 0 j - μ 0 1) = η 0 j - η 0 1 :=
    theorem_13_19_tauS_mu_zero_row_difference_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation j hj0 hjp
  have horth :
      Section1.scalarProduct G βL (τS (μ 0 j - μ 0 1)) = 0 :=
    theorem_13_19_betaL_tauS_mu_zero_row_difference_orthogonal_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19 j hj0 hjp
  rwa [← hdiff]


private theorem theorem_13_19_betaL_eta_eq_eta01_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct G βL (η 0 j) =
        Section1.scalarProduct G βL (η 0 1) := by
  intro j hj0 hj
  have hzero :
      Section1.scalarProduct G βL (η 0 j - η 0 1) = 0 :=
    theorem_13_19_betaL_eta_difference_orthogonal_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19 j hj0 hj
  rw [Section5.scalarProduct_sub_right] at hzero
  exact sub_eq_zero.mp hzero

/-- Checked PF `(13.19)(c)` independence wrapper: once the source
`betaLeta` step identifies every `(β_L, η_0j)` with the base entry
`(β_L, η_01)`, independence in the non-base range is immediate. -/
private theorem theorem_13_19_independence_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    theorem_13_19_independenceData βL η p := by
  intro j k hj0 hj hk0 hk
  rw [theorem_13_19_betaL_eta_eq_eta01_source
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
        τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
        p q u v c d e hsource hnotation h19 j hj0 hj,
      theorem_13_19_betaL_eta_eq_eta01_source
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
        τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
        p q u v c d e hsource hnotation h19 k hk0 hk]


private theorem theorem_13_19_pf78_setup
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    ∃ T : Finset (Section1.ClassFunction L),
      Section7.hypothesis_7_6_statement (Section12.typeIASet L H) L H R T ∧
        Section7.agreesWithDadeTransform (Section12.typeIASet L H) L R τL ∧
        Section7.theorem_7_8_hypothesis L H T Lfam τL τL1 φL ∧
        e = H.relIndex L ∧
        H.relIndex L ≤ (Nat.card H - 1) / 2 := by
  classical
  have hsourceOrig := hsource
  have h19Orig := h19
  rcases hsource with
    ⟨_hcase, _hTypePS, _hTypePT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := hMin
  rcases h19 with
    ⟨hLmax, hMF, hTypeI, he, hDade, hPunctured, hExt,
      hφmem, hφdeg, _hφτ, _hβL, _hβS⟩
  have hφirr : Section1.IsIrreducibleCharacterOnGroup φL :=
    theorem_13_19_Lfam_irreducible_of_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsourceOrig h19Orig hφmem
  let T : Finset (Section1.ClassFunction L) :=
    insert (Section7.principalInducedCharacter L H) Lfam
  have hT : Section7.inducedFamilyNotation (H.subgroupOf L) T := by
    intro χ
    constructor
    · intro hχ
      rw [Finset.mem_insert] at hχ
      rcases hχ with hχ | hχ
      · exact ⟨Section1.principalCharacter (H.subgroupOf L),
          Section3.principalCharacter_isIrreducibleCharacterOnGroup,
          by simpa [Section7.principalInducedCharacter] using hχ⟩
      · rcases (hPunctured χ).mp hχ with ⟨θ, hθirr, _hθne, hχeq⟩
        exact ⟨θ, hθirr, hχeq⟩
    · rintro ⟨θ, hθirr, hχeq⟩
      rw [Finset.mem_insert]
      by_cases hθ : θ = Section1.principalCharacter (H.subgroupOf L)
      · left
        rw [hχeq, hθ]
        rfl
      · right
        exact (hPunctured χ).mpr ⟨θ, hθirr, hθ, hχeq⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hMF hTypeI
  have hAeq : Section12.typeIASet L H = Section7.puncturedSubgroupSet H := by
    calc
      Section12.typeIASet L H = section16NonidentityElements (H : Set G) :=
        Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrob
      _ = Section7.puncturedSubgroupSet H := by
        ext g
        simp [Section7.puncturedSubgroupSet, section16NonidentityElements]
  have h76 :
      Section7.hypothesis_7_6_statement (Section12.typeIASet L H) L H R T :=
    ⟨Section12.section16MFSubgroup_le hMF,
      Section12.section16MFSubgroup_subgroupOf_normal hMF,
      hDade.1, hAeq, hT⟩
  have hAgree :
      Section7.agreesWithDadeTransform (Section12.typeIASet L H) L R τL :=
    hDade.2
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hoddL : Odd (Nat.card L) :=
    Section12.odd_card_of_typeIDefinitionData L H hTypeI
  have hφbar : Section1.conjugateCharacter φL ∈ Lfam :=
    Section12.puncturedInducedFamily_conjugate_mem
      L H Lfam hHnormal hPunctured φL hφmem
  have hφne : φL ≠ Section1.conjugateCharacter φL :=
    Section12.puncturedInducedFamily_ne_conjugate
      L H Lfam hHnormal hoddL hPunctured φL hφmem
  have hφchar : Section1.IsCharacter φL := by
    rcases (hPunctured φL).mp hφmem with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hnonempty :
      Section5.integerSpanOnNonempty Lfam Section5.puncturedSet :=
    Section5.integerSpanOnNonempty_of_conjugate_pair
      hφmem hφbar hφne hφchar
  have hsrc : Section5.sourceVirtualCharacters Lfam :=
    Section12.sourceVirtualCharacters_of_puncturedInducedFamily
      L H Lfam hPunctured
  rcases hExt with ⟨hIso, hVirt, hAgreeSpan⟩
  have hcoherent : Section6.coherentFamily Lfam τL :=
    ⟨hsrc, hnonempty, τL1, hIso, hVirt, hAgreeSpan⟩
  have h78 : Section7.theorem_7_8_hypothesis L H T Lfam τL τL1 φL := by
    refine ⟨Section12.section16MFSubgroup_le hMF, ?_, hPunctured, hcoherent,
      ⟨hIso, hVirt, hAgreeSpan⟩, hφmem, hφirr, ?_⟩
    · intro χ
      constructor
      · intro hχ
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_insert]
          exact Or.inr hχ
        · intro hχprincipal
          have hzero :
              Section1.scalarProduct L (Section7.principalInducedCharacter L H) χ = 0 :=
            Section7.theorem_7_8_principalInduced_punctured_member_scalar
              hHnormal hPunctured hχ
          have hself :
              Section1.scalarProduct L (Section7.principalInducedCharacter L H)
                  (Section7.principalInducedCharacter L H) =
                (H.relIndex L : ℂ) :=
            Section7.theorem_7_8_principalInduced_self_scalar hHnormal
          have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
            haveI : (H.subgroupOf L).FiniteIndex := inferInstance
            have hrel : H.relIndex L ≠ 0 := by
              simpa [Subgroup.relIndex] using
                (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
            exact_mod_cast hrel
          apply hrel_ne
          calc
            (H.relIndex L : ℂ) =
                Section1.scalarProduct L (Section7.principalInducedCharacter L H)
                  (Section7.principalInducedCharacter L H) := hself.symm
            _ = Section1.scalarProduct L
                  (Section7.principalInducedCharacter L H) χ := by rw [hχprincipal]
            _ = 0 := hzero
      · rintro ⟨hχT, hχne⟩
        rw [Finset.mem_insert] at hχT
        rcases hχT with hχprincipal | hχ
        · exact False.elim (hχne hχprincipal)
        · exact hχ
    · simpa [he] using hφdeg
  have htwo : 2 * H.relIndex L ≤ Nat.card H - 1 :=
    Section7.theorem_7_11_two_mul_relIndex_le_card_sub_one
      IsMinCE.odd_order hfrob
  have hhalf : H.relIndex L ≤ (Nat.card H - 1) / 2 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      (by simpa [Nat.mul_comm] using htwo)
  exact ⟨T, h76, hAgree, h78, he, hhalf⟩


private theorem theorem_13_19_tauL1_conjugate
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e)
    {ψ : Section1.ClassFunction L}
    (hψ : ψ ∈ Lfam) :
    Section1.conjugateCharacter (τL1 ψ) =
      τL1 (Section1.conjugateCharacter ψ) := by
  classical
  have hsourceOrig := hsource
  have h19Orig := h19
  rcases hsource with
    ⟨_hcase, _hTypePS, _hTypePT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := hMin
  rcases h19 with
    ⟨_hLmax, hMF, hTypeI, _he, hDade, hPunctured, hExt,
      _hφmem, _hφdeg, _hφτ, _hβL, _hβS⟩
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hoddL : Odd (Nat.card L) :=
    Section12.odd_card_of_typeIDefinitionData L H hTypeI
  have hψbar : Section1.conjugateCharacter ψ ∈ Lfam :=
    Section12.puncturedInducedFamily_conjugate_mem
      L H Lfam hHnormal hPunctured ψ hψ
  have hψne : ψ ≠ Section1.conjugateCharacter ψ :=
    Section12.puncturedInducedFamily_ne_conjugate
      L H Lfam hHnormal hoddL hPunctured ψ hψ
  let A : Section1.ClassFunction G := τL1 ψ
  let B : Section1.ClassFunction G := τL1 (Section1.conjugateCharacter ψ)
  let Dψ : Section1.ClassFunction G := A - B
  have hAsigned : Section3.IsSignedIrreducibleCharacter A := by
    dsimp [A]
    exact theorem_13_19_tauL1_Lfam_signed_irreducible
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsourceOrig h19Orig hψ
  have hBsigned : Section3.IsSignedIrreducibleCharacter B := by
    dsimp [B]
    exact theorem_13_19_tauL1_Lfam_signed_irreducible
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
      (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
      (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
      hsourceOrig h19Orig hψbar
  have hAB : Section1.scalarProduct G A B = 0 := by
    dsimp [A, B]
    rw [hExt.1 ψ (Section1.conjugateCharacter ψ)
      (Section5.integerSpan_of_mem Lfam hψ)
      (Section5.integerSpan_of_mem Lfam hψbar)]
    exact theorem_13_19_Lfam_conj_orthogonal
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Orig hψ
  have hBA : Section1.scalarProduct G B A = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hAB
  have hAA : Section1.scalarProduct G A A = 1 :=
    Section12.scalarProduct_self_of_isSignedIrreducibleCharacter hAsigned
  have hDψA : Section1.scalarProduct G Dψ A = 1 := by
    dsimp [Dψ]
    rw [Section5.scalarProduct_sub_left, hAA, hBA]
    simp
  have hdiffOn :
      Section2.CFOn L (Section12.typeIASet L H)
        (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_sub_conj_CFOn_typeIASet
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Orig hψ
  have hagree :
      τL1 (ψ - Section1.conjugateCharacter ψ) =
        τL (ψ - Section1.conjugateCharacter ψ) :=
    theorem_13_19_tauL1_eq_tauL_on_sub_conj
      (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
      (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
      (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
      h19Orig hψ
  rcases hDade.2 with ⟨hAL, hτDade⟩
  have hτeq :
      τL (ψ - Section1.conjugateCharacter ψ) =
        Section2.dadeTransform R hAL
          (ψ - Section1.conjugateCharacter ψ) :=
    hτDade _ hdiffOn
  have hDψdef : Dψ = τL1 (ψ - Section1.conjugateCharacter ψ) := by
    dsimp [Dψ, A, B]
    rw [map_sub]
  have hDψskew : Section1.conjugateCharacter Dψ = -Dψ := by
    rw [hDψdef, hagree, hτeq]
    calc
      Section1.conjugateCharacter
          (Section2.dadeTransform R hAL
            (ψ - Section1.conjugateCharacter ψ)) =
          Section2.dadeTransform R hAL
            (Section1.conjugateCharacter
              (ψ - Section1.conjugateCharacter ψ)) :=
        Section12.conjugateCharacter_dadeTransform R hAL _
      _ = Section2.dadeTransform R hAL
            (-(ψ - Section1.conjugateCharacter ψ)) := by
        rw [Section12.conjugateCharacter_sub_conjugate_eq_neg]
      _ = -Section2.dadeTransform R hAL
            (ψ - Section1.conjugateCharacter ψ) := by
        rw [show -(ψ - Section1.conjugateCharacter ψ) =
            ((-1 : ℂ) • (ψ - Section1.conjugateCharacter ψ)) by simp]
        rw [Section12.dadeTransform_smul]
        simp
  have hconjAsigned :
      Section3.IsSignedIrreducibleCharacter (Section1.conjugateCharacter A) :=
    Section12.isSignedIrreducibleCharacter_conjugateCharacter hAsigned
  have hDψconjA :
      Section1.scalarProduct G Dψ (Section1.conjugateCharacter A) = -1 := by
    have hstar :
        star (Section1.scalarProduct G Dψ (Section1.conjugateCharacter A)) = -1 := by
      calc
        star (Section1.scalarProduct G Dψ (Section1.conjugateCharacter A)) =
            Section1.scalarProduct G (Section1.conjugateCharacter Dψ) A := by
          symm
          exact Section12.scalarProduct_conjugate_left Dψ A
        _ = Section1.scalarProduct G (-Dψ) A := by rw [hDψskew]
        _ = -Section1.scalarProduct G Dψ A := by
          rw [show -Dψ = ((-1 : ℂ) • Dψ) by simp,
            Section1.scalarProduct_smul_left]
          simp
        _ = -1 := by rw [hDψA]
    simpa using congrArg star hstar
  have hconjA_ne_A : Section1.conjugateCharacter A ≠ A := by
    intro hEq
    have hbad := hDψconjA
    rw [hEq] at hbad
    have : (1 : ℂ) = -1 := hDψA.symm.trans hbad
    norm_num at this
  have hconjA_ne_negA : Section1.conjugateCharacter A ≠ -A :=
    Section12.conjugateCharacter_ne_neg_of_signedIrreducible hAsigned
  have hAconjA :
      Section1.scalarProduct G A (Section1.conjugateCharacter A) = 0 :=
    Section12.scalarProduct_signedIrreducible_eq_zero_of_ne_and_ne_neg
      hAsigned hconjAsigned hconjA_ne_A hconjA_ne_negA
  have hBconjA :
      Section1.scalarProduct G B (Section1.conjugateCharacter A) = 1 := by
    have h := hDψconjA
    dsimp [Dψ] at h
    rw [Section5.scalarProduct_sub_left, hAconjA] at h
    simpa using congrArg Neg.neg h
  have hnonzero :
      Section1.scalarProduct G B (Section1.conjugateCharacter A) ≠ 0 := by
    rw [hBconjA]
    norm_num
  rcases Section12.signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
      hBsigned hconjAsigned hnonzero with hEq | hEq
  · exact hEq
  · have hBB : Section1.scalarProduct G B B = 1 :=
      Section12.scalarProduct_self_of_isSignedIrreducibleCharacter hBsigned
    have hbad : Section1.scalarProduct G B (Section1.conjugateCharacter A) = -1 := by
      rw [hEq, show -B = ((-1 : ℂ) • B) by simp,
        Section1.scalarProduct_smul_right, hBB]
      simp
    rw [hBconjA] at hbad
    norm_num at hbad

/-- Source leaf for the PF `(13.19)(c1)`/`(13.19)(c2)` parity and index
alternative after the independence step. -/
private theorem theorem_13_19_alternative_source
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h19 : theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
      (μ 0 1) βL βS e) :
    theorem_13_19_alternativeData H βL βS φ η p q u e := by
  classical
  have hsourceOrig := hsource
  have hnotationOrig := hnotation
  have h19Orig := h19
  rcases hsource with
    ⟨_hcase, _htypePS, _htypePT, _hpCard, _hqCard, _hC, _hD, _hcCard,
      _hdCard, _hUCard, _hVCard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := hMin
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hμ00, _hν00, _hμdeg, _hνdeg⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  rcases h19 with
    ⟨_hLmax, hMF, _hTypeI, _he, _hDadeL, hPunctL, hcohL,
      hφmem, hφdeg, hφeq, hβLeq, hβSeq⟩
  have hp : Nat.Prime p :=
    section13_prime_q_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c (section13_hypothesis_13_1_sourceData_swap hsourceOrig)
  have hp1 : 1 < p := hp.one_lt
  let βS0 : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 1
  have hβhyp : theorem_13_18_hypothesis Smax P W1 (μ 0 1) βS0 1 p :=
    ⟨zero_lt_one, hp1, rfl⟩
  have hβSdef : βS = τS βS0 := by
    simpa [βS0] using hβSeq
  rcases theorem_13_18 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS0 βS 1 p q u v c d
      hsourceOrig hnotationOrig hβhyp hβSdef with
    ⟨Γ, X, Y, η01, _hβsupp, _hβA0, _hβnorm, hη01, hΓdef,
      _hΓindep, hΓone, hΓreal, hΓvirt, hΓXY, hdecomp, hYnorm⟩
  rcases theorem_13_19_pf78_setup
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ μ p q u v c d e hsourceOrig h19Orig with
    ⟨T, h76, hAgree, h78, he, hhalf⟩
  rcases Section7.theorem_7_8_a (Section12.typeIASet L H) L H R T Lfam
      τL τL1 φL h76 hAgree h78 with
    ⟨a, r, hrem⟩
  have hremOrig := hrem
  rcases hrem with ⟨hprincipalImage, hrImage, hrOne, hremEq⟩
  have hrnorm : Section5.cfNormSq r ≤ (H.relIndex L : ℝ) - 1 :=
    Section7.theorem_7_8_b_remainder_bound
      (Section12.typeIASet L H) L H R T Lfam τL τL1 φL
      h76 hAgree h78 hhalf a r hremOrig
  have hβLdef : Section7.theorem_7_8_beta L H τL φL = βL := by
    simpa [Section7.theorem_7_8_beta, Section7.theorem_7_8_betaInput,
      Section7.principalInducedCharacter] using hβLeq.symm
  have hφdef : φ = τL1 φL := hφeq
  let ΓL : Section1.ClassFunction G :=
    βL - (Section1.principalCharacter G - φ)
  have hΓLreal : ΓL = Section1.conjugateCharacter ΓL := by
    let βinput : Section1.ClassFunction L :=
      Section7.theorem_7_8_betaInput L H φL
    let diff : Section1.ClassFunction L :=
      φL - Section1.conjugateCharacter φL
    have hβinputOn :
        Section2.CFOn L (Section12.typeIASet L H) βinput := by
      dsimp [βinput]
      exact theorem_13_19_betaInput_CFOn_typeIASet hMF hPunctL hφmem
        (by simpa [_he] using hφdeg)
    have hdiffOn : Section2.CFOn L (Section12.typeIASet L H) diff := by
      dsimp [diff]
      exact theorem_13_19_sub_conj_CFOn_typeIASet
        (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
        (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
        (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
        h19Orig hφmem
    have hsumOn :
        Section2.CFOn L (Section12.typeIASet L H) (βinput + diff) := by
      constructor
      · intro x g
        simp [Pi.add_apply, hβinputOn.1 x g, hdiffOn.1 x g]
      · intro x hx
        simp [Pi.add_apply, hβinputOn.2 x hx, hdiffOn.2 x hx]
    letI : (H.subgroupOf L).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hMF
    have hprincipalInducedReal :
        Section1.conjugateCharacter (Section7.principalInducedCharacter L H) =
          Section7.principalInducedCharacter L H := by
      unfold Section7.principalInducedCharacter
      rw [Section1.conjugateCharacter_inducedCF,
        Section1.conjugateCharacter_principalCharacter]
    have hconjInput :
        Section1.conjugateCharacter βinput = βinput + diff := by
      calc
        Section1.conjugateCharacter βinput =
            Section1.conjugateCharacter
              (Section7.principalInducedCharacter L H - φL) := by rfl
        _ = Section1.conjugateCharacter (Section7.principalInducedCharacter L H) -
              Section1.conjugateCharacter φL := by
            ext x
            simp [Section1.conjugateCharacter, Pi.sub_apply]
        _ = Section7.principalInducedCharacter L H -
              Section1.conjugateCharacter φL := by rw [hprincipalInducedReal]
        _ = (Section7.principalInducedCharacter L H - φL) +
              (φL - Section1.conjugateCharacter φL) := by
            ext x
            simp [Pi.sub_apply, Pi.add_apply]
        _ = βinput + diff := by rfl
    have hβtau : βL = τL βinput := by
      simpa [βinput, Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using hβLeq
    rcases hAgree with ⟨hAL, hτDade⟩
    have hτβ : τL βinput = Section2.dadeTransform R hAL βinput :=
      hτDade βinput hβinputOn
    have hτsum :
        τL (βinput + diff) =
          Section2.dadeTransform R hAL (βinput + diff) :=
      hτDade (βinput + diff) hsumOn
    have hconjβ :
        Section1.conjugateCharacter βL = βL + τL diff := by
      calc
        Section1.conjugateCharacter βL =
            Section1.conjugateCharacter (τL βinput) := by rw [hβtau]
        _ = Section1.conjugateCharacter
              (Section2.dadeTransform R hAL βinput) := by rw [hτβ]
        _ = Section2.dadeTransform R hAL
              (Section1.conjugateCharacter βinput) :=
            Section12.conjugateCharacter_dadeTransform R hAL βinput
        _ = Section2.dadeTransform R hAL (βinput + diff) := by rw [hconjInput]
        _ = τL (βinput + diff) := hτsum.symm
        _ = βL + τL diff := by rw [map_add, ← hβtau]
    have hagreeDiff : τL1 diff = τL diff := by
      dsimp [diff]
      exact theorem_13_19_tauL1_eq_tauL_on_sub_conj
        (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
        (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
        (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
        h19Orig hφmem
    have hτdiff :
        τL diff = φ - Section1.conjugateCharacter φ := by
      rw [← hagreeDiff]
      dsimp [diff]
      rw [map_sub,
        ← theorem_13_19_tauL1_conjugate
          Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
          τS τT τL τL1 φL βL βS φ μ p q u v c d e
          hsourceOrig h19Orig hφmem]
      simp only [← hφdef]
    have hconjΓL :
        Section1.conjugateCharacter ΓL =
          Section1.conjugateCharacter βL -
            (Section1.principalCharacter G - Section1.conjugateCharacter φ) := by
      ext x
      simp [ΓL, Section1.conjugateCharacter, Pi.sub_apply]
    rw [hconjΓL, hconjβ, hτdiff]
    ext x
    simp [ΓL, Pi.sub_apply, Pi.add_apply]
    ring
  have hΓLvirt : Theory.Character.IsVirtualCharacter ΓL := by
    have hβvirt : Theory.Character.IsVirtualCharacter βL := by
      rw [← hβLdef]
      exact Section7.theorem_7_8_beta_virtual h76 hAgree h78
    have hprincipalVirt :
        Theory.Character.IsVirtualCharacter (Section1.principalCharacter G) :=
      Section3.isVirtualCharacter_principalCharacter
    have hφvirt : Theory.Character.IsVirtualCharacter φ := by
      rw [hφdef]
      exact hcohL.2.1 φL (Section5.integerSpan_of_mem Lfam hφmem)
    exact Section3.isVirtualCharacter_sub hβvirt
      (Section3.isVirtualCharacter_sub hprincipalVirt hφvirt)
  have hΓLone :
      Section1.scalarProduct G ΓL (Section1.principalCharacter G) = 0 := by
    have hprincipalφ :
        Section1.scalarProduct G (Section1.principalCharacter G) φ = 0 := by
      rw [hφdef]
      exact hprincipalImage φL hφmem
    have hφprincipal :
        Section1.scalarProduct G φ (Section1.principalCharacter G) = 0 := by
      have hswap := Section1.scalarProduct_star_swap
        (G := G) (Section1.principalCharacter G) φ
      have hstarzero :
          star (Section1.scalarProduct G φ (Section1.principalCharacter G)) = 0 := by
        simpa [hprincipalφ] using hswap
      simpa using congrArg star hstarzero
    have hweightedOne :
        Section1.scalarProduct G
          (Section7.theorem_7_8_weightedSum Lfam τL1 (H.relIndex L))
          (Section1.principalCharacter G) = 0 := by
      have hsum :
          Section7.theorem_7_8_weightedSum Lfam τL1 (H.relIndex L) =
            fun g => ∑ ψ : Lfam,
              (((ψ : Section1.ClassFunction L) 1 /
                (((H.relIndex L : ℕ) : ℂ) *
                  (Section5.cfNormSq (ψ : Section1.ClassFunction L) : ℂ))) •
                τL1 (ψ : Section1.ClassFunction L)) g := by
        ext g
        simp only [Section7.theorem_7_8_weightedSum, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        exact (Finset.sum_attach Lfam
          (fun ψ : Section1.ClassFunction L =>
            ψ 1 / (((H.relIndex L : ℕ) : ℂ) *
              (Section5.cfNormSq ψ : ℂ)) * τL1 ψ g)).symm
      rw [hsum, Section1.scalarProduct_fintype_sum_left]
      refine Finset.sum_eq_zero ?_
      intro ψ _hψ
      have hprincipalψ := hprincipalImage
        (ψ : Section1.ClassFunction L) ψ.2
      have hψprincipal :
          Section1.scalarProduct G (τL1 (ψ : Section1.ClassFunction L))
            (Section1.principalCharacter G) = 0 := by
        have hswap := Section1.scalarProduct_star_swap
          (G := G) (Section1.principalCharacter G)
            (τL1 (ψ : Section1.ClassFunction L))
        have hstarzero :
            star (Section1.scalarProduct G (τL1 (ψ : Section1.ClassFunction L))
              (Section1.principalCharacter G)) = 0 := by
          simpa [hprincipalψ] using hswap
        simpa using congrArg star hstarzero
      rw [Section1.scalarProduct_smul_left, hψprincipal]
      simp
    have hβprincipal :
        Section1.scalarProduct G βL (Section1.principalCharacter G) = 1 := by
      rw [← hβLdef, hremEq, ← hφdef, Section1.scalarProduct_add_left,
        Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
        Section1.scalarProduct_smul_left]
      rw [theorem_13_18_scalarProduct_principalCharacter_self, hφprincipal,
        hweightedOne, hrOne]
      simp
    dsimp [ΓL]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_left,
      hβprincipal, theorem_13_18_scalarProduct_principalCharacter_self,
      hφprincipal]
    ring
  have hparity :=
    Section5.real_virtual_principal_orthogonal_scalarProduct_even
      IsMinCE.odd_order hΓLvirt hΓLreal hΓLone hΓvirt hΓreal
  let bSphi : ℂ := Section1.scalarProduct G βS φ
  let bLeta : ℂ := Section1.scalarProduct G βL η01
  have hφvirt : Theory.Character.IsVirtualCharacter φ := by
    rw [hφdef]
    exact hcohL.2.1 φL (Section5.integerSpan_of_mem Lfam hφmem)
  have hβLvirt : Theory.Character.IsVirtualCharacter βL := by
    rw [← hβLdef]
    exact Section7.theorem_7_8_beta_virtual h76 hAgree h78
  have hηvirt : Theory.Character.IsVirtualCharacter η01 := by
    rw [hη01]
    exact theorem_13_18_eta_virtual_of_notation Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ hnotationOrig 0 1 hqpos hp1
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section1.principalCharacter G) :=
    Section3.isVirtualCharacter_principalCharacter
  have hβSvirt : Theory.Character.IsVirtualCharacter βS := by
    have hηprincipal : Theory.Character.IsVirtualCharacter η01 := hηvirt
    have hEq : βS = Γ + Section1.principalCharacter G - η01 := by
      rw [hΓdef]
      ext x
      simp only [Pi.add_apply, Pi.sub_apply, Section1.principalCharacter]
      ring
    rw [hEq]
    exact Section3.isVirtualCharacter_sub
      (Section3.isVirtualCharacter_add hΓvirt hprincipalVirt) hηprincipal
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hβSvirt hφvirt with
    ⟨zS, hzS⟩
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hβLvirt hηvirt with
    ⟨zL, hzL⟩
  have hbSstar : star bSphi = bSphi := by
    dsimp [bSphi]
    rw [hzS]
    simp
  have hηprincipal :
      Section1.scalarProduct G η01 (Section1.principalCharacter G) = 0 := by
    rw [hη01]
    exact theorem_13_18_eta_zero_row_principal_orthogonal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
      hnotationOrig 1 zero_lt_one hp1
  have hprincipalη :
      Section1.scalarProduct G (Section1.principalCharacter G) η01 = 0 := by
    have hswap := Section1.scalarProduct_star_swap
      (G := G) η01 (Section1.principalCharacter G)
    have hstarzero :
        star (Section1.scalarProduct G (Section1.principalCharacter G) η01) = 0 := by
      simpa [hηprincipal] using hswap
    simpa using congrArg star hstarzero
  have hprincipalφ :
      Section1.scalarProduct G (Section1.principalCharacter G) φ = 0 := by
    rw [hφdef]
    exact hprincipalImage φL hφmem
  have hφprincipal :
      Section1.scalarProduct G φ (Section1.principalCharacter G) = 0 := by
    have hswap := Section1.scalarProduct_star_swap
      (G := G) (Section1.principalCharacter G) φ
    have hstarzero :
        star (Section1.scalarProduct G φ (Section1.principalCharacter G)) = 0 := by
      simpa [hprincipalφ] using hswap
    simpa using congrArg star hstarzero
  have hβLprincipal :
      Section1.scalarProduct G βL (Section1.principalCharacter G) = 1 := by
    dsimp [ΓL] at hΓLone
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_left,
      theorem_13_18_scalarProduct_principalCharacter_self, hφprincipal] at hΓLone
    linear_combination hΓLone
  have hβSprincipal :
      Section1.scalarProduct G βS (Section1.principalCharacter G) = 1 := by
    rw [hΓdef, Section1.scalarProduct_add_left,
      Section5.scalarProduct_sub_left,
      theorem_13_18_scalarProduct_principalCharacter_self,
      hηprincipal] at hΓone
    linear_combination hΓone
  have hprincipalβS :
      Section1.scalarProduct G (Section1.principalCharacter G) βS = 1 := by
    have hswap := Section1.scalarProduct_star_swap
      (G := G) βS (Section1.principalCharacter G)
    calc
      Section1.scalarProduct G (Section1.principalCharacter G) βS =
          star (Section1.scalarProduct G βS (Section1.principalCharacter G)) := by
            simpa using congrArg star hswap
      _ = 1 := by rw [hβSprincipal]; simp
  have hβLβS : Section1.scalarProduct G βL βS = 0 := by
    have hβLsupp :
        Section1.supportedOn βL
          (Section2.dadeSupport (Section12.typeIASet L H) R) :=
      theorem_13_19_betaL_supportedOn_dadeSupport
        (Smax := Smax) (P := P) (W1 := W1) (L := L) (H := H)
        (Lfam := Lfam) (R := R) (τS := τS) (τL := τL) (τL1 := τL1)
        (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ) (e := e)
        h19Orig
    have hβSsupp :
        Section1.supportedOn βS
          (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
            section16ConjugatesOfSetBySet (W : Set G) Set.univ) := by
      rw [hβSdef]
      exact theorem_13_19_tauS_betaPre_supportedOn_PWG
        (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
        (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
        (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
        (ω := ω) (η := η) (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
        (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q) (u := u)
        (v := v) (c := c) (d := d) hsourceOrig hnotationOrig zero_lt_one hp1
    have hdisj := theorem_13_19_support_disjoint_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsourceOrig hnotationOrig h19Orig
    exact Section12.scalarProduct_eq_zero_of_supportedOn_disjoint
      hβLsupp hβSsupp hdisj
  have hφη : Section1.scalarProduct G φ η01 = 0 := by
    rw [hφdef, hη01]
    exact theorem_13_19_orthogonality_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsourceOrig hnotationOrig h19Orig φL hφmem 0 1 hqpos hp1
  have hφβS : Section1.scalarProduct G φ βS = bSphi := by
    have hswap := Section1.scalarProduct_star_swap (G := G) βS φ
    calc
      Section1.scalarProduct G φ βS = star bSphi := by
        simpa [bSphi] using congrArg star hswap
      _ = bSphi := hbSstar
  have hcross :
      Section1.scalarProduct G ΓL Γ = bSphi + bLeta - 1 := by
    rw [hΓdef]
    dsimp [ΓL, bLeta]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_left,
      Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right]
    rw [hβLβS, hβLprincipal, hprincipalβS,
      theorem_13_18_scalarProduct_principalCharacter_self, hprincipalη,
      hφβS, hφprincipal, hφη]
    ring
  rcases hparity with ⟨m, hm⟩
  have hzEqC : ((zS + zL - 1 : ℤ) : ℂ) = ((2 * m : ℤ) : ℂ) := by
    calc
      ((zS + zL - 1 : ℤ) : ℂ) = bSphi + bLeta - 1 := by
        dsimp [bSphi, bLeta] at hzS hzL ⊢
        rw [hzS, hzL]
        norm_num
      _ = Section1.scalarProduct G ΓL Γ := hcross.symm
      _ = ((2 * m : ℤ) : ℂ) := hm
  have hzEq : zS + zL - 1 = 2 * m := by
    exact_mod_cast hzEqC
  have hoddInts : Odd zS ∨ Odd zL := by
    by_contra hnot
    push Not at hnot
    have hzevenS : Even zS := Int.not_odd_iff_even.mp hnot.1
    have hzevenL : Even zL := Int.not_odd_iff_even.mp hnot.2
    have hzodd : Odd (zS + zL - 1) :=
      (hzevenS.add hzevenL).sub_odd odd_one
    rw [hzEq] at hzodd
    exact (Int.not_odd_iff_even.mpr (even_two_mul m)) hzodd
  rcases hoddInts with hoddS | hoddL
  · left
    refine ⟨?_, ?_⟩
    · rcases hoddS with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      change 2 * (k : ℂ) + 1 = Section1.scalarProduct G βS φ
      calc
        2 * (k : ℂ) + 1 = ((2 * k + 1 : ℤ) : ℂ) := by norm_num
        _ = (zS : ℂ) := by rw [hk]
        _ = Section1.scalarProduct G βS φ := hzS.symm
    · let I := ↑Lfam
      letI : Finite I := Fintype.finite (Finset.fintypeCoeSort Lfam)
      letI : Fintype I := Fintype.ofFinite I
      let χ : I → Section1.ClassFunction G := fun ψ => τL1 ψ.1
      have hχorth : ∀ ψ θ : I,
          Section1.scalarProduct G (χ ψ) (χ θ) = if ψ = θ then 1 else 0 := by
        intro ψ θ
        have hIso := hcohL.1 ψ.1 θ.1
          (Section5.integerSpan_of_mem Lfam ψ.2)
          (Section5.integerSpan_of_mem Lfam θ.2)
        dsimp [χ]
        rw [hIso]
        by_cases hψθ : ψ = θ
        · subst θ
          rw [if_pos rfl]
          exact theorem_13_19_Lfam_scalarProduct_self
            (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
            (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
            (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
            (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
            (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
            (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
            hsourceOrig h19Orig ψ.2
        · rw [if_neg hψθ]
          have hψirr := theorem_13_19_Lfam_irreducible_of_source
            (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
            (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
            (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
            (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
            (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
            (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
            hsourceOrig h19Orig ψ.2
          have hθirr := theorem_13_19_Lfam_irreducible_of_source
            (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
            (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
            (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
            (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
            (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
            (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
            hsourceOrig h19Orig θ.2
          exact Section1.scalarProduct_isBookIrreducible_ne ψ.1 θ.1
            (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hψirr)
            (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr)
            (by intro hval; exact hψθ (Subtype.ext hval))
      let degreeData (ψ : I) :=
        Section7.theorem_7_8_degree_zero_combo_mem_integerSpanOn h78 ψ.2
      let n : I → ℕ := fun ψ => Classical.choose (degreeData ψ)
      have hnne (ψ : I) : n ψ ≠ 0 :=
        (Classical.choose_spec (degreeData ψ)).1
      have hndeg (ψ : I) :
          Section1.degree ψ.1 = (H.relIndex L : ℂ) * (n ψ : ℂ) :=
        (Classical.choose_spec (degreeData ψ)).2.1
      have hnspan (ψ : I) :
          Section5.integerSpanOn Lfam Section5.puncturedSet
            (ψ.1 - (n ψ : ℂ) • φL) :=
        (Classical.choose_spec (degreeData ψ)).2.2
      have sum_scalar_zero : ∀ (s : Finset ℕ)
          (f : ℕ → Section1.ClassFunction G) (θ : Section1.ClassFunction G),
          (∀ i ∈ s, Section1.scalarProduct G (f i) θ = 0) →
            Section1.scalarProduct G (s.sum f) θ = 0 := by
        intro s f θ hs
        induction s using Finset.induction_on with
        | empty => simp [Section1.scalarProduct]
        | @insert i s hi ih =>
            rw [Finset.sum_insert hi, Section1.scalarProduct_add_left,
              hs i (Finset.mem_insert_self i s), ih]
            · simp
            · intro j hj
              exact hs j (Finset.mem_insert_of_mem hj)
      rcases hdecomp.1 with ⟨coeff, hXdef⟩
      have hXχ : ∀ ψ : I, Section1.scalarProduct G X (χ ψ) = 0 := by
        intro ψ
        rw [hXdef]
        apply sum_scalar_zero
        intro i hi
        apply sum_scalar_zero
        intro j hj
        have hiq : i < q := Finset.mem_range.mp hi
        have hjp : j < p := Finset.mem_range.mp hj
        have hψη := theorem_13_19_orthogonality_source
          Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
          τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
          p q u v c d e hsourceOrig hnotationOrig h19Orig
          ψ.1 ψ.2 i j hiq hjp
        have hηψ : Section1.scalarProduct G (η i j) (χ ψ) = 0 := by
          have hswap := Section1.scalarProduct_star_swap (G := G) (χ ψ) (η i j)
          have hstarzero : star (Section1.scalarProduct G (η i j) (χ ψ)) = 0 := by
            simpa [χ, hψη] using hswap
          simpa using congrArg star hstarzero
        rw [Section1.scalarProduct_smul_left, hηψ]
        simp
      have hβSsupp :
          Section1.supportedOn βS
            (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
              section16ConjugatesOfSetBySet (W : Set G) Set.univ) := by
        rw [hβSdef]
        exact theorem_13_19_tauS_betaPre_supportedOn_PWG
          (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
          (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
          (Sfam := Sfam) (Tfam := Tfam) (τS := τS) (τT := τT)
          (ω := ω) (η := η) (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
          (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q) (u := u)
          (v := v) (c := c) (d := d) hsourceOrig hnotationOrig zero_lt_one hp1
      have hdisj := theorem_13_19_support_disjoint_source
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
        τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
        p q u v c d e hsourceOrig hnotationOrig h19Orig
      have hcomboCoeff : ∀ ψ : I,
          Section1.scalarProduct G βS (χ ψ) = bSphi * (n ψ : ℂ) := by
        intro ψ
        let combo : Section1.ClassFunction L := ψ.1 - (n ψ : ℂ) • φL
        have hcomboOn : Section2.CFOn L (Section12.typeIASet L H) combo := by
          dsimp [combo]
          exact Section7.theorem_7_8_combo_CFOn h76 h78 ψ.2 (hndeg ψ)
        rcases hAgree with ⟨hAL, hτDade⟩
        have hτcombo : τL combo = Section2.dadeTransform R hAL combo :=
          hτDade combo hcomboOn
        have hcomboSupp :
            Section1.supportedOn (τL combo)
              (Section2.dadeSupport (Section12.typeIASet L H) R) := by
          rw [hτcombo]
          exact Section12.supportedOn_dadeTransform_dadeSupport
            hAL combo
        have hleft : Section1.scalarProduct G (τL combo) βS = 0 :=
          Section12.scalarProduct_eq_zero_of_supportedOn_disjoint
            hcomboSupp hβSsupp hdisj
        have hright : Section1.scalarProduct G βS (τL combo) = 0 := by
          have hswap := Section1.scalarProduct_star_swap (G := G) (τL combo) βS
          have hstarzero : star (Section1.scalarProduct G βS (τL combo)) = 0 := by
            simpa [hleft] using hswap
          simpa using congrArg star hstarzero
        have hagreeCombo : τL1 combo = τL combo :=
          hcohL.2.2 combo (hnspan ψ)
        rw [← hagreeCombo] at hright
        dsimp [combo] at hright
        rw [map_sub, map_smul, Section5.scalarProduct_sub_right,
          Section1.scalarProduct_smul_right, ← hφdef] at hright
        dsimp [χ, bSphi]
        simpa [mul_comm] using sub_eq_zero.mp hright
      have hYcoeff : ∀ ψ : I,
          Section1.scalarProduct G Y (χ ψ) = bSphi * (n ψ : ℂ) := by
        intro ψ
        have hη01ψ : Section1.scalarProduct G η01 (χ ψ) = 0 := by
          have hψη := theorem_13_19_orthogonality_source
            Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
            τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
            p q u v c d e hsourceOrig hnotationOrig h19Orig
            ψ.1 ψ.2 0 1 hqpos hp1
          have hswap := Section1.scalarProduct_star_swap (G := G) (χ ψ) η01
          have hstarzero : star (Section1.scalarProduct G η01 (χ ψ)) = 0 := by
            simpa [χ, hη01, hψη] using hswap
          simpa using congrArg star hstarzero
        have hΓcoeff :
            Section1.scalarProduct G Γ (χ ψ) =
              Section1.scalarProduct G βS (χ ψ) := by
          rw [hΓdef, Section1.scalarProduct_add_left,
            Section5.scalarProduct_sub_left, hprincipalImage ψ.1 ψ.2,
            hη01ψ]
          simp
        have hXY := congrArg (fun θ : Section1.ClassFunction G =>
          Section1.scalarProduct G θ (χ ψ)) hΓXY
        change Section1.scalarProduct G Γ (χ ψ) =
          Section1.scalarProduct G (X + Y) (χ ψ) at hXY
        rw [Section1.scalarProduct_add_left, hXχ ψ, zero_add] at hXY
        rw [← hXY, hΓcoeff, hcomboCoeff ψ]
      have heNe : e ≠ 0 := by
        rw [he]
        haveI : (H.subgroupOf L).FiniteIndex := inferInstance
        simpa [Subgroup.relIndex] using
          (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
      have heRNe : (e : ℝ) ≠ 0 := by exact_mod_cast heNe
      have hψnorm : ∀ ψ : I, Section5.cfNormSq ψ.1 = 1 := by
        intro ψ
        have hself := theorem_13_19_Lfam_scalarProduct_self
          (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
          (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
          (L := L) (H := H) (Sfam := Sfam) (Tfam := Tfam) (Lfam := Lfam)
          (R := R) (τS := τS) (τT := τT) (τL := τL) (τL1 := τL1)
          (φL := φL) (βL := βL) (βS := βS) (φ := φ) (μ := μ)
          (p := p) (q := q) (u := u) (v := v) (c := c) (d := d) (e := e)
          hsourceOrig h19Orig ψ.2
        unfold Section5.cfNormSq
        rw [hself]
        norm_num
      have htermIdentity : ∀ ψ : I,
          Complex.normSq (ψ.1 1) /
              ((e : ℝ) ^ 2 * Section5.cfNormSq ψ.1) =
            (n ψ : ℝ) ^ 2 := by
        intro ψ
        have hdegree := hndeg ψ
        rw [← he] at hdegree
        have hvalue : ψ.1 1 = (e : ℂ) * (n ψ : ℂ) := by
          simpa [Section1.degree_apply] using hdegree
        rw [hvalue, hψnorm ψ, Complex.normSq_mul,
          Complex.normSq_natCast, Complex.normSq_natCast]
        field_simp [heRNe]
      have hDegreeSum := Section7.theorem_7_8_b_degree_sum_identity h76 h78
      rw [← he] at hDegreeSum
      have hDegreeUniv :
          (Finset.univ : Finset I) =
            @Finset.univ (↑Lfam) (Finset.Subtype.fintype Lfam) := by
        ext ψ
        simp
      have hDegreeSumI : (∑ ψ : I,
          Complex.normSq (ψ.1 1) /
            ((e : ℝ) ^ 2 * Section5.cfNormSq ψ.1)) =
          ((Nat.card H : ℝ) - 1) / (e : ℝ) := by
        rw [hDegreeUniv]
        exact hDegreeSum
      have hSquareSum :
          (∑ ψ : I, (n ψ : ℝ) ^ 2) =
            ((Nat.card H : ℝ) - 1) / (e : ℝ) := by
        calc
          (∑ ψ : I, (n ψ : ℝ) ^ 2) =
              ∑ ψ : I, Complex.normSq (ψ.1 1) /
                ((e : ℝ) ^ 2 * Section5.cfNormSq ψ.1) := by
            refine Finset.sum_congr rfl ?_
            intro ψ _hψ
            exact (htermIdentity ψ).symm
          _ = ((Nat.card H : ℝ) - 1) / (e : ℝ) := hDegreeSumI
      have hzSne : zS ≠ 0 := by
        intro hz
        subst zS
        exact Int.not_odd_zero hoddS
      have hzSsquare : (1 : ℝ) ≤ (zS : ℝ) * (zS : ℝ) := by
        have hzpos : (0 : ℤ) < zS * zS := (mul_self_pos).2 hzSne
        have hzone : (1 : ℤ) ≤ zS * zS := by omega
        exact_mod_cast hzone
      have htermLower : ∀ ψ : I,
          (n ψ : ℝ) ^ 2 ≤
            Complex.normSq (Section1.scalarProduct G Y (χ ψ)) := by
        intro ψ
        rw [hYcoeff ψ]
        have hbScast : bSphi = (zS : ℂ) := hzS
        rw [hbScast, Complex.normSq_mul, Complex.normSq_intCast,
          Complex.normSq_natCast]
        have hnnonneg : (0 : ℝ) ≤ (n ψ : ℝ) * (n ψ : ℝ) :=
          mul_self_nonneg _
        nlinarith
      have hSquareLeCoeff :
          (∑ ψ : I, (n ψ : ℝ) ^ 2) ≤
            ∑ ψ : I,
              Complex.normSq (Section1.scalarProduct G Y (χ ψ)) :=
        Finset.sum_le_sum (fun ψ _hψ => htermLower ψ)
      have hBessel :=
        theorem_13_18_finite_orthonormal_coeff_normSq_sum_le_cfNormSq χ hχorth Y
      have hFinal :
          ((Nat.card H : ℝ) - 1) / (e : ℝ) ≤
            ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
        rw [← hSquareSum]
        exact le_trans hSquareLeCoeff (le_trans hBessel hYnorm)
      have hHcast : (((Nat.card H - 1 : ℕ) : ℝ)) =
          (Nat.card H : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne'))]
        norm_num
      rw [hHcast]
      exact hFinal
  · right
    refine ⟨?_, ?_⟩
    · intro j hj0 hjp
      have hjEq := theorem_13_19_betaL_eta_eq_eta01_source
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
        τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
        p q u v c d e hsourceOrig hnotationOrig h19Orig j hj0 hjp
      rcases hoddL with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      change 2 * (k : ℂ) + 1 = Section1.scalarProduct G βL (η 0 j)
      calc
        2 * (k : ℂ) + 1 = ((2 * k + 1 : ℤ) : ℂ) := by norm_num
        _ = (zL : ℂ) := by rw [hk]
        _ = Section1.scalarProduct G βL η01 := hzL.symm
        _ = Section1.scalarProduct G βL (η 0 j) := by rw [hjEq, hη01]
    · let J := {j : ℕ // j ∈ Finset.Ioo 0 p}
      let toFin : J → Fin p := fun j =>
        ⟨j.1, (Finset.mem_Ioo.mp j.2).2⟩
      have htoFin : Function.Injective toFin := by
        intro j k hjk
        apply Subtype.ext
        exact congrArg Fin.val hjk
      letI : Finite J := Finite.of_injective toFin htoFin
      let χ : J → Section1.ClassFunction G := fun j => η 0 j.1
      have hχorth : ∀ j k : J,
          Section1.scalarProduct G (χ j) (χ k) = if j = k then 1 else 0 := by
        intro j k
        have hj0 : 0 < j.1 := (Finset.mem_Ioo.mp j.2).1
        have hjp : j.1 < p := (Finset.mem_Ioo.mp j.2).2
        have hk0 : 0 < k.1 := (Finset.mem_Ioo.mp k.2).1
        have hkp : k.1 < p := (Finset.mem_Ioo.mp k.2).2
        have horth := theorem_13_18_eta_orthonormal_of_notation
          Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
          hnotationOrig 0 j.1 0 k.1 hqpos hjp hqpos hkp
        dsimp [χ]
        by_cases hjk : j = k
        · subst k
          simpa using horth
        · have hval : j.1 ≠ k.1 := by
            intro h
            exact hjk (Subtype.ext h)
          simpa [hjk, hval] using horth
      have hweightedEta : ∀ j : J,
          Section1.scalarProduct G
            (Section7.theorem_7_8_weightedSum Lfam τL1 (H.relIndex L))
            (χ j) = 0 := by
        intro j
        have hjp : j.1 < p := (Finset.mem_Ioo.mp j.2).2
        have hsum :
            Section7.theorem_7_8_weightedSum Lfam τL1 (H.relIndex L) =
              fun g => ∑ ψ : Lfam,
                (((ψ : Section1.ClassFunction L) 1 /
                  (((H.relIndex L : ℕ) : ℂ) *
                    (Section5.cfNormSq (ψ : Section1.ClassFunction L) : ℂ))) •
                  τL1 (ψ : Section1.ClassFunction L)) g := by
          ext g
          simp only [Section7.theorem_7_8_weightedSum, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul]
          exact (Finset.sum_attach Lfam
            (fun ψ : Section1.ClassFunction L =>
              ψ 1 / (((H.relIndex L : ℕ) : ℂ) *
                (Section5.cfNormSq ψ : ℂ)) * τL1 ψ g)).symm
        rw [hsum, Section1.scalarProduct_fintype_sum_left]
        refine Finset.sum_eq_zero ?_
        intro ψ _hψ
        have hψη := theorem_13_19_orthogonality_source
          Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
          τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
          p q u v c d e hsourceOrig hnotationOrig h19Orig
          (ψ : Section1.ClassFunction L) ψ.2 0 j.1 hqpos hjp
        rw [Section1.scalarProduct_smul_left]
        dsimp [χ]
        rw [hψη]
        simp
      have hprincipalEta : ∀ j : J,
          Section1.scalarProduct G (Section1.principalCharacter G) (χ j) = 0 := by
        intro j
        have hj0 : 0 < j.1 := (Finset.mem_Ioo.mp j.2).1
        have hjp : j.1 < p := (Finset.mem_Ioo.mp j.2).2
        have hright := theorem_13_18_eta_zero_row_principal_orthogonal_of_notation
          Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
          hnotationOrig j.1 hj0 hjp
        have hswap := Section1.scalarProduct_star_swap
          (G := G) (η 0 j.1) (Section1.principalCharacter G)
        dsimp [χ]
        have hstarzero :
            star (Section1.scalarProduct G (Section1.principalCharacter G)
              (η 0 j.1)) = 0 := by
          simpa [hright] using hswap
        simpa using congrArg star hstarzero
      have hφEta : ∀ j : J,
          Section1.scalarProduct G φ (χ j) = 0 := by
        intro j
        have hjp : j.1 < p := (Finset.mem_Ioo.mp j.2).2
        dsimp [χ]
        rw [hφdef]
        exact theorem_13_19_orthogonality_source
          Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
          τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
          p q u v c d e hsourceOrig hnotationOrig h19Orig
          φL hφmem 0 j.1 hqpos hjp
      have hrCoeff : ∀ j : J,
          Section1.scalarProduct G r (χ j) = bLeta := by
        intro j
        have hj0 : 0 < j.1 := (Finset.mem_Ioo.mp j.2).1
        have hjp : j.1 < p := (Finset.mem_Ioo.mp j.2).2
        have hEq := congrArg (fun θ : Section1.ClassFunction G =>
          Section1.scalarProduct G θ (χ j)) hremEq
        change Section1.scalarProduct G
          (Section7.theorem_7_8_beta L H τL φL) (χ j) =
          Section1.scalarProduct G
            (Section1.principalCharacter G - τL1 φL +
              (a : ℂ) • Section7.theorem_7_8_weightedSum Lfam τL1
                (H.relIndex L) + r) (χ j) at hEq
        rw [hβLdef, ← hφdef] at hEq
        rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left] at hEq
        rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left,
          hprincipalEta j, hφEta j, hweightedEta j] at hEq
        have hβeq := theorem_13_19_betaL_eta_eq_eta01_source
          Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
          τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
          p q u v c d e hsourceOrig hnotationOrig h19Orig j.1 hj0 hjp
        dsimp [χ] at hEq
        rw [hβeq, ← hη01] at hEq
        change Section1.scalarProduct G r (η 0 j.1) =
          Section1.scalarProduct G βL η01
        simpa using hEq.symm
      have hzLne : zL ≠ 0 := by
        intro hz
        subst zL
        exact Int.not_odd_zero hoddL
      have htermLower : ∀ j : J,
          (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G r (χ j)) := by
        intro j
        rw [hrCoeff j]
        have hbLcast : bLeta = (zL : ℂ) := hzL
        rw [hbLcast, Complex.normSq_intCast]
        have hzpos : (0 : ℤ) < zL * zL := (mul_self_pos).2 hzLne
        have hzone : (1 : ℤ) ≤ zL * zL := by omega
        exact_mod_cast hzone
      have hcardLower :
          (Fintype.card J : ℝ) ≤
            ∑ j : J, Complex.normSq (Section1.scalarProduct G r (χ j)) := by
        calc
          (Fintype.card J : ℝ) = ∑ _j : J, (1 : ℝ) := by simp
          _ ≤ ∑ j : J, Complex.normSq (Section1.scalarProduct G r (χ j)) :=
            Finset.sum_le_sum (fun j _hj => htermLower j)
      have hBessel :=
        theorem_13_18_finite_orthonormal_coeff_normSq_sum_le_cfNormSq χ hχorth r
      have hcardNorm : (Fintype.card J : ℝ) ≤ Section5.cfNormSq r :=
        le_trans hcardLower hBessel
      have hcardJ : Fintype.card J = p - 1 := by
        let eJ : J ≃ ↑(Finset.Ioo 0 p) :=
          { toFun := fun j => ⟨j.1, j.2⟩
            invFun := fun j => ⟨j.1, j.2⟩
            left_inv := fun j => rfl
            right_inv := fun j => rfl }
        rw [Fintype.card_congr eJ, Fintype.card_coe]
        rw [Nat.card_Ioo]
        omega
      have hbound : ((p - 1 : ℕ) : ℝ) ≤ (e : ℝ) - 1 := by
        rw [← hcardJ]
        exact le_trans hcardNorm (by simpa [he] using hrnorm)
      have hpcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)]
        norm_num
      have hpeReal : (p : ℝ) ≤ (e : ℝ) := by
        rw [hpcast] at hbound
        linarith
      exact_mod_cast hpeReal

end theorem_13_19_source

public theorem theorem_13_19
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (Lfam : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (τL τL1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φL : Section1.ClassFunction L)
    (βL βS φ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d e : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_19_hypothesis L H Smax P W1 Lfam R τS τL τL1 φL φ
          (μ 0 1) βL βS e →
      Disjoint (Section2.dadeSupport (Section12.typeIASet L H) R)
        (section16ConjugatesOfSetBySet (P : Set G) Set.univ ∪
          section16ConjugatesOfSetBySet (W : Set G) Set.univ) ∧
        (∀ ψ : Section1.ClassFunction L, ψ ∈ Lfam →
          ∀ i j : ℕ, i < q → j < p →
            Section1.scalarProduct G (τL1 ψ) (η i j) = 0) ∧
          theorem_13_19_independenceData βL η p ∧
          theorem_13_19_alternativeData H βL βS φ η p q u e := by
  intro hsource hnotation h19
  exact ⟨
    theorem_13_19_support_disjoint_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19,
    theorem_13_19_orthogonality_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19,
    theorem_13_19_independence_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19,
    theorem_13_19_alternative_source
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam R
      τS τT τL τL1 φL βL βS φ ω η μ ν μsum νsum δ δ' σ
      p q u v c d e hsource hnotation h19⟩
end CFSG.Section13
