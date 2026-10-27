module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_14
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
# Peterfalvi, Section 12: Theorem (12.15)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.15) -/


private theorem theorem_12_15_typeI_orthogonality
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H E N NF : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (chi : Section1.ClassFunction L)
    (psi : Section1.ClassFunction G)
    (psirho : Section1.ClassFunction L)
    (SN : Finset (Section1.ClassFunction N))
    (RN : G → Subgroup G)
    (tauN : Section1.ClassFunction N →ₗ[ℂ] Section1.ClassFunction G)
    (DN tildeAN tildeA0N tildeA1N : Set G)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psirho)
    (h12N : hypothesis_12_1_data N NF SN RN tauN)
    (hnotN : Section8.notation_8_14_source_data N
      (typeIASet N NF) (typeIASet N NF) (Section8.a1Set NF)
      DN tildeAN tildeA0N tildeA1N RN)
    (hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) N L) :
    ∃ SXN : SN → Finset (Section1.ClassFunction N),
    ∃ R1N : Section1.ClassFunction N → Finset (Section1.ClassFunction G),
    ∃ RfunN : SN → Finset (Section1.ClassFunction G),
      constituentFamilyData N NF SN SXN RN tauN ∧
      (∀ xi : SN,
        rFamilyData (xi : Section1.ClassFunction N) (SXN xi) tauN R1N (RfunN xi)) ∧
      hypothesis52WithRData SN tauN RfunN ∧
      orthogonalToAllR SN RfunN psi := by
  classical
  rcases h13 with
    ⟨h12L, _hcomp, _he, hchiS, _hdeg, _h78pack, hnotpack,
      hExt, hpsi, _hpsiclass, _hrho⟩
  rcases hnotpack with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hMsLSource, hnotL⟩
  rcases theorem_12_2_a N NF SN RN tauN h12N with ⟨SXN, hdataN⟩
  rcases theorem_12_2_b N NF SN SXN RN tauN h12N hdataN with
    ⟨R1N, RfunN, hRdataN, h52N⟩
  rcases theorem_12_2_a L H S R tau h12L with ⟨SXL, hdataL⟩
  rcases theorem_12_2_b L H S SXL R tau h12L hdataL with
    ⟨R1L, RfunL, hRdataL, h52L⟩
  have hMsN : Section8.msChoiceSource N NF NF :=
    Section8.msChoiceSource_of_typeIDefinitionData h12N.2.2.1
  have hsrcPair (chiN : Section1.ClassFunction N) :
      theorem_12_3_source_pair_data N NF L H SN S tauN tau RN R
        chiN chi DN tildeAN tildeA0N tildeA1N
        DL tildeAL tildeA0L tildeA1L := by
    refine ⟨inferInstance, hMsN, hMsLSource, hnotN, hnotL, ?_, ?_⟩
    · intro hchiN
      exact supportedOn_tau_sub_conjugate_tildeA1 h12N hnotN hchiN
    · intro _hchi
      exact supportedOn_tau_sub_conjugate_tildeA1 h12L hnotL hchiS
  have horthFamilies (chiN : SN) :
      Section5.orthogonalFinsets (RfunN chiN) (RfunL ⟨chi, hchiS⟩) :=
    theorem_12_3 N NF L H SN S tauN tau RN R SXN SXL R1N R1L
      RfunN RfunL (chiN : Section1.ClassFunction N) chi
      DN tildeAN tildeA0N tildeA1N DL tildeAL tildeA0L tildeA1L
      (hsrcPair chiN) h12N h12L hdataN hdataL hnotconj
      hRdataN h52N hRdataL h52L chiN.2 hchiS
  have hpsisubset :
      Section5.isSubsetSumOf (RfunL ⟨chi, hchiS⟩) psi := by
    rw [hpsi]
    exact coherentExtension_subsetSum_of_hypothesis52WithRData h52L hExt hchiS
  have horthN : orthogonalToAllR SN RfunN psi := by
    intro chiN alpha halpha
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
        horthFamilies chiN halpha (hFsub beta.2)
    have hswap := Section1.scalarProduct_star_swap (G := G) alpha psi
    have hstarzero : star (Section1.scalarProduct G psi alpha) = 0 := by
      simpa [hright] using hswap
    simpa using congrArg star hstarzero
  exact ⟨SXN, R1N, RfunN, hdataN, hRdataN, h52N, horthN⟩


private theorem theorem_12_15_psi_constant_on_typeI_kernel_coset
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H E N NF : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (tau tau1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (chi : Section1.ClassFunction L)
    (psi : Section1.ClassFunction G)
    (psirho : Section1.ClassFunction L)
    (h13 : notation_12_13_data L H E e S R tau tau1 chi psi psirho)
    (hNmax : N ∈ section9MaximalSubgroups G)
    (hNMF : section16MFSubgroup N NF)
    (hTypeIN : Section8.typeIDefinitionData N NF)
    (hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) N L)
    (z : G) (hzN : z ∈ N) (hznotNF : z ∉ NF) :
    constantOnRightCoset NF psi z := by
  classical
  rcases exists_puncturedInducedFamily (NF.subgroupOf N) with ⟨SN, hSN⟩
  have hMsN : Section8.msChoiceSource N NF NF :=
    Section8.msChoiceSource_of_typeIDefinitionData hTypeIN
  have hnot10N : Section8.notation_8_10_source_data N NF NF
      (typeIASet N NF) (typeIASet N NF) (Section8.a1Set NF) :=
    notation_8_10_source_data_of_typeI_msChoice
      N NF hNmax hNMF hTypeIN hMsN
  have hA1N : Section8.a1Set NF ⊆ typeIASet N NF := by
    simpa [Section8.a1Set] using
      nonidentity_kernel_subset_typeIASet N NF (section16MFSubgroup_le hNMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      N NF NF (typeIASet N NF) (typeIASet N NF) (Section8.a1Set NF)
      (typeIASet N NF) inferInstance hnot10N (Or.inl rfl) hA1N with
    ⟨RN, tildeAN, tildeA0N, tildeA1N, hnotN⟩
  have h815N : Section8.theorem_8_15_source_data N NF NF
      (typeIASet N NF) (typeIASet N NF) (Section8.a1Set NF)
      (typeIASet N NF) (Section8.section8DSet N (typeIASet N NF))
      tildeAN tildeA0N tildeA1N RN :=
    ⟨hnot10N, hnotN, Or.inr (Or.inl rfl)⟩
  have h22N : Section2.Hypothesis2 (typeIASet N NF) N RN :=
    Section8.theorem_8_15_hypothesis2 (inferInstance : IsMinCE G) h815N
  let tauN : Section1.ClassFunction N →ₗ[ℂ] Section1.ClassFunction G :=
    dadeTransformLinear RN h22N.subset_L
  have hDadeN : dadeIsometryRelativeToTypeIASet N NF RN tauN := by
    simpa [tauN] using
      dadeIsometryRelativeToTypeIASet_of_hypothesis2 N NF RN h22N
  have h12N : hypothesis_12_1_data N NF SN RN tauN :=
    ⟨hNmax, hNMF, hTypeIN, hSN, hDadeN⟩
  rcases theorem_12_15_typeI_orthogonality
      L H E N NF e S R tau tau1 chi psi psirho SN RN tauN
      (Section8.section8DSet N (typeIASet N NF))
      tildeAN tildeA0N tildeA1N h13 h12N hnotN hnotconj with
    ⟨SXN, R1N, RfunN, hdataN, hRdataN, h52N, horthN⟩
  have hinputN : theorem_12_4_dade_induction_lemma_source_inputs
      N NF SN RN tauN := by
    intro _hhyp
    exact ⟨inferInstance, hMsN, _, _, _, _, hnotN⟩
  exact theorem_12_4 N NF SN SXN RN R1N RfunN tauN psi z hinputN h12N
    hdataN hRdataN h52N h13.2.2.2.2.2.2.2.2.2.1 horthN hzN hznotNF


private theorem theorem_12_15_supporting_typeI_not_conjugate
    {G : Type u} [Group G] [Finite G]
    (L H N NF : Subgroup G)
    (hfrobL : Section7.frobeniusWithKernel L H)
    (hHMF : section16MFSubgroup L H)
    (hNMF : section16MFSubgroup N NF)
    (z : G)
    (hz : z ∈ Section8.section8CentralizerUnion N NF \ Section8.a1Set NF) :
    ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) N L := by
  classical
  rintro ⟨a, _ha, hNL⟩
  have hNFconjMF : section16MFSubgroup L (NF.conjBy a) := by
    have hconj := Section8.theorem_8_18_mfSubgroup_conjBy a hNMF
    simpa [hNL] using hconj
  have hNFconj : NF.conjBy a = H :=
    section16MFSubgroup_unique hNFconjMF hHMF
  rcases hz.1 with ⟨y, ⟨hyNF, hyne⟩, hycent, _hzne⟩
  let za : G := a * z * a⁻¹
  let ya : G := a * y * a⁻¹
  have hzaL : za ∈ L := by
    rw [hNL, Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨z, hycent.1, by simp [za, MulAut.conj_apply]⟩
  have hyaH : ya ∈ H := by
    rw [← hNFconj, Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨y, hyNF, by simp [ya, MulAut.conj_apply]⟩
  have hza_ne : za ≠ 1 := by
    intro hza
    apply _hzne
    have := congrArg (fun t : G => a⁻¹ * t * a) hza
    simp only [za] at this
    group at this
    exact this
  have hya_ne : ya ≠ 1 := by
    intro hya
    apply hyne
    have := congrArg (fun t : G => a⁻¹ * t * a) hya
    simp only [ya] at this
    group at this
    exact this
  have hcomm : za * ya = ya * za := by
    have hzy : z * y = y * z :=
      Subgroup.mem_centralizer_singleton_iff.mp hycent.2
    simp only [za, ya]
    calc
      (a * z * a⁻¹) * (a * y * a⁻¹) = a * (z * y) * a⁻¹ := by group
      _ = a * (y * z) * a⁻¹ := by rw [hzy]
      _ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
  have hzaA : za ∈ typeIASet L H :=
    ⟨hzaL, hza_ne, ya, hyaH, hya_ne,
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hzaH : za ∈ H := by
    have hEq := typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrobL
    exact (hEq ▸ hzaA).1
  have hzaNFconj : za ∈ NF.conjBy a := by simpa [hNFconj] using hzaH
  rw [Subgroup.conjBy, Subgroup.mem_map] at hzaNFconj
  rcases hzaNFconj with ⟨w, hwNF, hw⟩
  have hwz : w = z := by
    apply (MulAut.conj a).injective
    simpa [za, MulAut.conj_apply] using hw
  apply hz.2
  simpa [Section8.a1Set, hwz] using
    (show z ∈ section16NonidentityElements (NF : Set G) from ⟨by simpa [hwz] using hwNF, _hzne⟩)

private theorem theorem_12_15_subgroupRestriction_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    (J : Subgroup G) {phi : Section1.ClassFunction G}
    (hphi : Theory.Character.IsVirtualCharacter phi) :
    Theory.Character.IsVirtualCharacter (Section1.subgroupRestriction J phi) := by
  classical
  rcases hphi with ⟨r, m, n, rho, rfl⟩
  refine ⟨r, m, n, fun i => (rho i).comp J.subtype, ?_⟩
  ext j
  simp [Theory.Character.virtualCharacterOfRepresentations,
    Section1.subgroupRestriction, Representation.character]

private theorem theorem_12_15_virtualCharacter_value_isIntegral
    {G : Type u} [Group G] [Finite G]
    {phi : Section1.ClassFunction G}
    (hphi : Theory.Character.IsVirtualCharacter phi) (g : G) :
    IsIntegral ℤ (phi g) := by
  classical
  rcases hphi with ⟨r, m, n, rho, rfl⟩
  unfold Theory.Character.virtualCharacterOfRepresentations
  apply IsIntegral.sum
  intro i _hi
  have hm : IsIntegral ℤ (m i : ℂ) := isIntegral_algebraMap
  exact hm.mul
    (Theory.Character.representation_character_isIntegral (ρ := rho i) g)

private theorem theorem_12_15_value_isRational_of_constant_on_subgroup_complement
    {G : Type u} [Group G] [Finite G]
    (K K' : Subgroup G)
    (psi : Section1.ClassFunction G)
    (hpsi : Theory.Character.IsVirtualCharacter psi)
    (hK'K : K' ≤ K)
    (hconst :
      ∀ a b : G, a ∈ K → a ∉ K' → b ∈ K → b ∉ K' → psi a = psi b)
    (g : G) (hgK : g ∈ K) (hgK' : g ∉ K') :
    ∃ q : ℚ, psi g = (q : ℂ) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K' := Fintype.ofFinite K'
  have hresK := theorem_12_15_subgroupRestriction_isVirtualCharacter K hpsi
  have hresK' := theorem_12_15_subgroupRestriction_isVirtualCharacter K' hpsi
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hresK
      (Section3.isVirtualCharacter_principalCharacter (G := K)) with ⟨m, hm⟩
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hresK'
      (Section3.isVirtualCharacter_principalCharacter (G := K')) with ⟨n, hn⟩
  have hmraw :
      (Nat.card K : ℂ)⁻¹ * ∑ z : K, psi (z : G) = (m : ℂ) := by
    simpa [Section1.scalarProduct, Section1.subgroupRestriction,
      Section1.principalCharacter] using hm
  have hnraw :
      (Nat.card K' : ℂ)⁻¹ * ∑ z : K', psi (z : G) = (n : ℂ) := by
    simpa [Section1.scalarProduct, Section1.subgroupRestriction,
      Section1.principalCharacter] using hn
  have hcardK : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := K)).ne'
  have hcardK' : (Nat.card K' : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := K')).ne'
  have hsumK :
      (∑ z : K, psi (z : G)) = (Nat.card K : ℂ) * (m : ℂ) := by
    calc
      (∑ z : K, psi (z : G)) =
          (Nat.card K : ℂ) *
            ((Nat.card K : ℂ)⁻¹ * ∑ z : K, psi (z : G)) := by
              field_simp [hcardK]
      _ = (Nat.card K : ℂ) * (m : ℂ) := by rw [hmraw]
  have hsumK' :
      (∑ z : K', psi (z : G)) = (Nat.card K' : ℂ) * (n : ℂ) := by
    calc
      (∑ z : K', psi (z : G)) =
          (Nat.card K' : ℂ) *
            ((Nat.card K' : ℂ)⁻¹ * ∑ z : K', psi (z : G)) := by
              field_simp [hcardK']
      _ = (Nat.card K' : ℂ) * (n : ℂ) := by rw [hnraw]
  let e : {z : K // (z : G) ∈ K'} ≃ K' :=
    (Subgroup.subgroupOfEquivOfLe hK'K).toEquiv
  have hsumPos :
      (∑ z : {z : K // (z : G) ∈ K'}, psi (z : G)) =
        ∑ z : K', psi (z : G) := by
    exact Fintype.sum_equiv e _ _ (fun z => by
      change psi (z.1.1 : G) = psi (((e z : K') : G))
      rfl)
  have hsumNeg :
      (∑ z : {z : K // (z : G) ∉ K'}, psi (z : G)) =
        (Fintype.card {z : K // (z : G) ∉ K'} : ℂ) * psi g := by
    calc
      (∑ z : {z : K // (z : G) ∉ K'}, psi (z : G)) =
          ∑ _z : {z : K // (z : G) ∉ K'}, psi g := by
            apply Finset.sum_congr rfl
            intro z _hz
            exact hconst (z : G) g z.1.2 z.2 hgK hgK'
      _ = (Fintype.card {z : K // (z : G) ∉ K'} : ℂ) * psi g := by
        simp [Finset.card_univ]
  have hsplit :
      (∑ z : K', psi (z : G)) +
          (Fintype.card {z : K // (z : G) ∉ K'} : ℂ) * psi g =
        ∑ z : K, psi (z : G) := by
    rw [← hsumPos, ← hsumNeg]
    exact Fintype.sum_subtype_add_sum_subtype
      (fun z : K => (z : G) ∈ K') (fun z : K => psi (z : G))
  have hcompNonempty : Nonempty {z : K // (z : G) ∉ K'} :=
    ⟨⟨⟨g, hgK⟩, hgK'⟩⟩
  letI : Nonempty {z : K // (z : G) ∉ K'} := hcompNonempty
  have hcomp : (Fintype.card {z : K // (z : G) ∉ K'} : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hrel :
      (Fintype.card {z : K // (z : G) ∉ K'} : ℂ) * psi g =
        (Nat.card K : ℂ) * (m : ℂ) - (Nat.card K' : ℂ) * (n : ℂ) := by
    rw [hsumK, hsumK'] at hsplit
    linear_combination hsplit
  refine ⟨((Nat.card K : ℚ) * (m : ℚ) - (Nat.card K' : ℚ) * (n : ℚ)) /
      (Fintype.card {z : K // (z : G) ∉ K'} : ℚ), ?_⟩
  calc
    psi g = ((Nat.card K : ℂ) * (m : ℂ) - (Nat.card K' : ℂ) * (n : ℂ)) /
        (Fintype.card {z : K // (z : G) ∉ K'} : ℂ) := by
      field_simp [hcomp]
      simpa [mul_comm] using hrel
    _ = (((Nat.card K : ℚ) * (m : ℚ) - (Nat.card K' : ℚ) * (n : ℚ)) /
        (Fintype.card {z : K // (z : G) ∉ K'} : ℚ) : ℚ) := by
      norm_num

/-- The source-result package for PF `(12.15)` implies the public projection,
constancy, and integrality conclusion. -/
public theorem theorem_12_15_of_source_result_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (RM : G → Subgroup G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (ψρM : Section1.ClassFunction M)
    (x : G) (p : ℕ)
    (hsrc :
      theorem_12_15_source_result_data M K K' P0 L H Ls E e S R τ τ₁ χ
        RM ψ ψρ ψρM x p)
    (h15src : theorem_12_15_source_data M K RM)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ)
    (hρM : dadeProjectionData (Section8.a1Set K) M RM ψ ψρM) :
    (∀ g : M, (g : G) ∈ K → (g : G) ≠ 1 → ψρM g = ψ (g : G)) ∧
    (∀ x y : G, x ∈ K → x ∉ K' → y ∈ K → y ∉ K' → ψ x = ψ y) ∧
    ∀ g : G, g ∈ K → g ∉ K' → ψ g ∈ Set.range (fun n : ℤ => (n : ℂ)) :=
  hsrc h15src h128 h129 h13 hρM

/-- Source leaf for the PF `(12.15)` endpoint: projection agreement on `K#`,
constancy on `K - K'`, and integrality of the resulting values. -/
public theorem theorem_12_15_result_source_leaf
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (RM : G → Subgroup G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (ψρM : Section1.ClassFunction M)
    (x : G) (p : ℕ) :
    theorem_12_15_source_result_data M K K' P0 L H Ls E e S R τ τ₁ χ
      RM ψ ψρ ψρM x p := by
  classical
  intro h15src h128 h129 h13 hρM
  have h128copy := h128
  have h129copy := h129
  have h13copy := h13
  rcases h15src with
    ⟨_hmin, hnotfrobM, AM, A0M, A1M, DM, tildeAM, tildeA0M, tildeA1M,
      hA1eq, _hMsSource, hnot10M, hnotM⟩
  have hnotMcopy := hnotM
  rcases hnotMcopy with
    ⟨hA1AM, hAMA0M, hDM, hRbotM, hUniqueM, hRsourceM,
      _htildeAM, _htildeA0M, _htildeA1M⟩
  rcases h128 with
    ⟨_hp, _hbad, _hminp, hMmax, hKMF, hTypeIM, hMsM, _hK', _hquot,
      _hP0Sylow⟩
  rcases h129 with
    ⟨_hP0comm, _hP0rank, _hLmax, hHMF, _hMsL, _hP0Ls, _hxL,
      _hxOmega, _hcentK, _hNxM, _hCnotL⟩
  rcases h13 with
    ⟨h12L, _hcomp, _he, _hchiS, _hdeg, _h78pack, _hnotpack,
      _hExt, _hpsi, hpsiclass, _hrho⟩
  have hTypeIL : Section8.typeIDefinitionData L H := h12L.2.2.1
  have hfrobL : Section7.frobeniusWithKernel L H :=
    theorem_12_10 M K K' P0 L H Ls x p h128copy h129copy
  have hnotconjML :
      ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L :=
    not_conj_of_hypothesis_12_8_12_9_typeI
      M K K' P0 L H Ls x p h128copy h129copy hTypeIL
  have hTypeIsets : AM = typeIASet M K ∧ A0M = typeIASet M K := by
    rcases hnot10M.2.2.2.2 with hI | hP
    · have hAM : AM = typeIASet M K := by
        rw [typeIASet_eq_section8CentralizerUnion]
        exact hI.2.1
      exact ⟨hAM, hI.2.2.trans hAM⟩
    · rcases hP with ⟨U, W1, W2, hP, _hTypes, _hA, _hA0, _hLate⟩
      exact False.elim
        (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeIM)
  have h815M : Section8.theorem_8_15_source_data M K K
      AM A0M A1M AM DM tildeAM tildeA0M tildeA1M RM :=
    ⟨hnot10M, hnotM, Or.inr (Or.inl rfl)⟩
  have h22Mraw : Section2.Hypothesis2 AM M RM :=
    Section8.theorem_8_15_hypothesis2 (inferInstance : IsMinCE G) h815M
  have h22M : Section2.Hypothesis2 (typeIASet M K) M RM := by
    simpa [hTypeIsets.1] using h22Mraw
  let tauM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G :=
    dadeTransformLinear RM h22M.subset_L
  rcases exists_puncturedInducedFamily (K.subgroupOf M) with ⟨SM, hSM⟩
  have hDadeM : dadeIsometryRelativeToTypeIASet M K RM tauM := by
    simpa [tauM] using
      dadeIsometryRelativeToTypeIASet_of_hypothesis2 M K RM h22M
  have h12M : hypothesis_12_1_data M K SM RM tauM :=
    ⟨hMmax, hKMF, hTypeIM, hSM, hDadeM⟩
  have hnotMtype : Section8.notation_8_14_source_data M
      (typeIASet M K) (typeIASet M K) (Section8.a1Set K)
      DM tildeAM tildeA0M tildeA1M RM := by
    simpa [hTypeIsets.1, hTypeIsets.2, hA1eq] using hnotM
  rcases theorem_12_15_typeI_orthogonality
      L H E M K e S R τ τ₁ χ ψ ψρ SM RM tauM DM
      tildeAM tildeA0M tildeA1M h13copy h12M hnotMtype hnotconjML with
    ⟨SXM, R1M, RfunM, hdataM, hRdataM, h52M, horthM⟩
  have hρMfull : dadeProjectionData (typeIASet M K) M RM ψ ψρM :=
    ⟨h22M, hρM.2⟩
  have hpart1 :
      ∀ g : M, (g : G) ∈ K → (g : G) ≠ 1 → ψρM g = ψ (g : G) := by
    intro g hgK hgne
    have hgA1 : (g : G) ∈ A1M := by
      rw [hA1eq]
      exact ⟨hgK, hgne⟩
    have hgAM : (g : G) ∈ AM := hA1AM hgA1
    have hgA0M : (g : G) ∈ A0M := hAMA0M hgAM
    by_cases hC : Subgroup.centralizer ({(g : G)} : Set G) ≤ M
    · have hgnotD : (g : G) ∉ DM := by
        rw [hDM]
        exact fun hgD => hgD.2 hC
      have hRMbot : RM (g : G) = ⊥ := hRbotM (g : G) ⟨hgA0M, hgnotD⟩
      letI : Fintype (RM (g : G)) := Fintype.ofFinite _
      rw [hρM.2, Section7.dadeProjection, Section2.dadeAveragingFunction]
      have hsum :
          (∑ z : RM (g : G), ψ ((g : G) * (z : G))) =
            (Nat.card (RM (g : G)) : ℂ) * ψ (g : G) := by
        calc
          (∑ z : RM (g : G), ψ ((g : G) * (z : G))) =
              ∑ _z : RM (g : G), ψ (g : G) := by
            apply Finset.sum_congr rfl
            intro z _hz
            have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
              simpa [hRMbot] using z.2
            simp [Subgroup.mem_bot.mp hzbot]
          _ = (Nat.card (RM (g : G)) : ℂ) * ψ (g : G) := by
            simp [Finset.card_univ]
      rw [hsum]
      field_simp [show (Nat.card (RM (g : G)) : ℂ) ≠ 0 by
        exact_mod_cast (Nat.card_pos (α := RM (g : G))).ne']
    · have hgD : (g : G) ∈ DM := by
        rw [hDM]
        exact ⟨hgA0M, hC⟩
      have hgD8 : (g : G) ∈ Section8.section8DSet M A0M := by
        simpa [hDM] using hgD
      rcases hUniqueM (g : G) hgD with ⟨N, hNcont, _hNuniq⟩
      have h813 := Section8.theorem_8_13 M K K AM A0M A1M A0M
        (inferInstance : IsMinCE G) hnot10M (Or.inr rfl)
      rcases h813.2.2.2 (g : G) hgD8 N hNcont with ⟨NF, hSupp⟩
      rcases hSupp with
        ⟨hNmax, hNMF, hNunique, _hsemiN, _hsemiC, _hcop, hNtype⟩
      have hTypeIbranch :
          Section8.typeIDefinitionData N NF ∧
            (g : G) ∈ Section8.section8CentralizerUnion N NF \ Section8.a1Set NF := by
        rcases hNtype with hI | hII
        · exact hI
        · rcases hII.2.2 with ⟨U, hcompM, hjoinM⟩
          exact False.elim (hnotfrobM
            (frobeniusWithKernel_of_section12FrobeniusJoinWithKernel hcompM
              (section16MFSubgroup_subgroupOf_normal hKMF) hjoinM))
      have hgTypeA : (g : G) ∈ typeIASet N NF := by
        rw [typeIASet_eq_section8CentralizerUnion]
        exact hTypeIbranch.2.1
      have hgnotNF : (g : G) ∉ NF := by
        intro hgNF
        apply hTypeIbranch.2.2
        exact ⟨hgNF, hgne⟩
      have hnotconjNL :
          ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) N L :=
        theorem_12_15_supporting_typeI_not_conjugate L H N NF hfrobL hHMF hNMF
          (g : G) hTypeIbranch.2
      have hcosetN : constantOnRightCoset NF ψ (g : G) :=
        theorem_12_15_psi_constant_on_typeI_kernel_coset
          L H E N NF e S R τ τ₁ χ ψ ψρ h13copy hNmax hNMF
          hTypeIbranch.1 hnotconjNL (g : G) hgTypeA.1 hgnotNF
      have hRMg : RM (g : G) = elementCentralizerIn NF (g : G) :=
        hRsourceM (g : G) hgD N NF hNunique hNMF
      have hRMle : RM (g : G) ≤ NF := by
        rw [hRMg]
        exact fun _ hz => hz.1
      letI : Fintype (RM (g : G)) := Fintype.ofFinite _
      rw [hρM.2, Section7.dadeProjection, Section2.dadeAveragingFunction]
      have hsum :
          (∑ z : RM (g : G), ψ ((g : G) * (z : G))) =
            (Nat.card (RM (g : G)) : ℂ) * ψ (g : G) := by
        calc
          (∑ z : RM (g : G), ψ ((g : G) * (z : G))) =
              ∑ _z : RM (g : G), ψ (g : G) := by
            apply Finset.sum_congr rfl
            intro z _hz
            exact hcosetN ⟨(z : G), hRMle z.2⟩
          _ = (Nat.card (RM (g : G)) : ℂ) * ψ (g : G) := by
            simp [Finset.card_univ]
      rw [hsum]
      field_simp [show (Nat.card (RM (g : G)) : ℂ) ≠ 0 by
        exact_mod_cast (Nat.card_pos (α := RM (g : G))).ne']
  have hpart2 :
      ∀ a b : G, a ∈ K → a ∉ K' → b ∈ K → b ∉ K' → ψ a = ψ b := by
    intro a b haK haNotK' hbK hbNotK'
    let aM : M := ⟨a, (section16MFSubgroup_le hKMF) haK⟩
    let bM : M := ⟨b, (section16MFSubgroup_le hKMF) hbK⟩
    have haNotDer : (a : G) ∉ ambientDerivedSubgroup K := by
      simpa [← _hK'] using haNotK'
    have hbNotDer : (b : G) ∉ ambientDerivedSubgroup K := by
      simpa [← _hK'] using hbNotK'
    have haNe : a ≠ 1 := by
      intro ha
      apply haNotK'
      simp [ha]
    have hbNe : b ≠ 1 := by
      intro hb
      apply hbNotK'
      simp [hb]
    have hconst := theorem_12_5 M K SM SXM RM R1M RfunM tauM ψ ψρM
      h12M hdataM hRdataM h52M hpsiclass horthM hρMfull
      aM bM haK haNotDer hbK hbNotDer
    calc
      ψ a = ψρM aM := (hpart1 aM haK haNe).symm
      _ = ψρM bM := hconst
      _ = ψ b := hpart1 bM hbK hbNe
  have hpsiVirt : Theory.Character.IsVirtualCharacter ψ := by
    rw [_hpsi]
    exact _hExt.2.1 χ (Section5.integerSpan_of_mem S _hchiS)
  have hK'K : K' ≤ K := by
    rw [_hK']
    exact section12_ambientDerivedSubgroup_le
  refine ⟨hpart1, hpart2, ?_⟩
  intro g hgK hgK'
  have hrat := theorem_12_15_value_isRational_of_constant_on_subgroup_complement
    K K' ψ hpsiVirt hK'K hpart2 g hgK hgK'
  have hint := theorem_12_15_virtualCharacter_value_isIntegral hpsiVirt g
  rcases Theory.Character.isaacs_lemma_3_2_core hint hrat with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Peterfalvi `(12.15)`.

Let `ρ_M` be the mapping defined in Hypothesis `(7.1)` with `M` and
`A₁(M)` in place of `L` and `A`.  Then `ψ^{ρ_M}(g) = ψ(g)` for
`g ∈ K^#`, `ψ` is constant on `K - K'`, and `ψ(g) ∈ ℤ` for
`g ∈ K - K'`. -/
public theorem theorem_12_15
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (RM : G → Subgroup G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (ψρM : Section1.ClassFunction M)
    (x : G) (p : ℕ)
    (h15src : theorem_12_15_source_data M K RM)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (h13 : notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ)
    (hρM : dadeProjectionData (Section8.a1Set K) M RM ψ ψρM) :
    (∀ g : M, (g : G) ∈ K → (g : G) ≠ 1 → ψρM g = ψ (g : G)) ∧
    (∀ x y : G, x ∈ K → x ∉ K' → y ∈ K → y ∉ K' → ψ x = ψ y) ∧
    ∀ g : G, g ∈ K → g ∉ K' → ψ g ∈ Set.range (fun n : ℤ => (n : ℂ)) := by
  exact theorem_12_15_of_source_result_data M K K' P0 L H Ls E e S R τ τ₁ χ
    RM ψ ψρ ψρM x p
    (theorem_12_15_result_source_leaf M K K' P0 L H Ls E e S R τ τ₁ χ
      RM ψ ψρ ψρM x p)
    h15src h128 h129 h13 hρM

end CFSG.Section12
