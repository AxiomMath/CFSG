module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_Common
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection10.PFsection10_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection11.PFsection11_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_2
-/

noncomputable section

open scoped BigOperators Pointwise commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u
open Section1 Section2 Section3 Section4

/-! ## (13.2) -/


private theorem section13_exists_transformedIrreducibleFamily
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (W : Subgroup M)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    ∃ R : Finset (Section1.ClassFunction G),
      Section11.transformedIrreducibleFamily R σ := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := W) with
    ⟨ι, hι, χrep, hχrep, _hsum⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let χ : ι → Section1.ClassFunction W :=
    fun i => Section1.ofConjClassFunction (χrep i)
  have hχirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (χ i) := by
    intro i
    exact Section10.ofConjClassFunction_isIrreducibleCharacterOnGroup_sec10
      (hχrep.1 i)
  have hχcomplete : ∀ θ : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup θ → ∃ i, χ i = θ := by
    intro θ hθirr
    let θrep : Theory.Character.ConjClassFunction W :=
      Section1.toConjClassFunction θ
        (Section10.isClassFunction_of_irreducibleCharacterOnGroup_sec10 hθirr)
    have hθrepirr : Theory.Character.IsIrreducibleConjCharacter θrep :=
      Section10.toConjClassFunction_isIrreducibleCharacter_of_onGroup_sec10 hθirr
    rcases hχrep.2.1 θrep hθrepirr with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext w
    change χrep i (ConjClasses.mk w) = θ w
    rw [hi]
    rfl
  refine ⟨Finset.univ.image (fun i => σ (χ i)), ?_⟩
  intro ψ
  constructor
  · intro hψ
    rcases Finset.mem_image.mp hψ with ⟨i, _hi, rfl⟩
    exact ⟨χ i, hχirr i, rfl⟩
  · rintro ⟨ω, hωirr, rfl⟩
    rcases hχcomplete ω hωirr with ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by rw [hi]⟩

private theorem section13_section11Subfamily_filter
    {G : Type u} [Group G] [Finite G]
    {M X : Subgroup G}
    (S : Finset (Section1.ClassFunction M))
    [DecidablePred fun χ : Section1.ClassFunction M =>
      Section1.subgroupInKernel' χ (X.subgroupOf M)]
    (hXM : X ≤ M) :
    Section11.section11Subfamily X S
      (S.filter fun χ => Section1.subgroupInKernel' χ (X.subgroupOf M)) := by
  classical
  constructor
  · exact hXM
  · intro χ
    simp

private def theorem_13_2_uBoundBranchData (p q u : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧
    (u ≤ (p - 1) ^ (q - 1) ∨ u ∣ (p ^ q - 1) / (p - 1))

private theorem section13_p_sub_one_pow_q_sub_one_le_geom_quotient
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  have hmem : q - 1 ∈ Finset.range q := by
    simpa using hq.pos
  have hterm_sum : p ^ (q - 1) ≤ ∑ i ∈ Finset.range q, p ^ i := by
    exact Finset.single_le_sum (by
      intro _ _
      exact Nat.zero_le _) hmem
  exact (Nat.pow_le_pow_left (Nat.sub_le p 1) (q - 1)).trans hterm_sum

private theorem section13_geom_quotient_pos_of_primes
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    0 < (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  have hmem0 : 0 ∈ Finset.range q := by
    simp [hq.pos]
  have hterm_sum : p ^ 0 ≤ ∑ i ∈ Finset.range q, p ^ i := by
    exact Finset.single_le_sum (by
      intro _ _
      exact Nat.zero_le _) hmem0
  have hone_le : 1 ≤ ∑ i ∈ Finset.range q, p ^ i := by
    simpa using hterm_sum
  exact lt_of_lt_of_le Nat.zero_lt_one hone_le

private theorem section13_theorem_13_2_u_bound_from_branchData
    {p q u : ℕ} (hdata : theorem_13_2_uBoundBranchData p q u) :
    u ≤ (p ^ q - 1) / (p - 1) := by
  rcases hdata with ⟨hp, hq, hsmall | hdiv⟩
  · exact hsmall.trans (section13_p_sub_one_pow_q_sub_one_le_geom_quotient hp hq)
  · exact Nat.le_of_dvd (section13_geom_quotient_pos_of_primes hp hq) hdiv

private theorem section13_natCard_fin_fun_multiplicative_zmod
    (a q : ℕ) [NeZero a] :
    Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) = a ^ (q - 1) := by
  rw [Nat.card_eq_fintype_card]
  simp

private theorem section13_theorem_13_2_uBoundBranchData_of_caseA
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hcaseA : case_9_7_a_sourceDataForSection13 M MF U W1 W2 C p q u) :
    theorem_13_2_uBoundBranchData p q u := by
  rcases hcaseA with ⟨hBarU, a, hcase⟩
  rcases hcase with
    ⟨_h92, _hH0le, _hCentIn, hp, hq, _hpdata, _hquot, _hcardQuot,
      hadvd, hinj⟩
  rcases hBarU with ⟨_hCU, _hnormalBar, hcardBar⟩
  rcases hinj with ⟨_hCUinj, _hnormalInj, φ, hφinj⟩
  refine ⟨hp, hq, Or.inl ?_⟩
  have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have ha_pos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
    rw [ha0, Nat.zero_dvd] at hadvd
    omega
  haveI : NeZero a := ⟨ha_pos.ne'⟩
  have hquot_le : Nat.card (U ⧸ C.subgroupOf U) ≤
      Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) :=
    Nat.card_le_card_of_injective φ hφinj
  have hquot_card :
      Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) = a ^ (q - 1) :=
    section13_natCard_fin_fun_multiplicative_zmod a q
  have hu_le_a : u ≤ a ^ (q - 1) := by
    rw [← hcardBar]
    exact hquot_le.trans_eq hquot_card
  have ha_le : a ≤ p - 1 := Nat.le_of_dvd hp_sub_pos hadvd
  exact hu_le_a.trans (Nat.pow_le_pow_left ha_le (q - 1))

private theorem section13_theorem_13_2_uBoundBranchData_of_caseB
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hcaseB : case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u) :
    theorem_13_2_uBoundBranchData p q u := by
  dsimp [case_9_7_b_sourceDataForSection13] at hcaseB
  rcases hcaseB with
    ⟨_h92, _hH0le, _hCentIn, hp, hq, _hpdata, _hquot, _hcentBy,
      _hcyclicQuot, _hirr, _hfield, _hcop, hdiv, _hprimeField⟩
  exact ⟨hp, hq, Or.inr hdiv⟩

private def theorem_13_2_case_9_7_setupData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 C : Subgroup G)
    (p q u : ℕ) : Prop :=
  Section9.hypothesis_9_2_statement Smax P U W1 W2 q ∧
    (∃ hp : Nat.Primes,
      hp.val = p ∧
        Section9.hoReductionData Smax P U W2 ⊥ hp ∧
        Section9.quotientChiefFactorData_9_6 Smax P ⊥ W1 hp) ∧
    Section9.quotientCentralizerIn P ⊥ U C ∧
    Section9.quotientBarUCardinality U C u

private def theorem_13_2_case_9_7_prereqData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 C : Subgroup G)
    (p q u : ℕ) : Prop :=
  Section9.hypothesis_9_2_statement Smax P U W1 W2 q ∧
    (∃ hp : Nat.Primes,
      hp.val = p ∧
        Section9.hoReductionData Smax P U W2 ⊥ hp ∧
        Section9.quotientChiefFactorData_9_6 Smax P ⊥ W1 hp) ∧
    Section9.quotientBarUCardinality U C u

private def theorem_13_2_case_9_7_corePrereqData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  Section9.hypothesis_9_2_statement Smax P U W1 W2 q ∧
    ∃ hp : Nat.Primes,
      hp.val = p ∧
        Section9.hoReductionData Smax P U W2 ⊥ hp ∧
        Section9.quotientChiefFactorData_9_6 Smax P ⊥ W1 hp

private theorem section13_typeP_U_le_normalizer_MF
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePDefinitionData M MF U W1 W2) :
    U ≤ Subgroup.normalizer (MF : Set G) := by
  rcases htype with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD, _hUnil, _hW1norm,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hMF with ⟨⟨hMFM, hMFNormalM, _hMFnil, _hMFHall⟩, _hmax⟩
  have hDleM : ambientDerivedSubgroup M ≤ M := section12_ambientDerivedSubgroup_le
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFNormalM
  exact hUleD.trans (hDleM.trans hM_le_norm_MF)

private theorem section13_subgroupCentralizerIn_subgroupOf_normal_of_le_normalizer
    {G : Type u} [Group G]
    {U P : Subgroup G}
    (hUnormP : U ≤ Subgroup.normalizer (P : Set G)) :
    ((subgroupCentralizerIn U P).subgroupOf U).Normal := by
  classical
  let C : Subgroup G := subgroupCentralizerIn U P
  have hCU : C ≤ U := inf_le_left
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCU).2 ?_
  intro u huU
  have huNormP : u ∈ Subgroup.normalizer (P : Set G) := hUnormP huU
  have huInvNormP : u⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem huNormP
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hxC
    refine ⟨U.mul_mem (U.mul_mem huU hxC.1) (U.inv_mem huU), ?_⟩
    change u * x * u⁻¹ ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hp_conj : u⁻¹ * p * u ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp huInvNormP p).1 hpP
    have hcomm : (u⁻¹ * p * u) * x = x * (u⁻¹ * p * u) :=
      Subgroup.mem_centralizer_iff.mp hxC.2 (u⁻¹ * p * u) hp_conj
    calc
      p * (u * x * u⁻¹) = u * ((u⁻¹ * p * u) * x) * u⁻¹ := by group
      _ = u * (x * (u⁻¹ * p * u)) * u⁻¹ := by rw [hcomm]
      _ = (u * x * u⁻¹) * p := by group
  · intro hxC
    have hUinvInv : (u⁻¹)⁻¹ ∈ U := by simpa using huU
    have hx' : u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹ ∈ C := by
      refine ⟨?_, ?_⟩
      · exact U.mul_mem (U.mul_mem (U.inv_mem huU) hxC.1) hUinvInv
      · change u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹ ∈
          Subgroup.centralizer (P : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro p hpP
        have hp_conj : u * p * u⁻¹ ∈ P := by
          simpa using (Subgroup.mem_normalizer_iff.mp huNormP p).1 hpP
        have hcomm : (u * p * u⁻¹) * (u * x * u⁻¹) =
            (u * x * u⁻¹) * (u * p * u⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hxC.2 (u * p * u⁻¹) hp_conj
        calc
          p * (u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹) =
              u⁻¹ * ((u * p * u⁻¹) * (u * x * u⁻¹)) * u := by group
          _ = u⁻¹ * ((u * x * u⁻¹) * (u * p * u⁻¹)) * u := by rw [hcomm]
          _ = (u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹) * p := by group
    simpa [C, mul_assoc] using hx'

private theorem section13_theorem_13_2_quotientBarUCardinality_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section9.quotientBarUCardinality U C u := by
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, hc_card,
      _hd_card, hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have hCU : C ≤ U := by
    rw [hC]
    exact inf_le_left
  have hUnormP : U ≤ Subgroup.normalizer (P : Set G) :=
    section13_typeP_U_le_normalizer_MF (M := Smax) (MF := P)
      (U := U) (W1 := W1) (W2 := W2) hptypeS
  have hnormal : (C.subgroupOf U).Normal := by
    rw [hC]
    exact section13_subgroupCentralizerIn_subgroupOf_normal_of_le_normalizer hUnormP
  refine ⟨hCU, hnormal, ?_⟩
  letI : (C.subgroupOf U).Normal := hnormal
  have hcard_sub : Nat.card (C.subgroupOf U) = Nat.card C :=
    natCard_subgroupOf_eq C U hCU
  have hlag : Nat.card U =
      Nat.card (U ⧸ C.subgroupOf U) * Nat.card (C.subgroupOf U) := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf U)
  rw [hcard_sub, ← hc_card] at hlag
  rw [hU_card] at hlag
  have hcpos : 0 < c := by
    rw [hc_card]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hcpos hlag.symm

private theorem section13_frobenius_U_sup_W1_of_typePDefinitionData
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePDefinitionData M MF U W1 W2)
    (hUne : U ≠ ⊥) :
    section12FrobeniusJoinWithKernel U W1 := by
  classical
  rcases htype with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1Hall, hMcomp, _hUleD, _hUnil, hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2leInf, _hW2cyc,
      _hW2ne, hcentralizer, _hnorm⟩
  rcases hDercomp with ⟨hMFleD, hUleD, _hD_eq, hMFUdisj⟩
  let S : Subgroup G := U ⊔ W1
  have hDdisjW1 : Disjoint (ambientDerivedSubgroup M) W1 := hMcomp.2.2.2
  have hUWdisj : Disjoint U W1 := by
    rw [disjoint_iff] at hDdisjW1 ⊢
    apply le_antisymm
    · exact (inf_le_inf_right W1 hUleD).trans (le_of_eq hDdisjW1)
    · exact bot_le
  have hW1leNormU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).1
  have hUnormalS : (U.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := U) (K := S) (by simp [S])).2
    simpa [S] using sup_le Subgroup.le_normalizer hW1leNormU
  have hUWcomp : section12ComplementIn S U W1 := by
    exact ⟨by simp [S], by simp [S], rfl, hUWdisj⟩
  have hUWdisjSub : Disjoint (U.subgroupOf S) (W1.subgroupOf S) := by
    rw [disjoint_iff] at hUWdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ W1 := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, S] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, S] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hUWdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hUWsupTop :
      U.subgroupOf S ⊔ W1.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := W1) (B := S)
      (by simp [S]) (by simp [S])]
    exact Subgroup.subgroupOf_eq_top.2 (by simp [S])
  have hUWcompSub : (U.subgroupOf S).IsComplement' (W1.subgroupOf S) := by
    letI : (U.subgroupOf S).Normal := hUnormalS
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf S) (W1.subgroupOf S) hUWdisjSub hUWsupTop
  have hUsub_ne : U.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hUne
    have hcard :
        Nat.card (U.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := U.subgroupOf S)).1 hbot
    have hcardU : Nat.card U = 1 := by
      rw [natCard_subgroupOf_eq U S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := U)).2 hcardU
  have hW1sub_ne : W1.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hW1ne
    have hcard :
        Nat.card (W1.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := W1.subgroupOf S)).1 hbot
    have hcardW1 : Nat.card W1 = 1 := by
      rw [natCard_subgroupOf_eq W1 S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := W1)).2 hcardW1
  have hcent :
      ∀ x : W1.subgroupOf S, x ≠ 1 →
        elementCentralizerIn (U.subgroupOf S) (x : S) = ⊥ := by
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyParts :
        y ∈ U.subgroupOf S ∧
          y ∈ Subgroup.centralizer ({(x : S)} : Set S) := by
      simpa [elementCentralizerIn] using hy
    let xG : G := ((x : S) : G)
    have hxW1 : xG ∈ W1 := by
      simpa [xG] using (Subgroup.mem_subgroupOf.mp x.property : ((x : S) : G) ∈ W1)
    have hxGne : xG ≠ 1 := by
      intro hxG
      apply hxne
      ext
      exact hxG
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf, S] using hyParts.1
    have hyDer : (y : G) ∈ ambientDerivedSubgroup M := hUleD hyU
    have hcentx : elementCentralizerIn (ambientDerivedSubgroup M) xG = W2 :=
      hcentralizer xG hxW1 hxGne
    have hyCommS : (y : S) * (x : S) = (x : S) * (y : S) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyParts.2
    have hyCommG : (y : G) * xG = xG * (y : G) := by
      simpa [xG] using congrArg Subtype.val hyCommS
    have hyCentX : (y : G) ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hyCommG.symm
    have hyElem : (y : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [elementCentralizerIn] using And.intro hyDer hyCentX
    have hyW2 : (y : G) ∈ W2 := by
      simpa [hcentx] using hyElem
    have hyMF : (y : G) ∈ MF := (hW2leInf hyW2).1
    have hyBot : (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hMFUdisj) hyMF hyU
    ext
    simpa using hyBot
  exact (lemma_3_1 (G := S) (K := U.subgroupOf S) (R := W1.subgroupOf S)
    hUsub_ne hW1sub_ne hUnormalS hUWcompSub).2 hcent

private theorem section13_quotientCentralizerIn_bot_of_subgroupCentralizerIn
    {G : Type u} [Group G]
    {P U C : Subgroup G}
    (hC : C = subgroupCentralizerIn U P) :
    Section9.quotientCentralizerIn P ⊥ U C := by
  subst C
  dsimp [Section9.quotientCentralizerIn, subgroupCentralizerIn]
  constructor
  · exact inf_le_left
  · intro x hxU
    constructor
    · intro hx h hP
      rcases hx with ⟨_hxU, hxcent⟩
      have hxcent' : x ∈ Subgroup.centralizer (P : Set G) := hxcent
      rw [Subgroup.mem_centralizer_iff] at hxcent'
      have hcomm : Commute x h := (Commute.eq (hxcent' h hP)).symm
      simpa [Subgroup.mem_bot] using hcomm.commutator_eq
    · intro hx
      refine ⟨hxU, ?_⟩
      have hxcent : x ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hP
        have hcomm_bot : ⁅x, h⁆ ∈ (⊥ : Subgroup G) := hx h hP
        have hcomm_eq : ⁅x, h⁆ = 1 := by
          simpa [Subgroup.mem_bot] using hcomm_bot
        rw [commutatorElement_def] at hcomm_eq
        have hmul := congrArg (fun z : G => z * h * x) hcomm_eq
        simp [mul_assoc] at hmul
        exact hmul.symm
      exact hxcent

private theorem section13_theorem_13_2_case_9_7_sourceData_from_setupData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax P U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hsetup : theorem_13_2_case_9_7_setupData Smax P U W1 W2 C p q u) :
    case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u ∨
      case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  rcases hsetup with ⟨h92, hp96, hCent, hBarU⟩
  rcases Section9.theorem_9_7_source_core_sec9 Smax P U W1 W2 ⊥ C p q u
      h92 hp96 hCent hBarU with
    hcaseA | hcaseB
  · rcases hcaseA with ⟨a, hcaseA⟩
    exact Or.inl ⟨hBarU, a, hcaseA⟩
  · exact Or.inr hcaseB

private def theorem_13_2_case_9_7_hypothesis95BotData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 C : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p : ℕ) : Prop :=
  ∃ Cprime : Subgroup G, ∃ hp : Nat.Primes,
    hp.val = p ∧
      Section9.Hypothesis_9_5 Smax P U W1 W2 (⊥ : Subgroup G)
        C Cprime τS Sfam ∧
      Section9.hoReductionData Smax P U W2 (⊥ : Subgroup G) hp

private def theorem_13_2_case_9_7_hypothesis95CoreData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p : ℕ) : Prop :=
  Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1) ∧
    (∃ hp : Nat.Primes, hp.val = p ∧
      Section9.hoReductionData Smax P U W2 (⊥ : Subgroup G) hp) ∧
    Section9.dadeIsometryRelativeToASet Smax U τS ∧
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
        (⊥ : Subgroup G) Sfam ∧
    Section5.hypothesis_5_2_b_statement Sfam τS

public theorem section13_theorem_13_2_global_isMinCE_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    IsMinCE G := by
  rcases _hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  exact hMin

private theorem section13_commutator_map_subtype_le
    {G : Type u} [Group G]
    (C : Subgroup G) :
    (_root_.commutator C).map C.subtype ≤ C := by
  rintro x ⟨y, _hy, rfl⟩
  exact y.property

private def theorem_13_2_typeCommonT6FusionData
    {G : Type u} [Group G]
    (M MF U : Subgroup G) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    Subgroup.normalizer (M : Set G) = M ∧
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥

private def theorem_13_2_typeCommonT6FusionCoreData
    {G : Type u} [Group G]
    (M MF U : Subgroup G) : Prop :=
  Subgroup.normalizer (M : Set G) = M ∧
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥

private def theorem_13_2_typeCommonT6FusionCentralizerData
    {G : Type u} [Group G]
    (M MF U : Subgroup G) : Prop :=
  ∀ X : Subgroup G,
    X ≤ U →
      X ≠ ⊥ →
        subgroupCentralizerIn MF X ≠ ⊥ →
          section9MaximalSubgroupsContaining
            (Subgroup.centralizer (X : Set G)) = {M}

private def theorem_13_2_typeCommonT6Data
    {G : Type u} [Group G]
    (M MF U : Subgroup G) : Prop :=
  ∀ A0 A1 : Subgroup G,
    section16PrimeOrderSubgroupOf A0 U →
      section16PrimeOrderSubgroupOf A1 U →
        section16ConjugateSubgroupsIn ⊤ A0 A1 →
          ¬ section16ConjugateSubgroupsIn M A0 A1 →
            subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥

private def theorem_13_2_typeCommonT6FusionUniqueData
    {G : Type u} [Group G]
    (M MF U : Subgroup G) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    Subgroup.normalizer (M : Set G) = M ∧
    theorem_13_2_typeCommonT6FusionCentralizerData M MF U

private theorem section13_maximal_normalizer_eq_self_of_isMinCE
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
  have hMsigmaSub_ne : section10MsigmaSubgroup M ≠ ⊥ := by
    intro hbot
    exact hMsigma_ne (by simp [section10Msigma, hbot])
  have hnorm :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      (G := G) hM (N := section10MsigmaSubgroup M) hMsigmaSub_ne
  have hnormSigma :
      Subgroup.normalizer (section10Msigma M : Set G) = M := by
    simpa [section10Msigma] using hnorm
  apply le_antisymm
  · intro g hgNormM
    have hle :
        Subgroup.normalizer (M : Set G) ≤
          Subgroup.normalizer
            (((section10MsigmaSubgroup M : Subgroup M).map M.subtype : Subgroup G) : Set G) :=
      section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (H := M) (K := section10MsigmaSubgroup M)
    have hgNormSigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) := by
      simpa [section10Msigma] using hle hgNormM
    simpa [hnormSigma] using hgNormSigma
  · exact Subgroup.le_normalizer

private theorem section13_ne_bot_of_hasPrimeOrder
    {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} (hA : section16HasPrimeOrder A) :
    A ≠ ⊥ := by
  rcases hA with ⟨p, hcard⟩
  intro hbot
  have hcard_one : Nat.card A = 1 := by
    simp [hbot]
  have hpone : p.val = 1 := by
    rw [← hcard, hcard_one]
  exact p.property.ne_one hpone

private theorem section13_nat_prime_card_of_hasPrimeOrder
    {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} (hA : section16HasPrimeOrder A) :
    Nat.Prime (Nat.card A) := by
  rcases hA with ⟨p, hp⟩
  rw [hp]
  exact p.property

private theorem section13_centralizer_conjBy
    {G : Type u} [Group G]
    (X : Subgroup G) (a : G) :
    (Subgroup.centralizer (X : Set G)).conjBy a =
      Subgroup.centralizer (X.conjBy a : Set G) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro x hxX
    rcases Subgroup.mem_map.mp hxX with ⟨x0, hx0, rfl⟩
    have hcomm := hz x0 hx0
    have hcomm' := congrArg (fun t : G => a * t * a⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hy
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨a⁻¹ * y * a, ?_, by simp [mul_assoc, MulAut.conj_apply]⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hxX
    have hxX' : a * x * a⁻¹ ∈ X.conjBy a := by
      exact Subgroup.mem_map.mpr ⟨x, hxX, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hcomm := hy (a * x * a⁻¹) hxX'
    have hcomm' := congrArg (fun t : G => a⁻¹ * t * a) hcomm
    simpa [mul_assoc] using hcomm'

private theorem section13_centralizer_nonidentityElements_subgroup
    {G : Type u} [Group G]
    (X : Subgroup G) :
    Subgroup.centralizer (section16NonidentityElements (X : Set G)) =
      Subgroup.centralizer (X : Set G) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hxX
    by_cases hx1 : x = 1
    · simp [hx1]
    · exact hy x ⟨hxX, hx1⟩
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    exact hy x hx.1

private theorem section13_maximalSubgroupsContaining_centralizer_conjBy
    {G : Type u} [Group G] [Finite G]
    {X M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (g : G)
    (huniq : section9MaximalSubgroupsContaining
      (Subgroup.centralizer (X : Set G)) = {M}) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer (X.conjBy g : Set G)) = {M.conjBy g} := by
  ext H
  constructor
  · intro hH
    have hHinv :
        H.conjBy g⁻¹ ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      refine ⟨section10_maximal_conjBy (G := G) hH.1 g⁻¹, ?_⟩
      intro x hxC
      have hxCgMap :
          g * x * g⁻¹ ∈ (Subgroup.centralizer (X : Set G)).conjBy g := by
        exact Subgroup.mem_map.mpr ⟨x, hxC, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hxCg : g * x * g⁻¹ ∈ Subgroup.centralizer (X.conjBy g : Set G) := by
        simpa [section13_centralizer_conjBy (G := G) X g] using hxCgMap
      have hxH : g * x * g⁻¹ ∈ H := hH.2 hxCg
      exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hxH, by
        simp [mul_assoc]⟩
    have hHinv_eq : H.conjBy g⁻¹ = M := by
      have hmem : H.conjBy g⁻¹ ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq] using hHinv
      simpa using hmem
    have hHeq : H = M.conjBy g := by
      calc
        H = (H.conjBy g⁻¹).conjBy g := (Subgroup.conjBy_inv' H g).symm
        _ = M.conjBy g := by rw [hHinv_eq]
    simp [hHeq]
  · intro hH
    simp at hH
    subst hH
    have hMcent :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      simp [huniq]
    refine ⟨section10_maximal_conjBy (G := G) hM g, ?_⟩
    intro x hxC
    have hxBackMap :
        g⁻¹ * x * g ∈
          (Subgroup.centralizer (X.conjBy g : Set G)).conjBy g⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨x, hxC, by simp [mul_assoc]⟩
    have hxBack : g⁻¹ * x * g ∈ Subgroup.centralizer (X : Set G) := by
      have hxBack' :
          g⁻¹ * x * g ∈ Subgroup.centralizer (((X.conjBy g).conjBy g⁻¹) : Set G) := by
        simpa [section13_centralizer_conjBy (G := G) (X := X.conjBy g) (a := g⁻¹)]
          using hxBackMap
      simpa [Subgroup.conjBy_inv] using hxBack'
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hMcent.2 hxBack, by
      simp [MulAut.conj_apply, mul_assoc]⟩

private theorem section13_typeCommonT6_of_fusionData
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hdata : theorem_13_2_typeCommonT6FusionData M MF U) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨
                subgroupCentralizerIn MF A1 = ⊥ := by
  exact hdata.2.2

private theorem section13_typeCommonT6_of_fusionUniqueData
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hdata : theorem_13_2_typeCommonT6FusionUniqueData M MF U) :
    theorem_13_2_typeCommonT6Data M MF U := by
  classical
  rcases hdata with ⟨hMmax, hSelfNorm, hfusion⟩
  intro A0 A1 hA0 hA1 hconj hnotMconj
  by_cases hC0 : subgroupCentralizerIn MF A0 = ⊥
  · exact Or.inl hC0
  · right
    by_contra hC1
    rcases hconj with ⟨g, _hgTop, hgEq⟩
    have hA0ne : A0 ≠ ⊥ := section13_ne_bot_of_hasPrimeOrder hA0.2
    have hA1ne : A1 ≠ ⊥ := section13_ne_bot_of_hasPrimeOrder hA1.2
    have huniq0 :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (A0 : Set G)) = {M} :=
      hfusion A0 hA0.1 hA0ne hC0
    have huniq1 :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (A1 : Set G)) = {M} :=
      hfusion A1 hA1.1 hA1ne hC1
    have huniq1_from0 :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (A1 : Set G)) = {M.conjBy g} := by
      simpa [hgEq] using
        section13_maximalSubgroupsContaining_centralizer_conjBy
          (G := G) (X := A0) (M := M) hMmax g huniq0
    have hMg_mem :
        M.conjBy g ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer (A1 : Set G)) := by
      simp [huniq1_from0]
    have hMg_eq_M : M.conjBy g = M := by
      have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq1] using hMg_mem
      simpa using hsingle
    have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
      section10_mem_normalizer_of_conjBy_eq (G := G) hMg_eq_M
    have hgM : g ∈ M := by
      simpa [hSelfNorm] using hgNormM
    exact hnotMconj ⟨g, hgM, hgEq⟩

private theorem section13_TISubset_of_nonidentityElements
    {G : Type u} [Group G] [Finite G] {X : Set G}
    (h : section16TISubset (section16NonidentityElements X)) :
    section16TISubset X := by
  have hsharp_conj : ∀ g : G,
      section16NonidentityElements (section16ConjugateSet X g) =
        section16ConjugateSet (section16NonidentityElements X) g := by
    intro g
    ext z
    constructor
    · rintro ⟨hz, hz1⟩
      rcases hz with ⟨x, hx, rfl⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hx1
      apply hz1
      simp [hx1]
    · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      intro hconj_one
      apply hx1
      have := congrArg (fun t => g⁻¹ * t * g) hconj_one
      simpa [mul_assoc] using this
  intro g
  rcases h g with hconj | hdisj
  · left
    ext y
    constructor
    · intro hy
      by_cases hy1 : y = 1
      · rcases hy with ⟨x, hx, hxy⟩
        rw [hy1] at hxy
        have hx1 : x = 1 := by
          have := congrArg (fun t => g⁻¹ * t * g) hxy.symm
          simpa [mul_assoc] using this
        simpa [hy1, hx1] using hx
      · have hysharp : y ∈ section16NonidentityElements (section16ConjugateSet X g) :=
          ⟨hy, hy1⟩
        have : y ∈ section16ConjugateSet (section16NonidentityElements X) g := by
          simpa [hsharp_conj g] using hysharp
        have : y ∈ section16NonidentityElements X := by
          simpa [hconj] using this
        exact this.1
    · intro hy
      by_cases hy1 : y = 1
      · refine ⟨1, ?_, ?_⟩
        · simpa [← hy1] using hy
        · simp [hy1]
      · have : y ∈ section16NonidentityElements X := ⟨hy, hy1⟩
        have : y ∈ section16ConjugateSet (section16NonidentityElements X) g := by
          simpa [hconj] using this
        rcases this with ⟨x, hx, rfl⟩
        exact ⟨x, hx.1, rfl⟩
  · right
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    · apply hdisj
      constructor
      · exact ⟨hy.1, hy1⟩
      · have : y ∈ section16NonidentityElements (section16ConjugateSet X g) :=
          ⟨hy.2, hy1⟩
        simpa [hsharp_conj g] using this

private theorem section13_section16TypeIIToIVExtra_of_sourceCondition
    {G : Type u} [Group G] [Finite G]
    {M U W1 : Subgroup G}
    (h : Section8.typeIIToIVSourceCondition M U W1) :
    section16TypeIIToIVExtra M W1 :=
  ⟨h.2.1, section13_TISubset_of_nonidentityElements h.2.2⟩

private theorem section12ComplementIn_isComplement'_subgroupOf_for_final
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    [hHNormal : (H.subgroupOf M).Normal] :
    (K.subgroupOf M).IsComplement' (H.subgroupOf M) := by
  rcases hcomp with ⟨hHM, hKM, hsup, hdisj⟩
  have hsup_local : K.subgroupOf M ⊔ H.subgroupOf M = ⊤ := by
    calc
      K.subgroupOf M ⊔ H.subgroupOf M = (K ⊔ H).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := K) (A' := H) (B := M) hKM hHM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxK hxH
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxH,
      by simpa [Subgroup.mem_subgroupOf] using hxK⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (K.subgroupOf M) (H.subgroupOf M)).symm

/-- Restrict a Hall subgroup in an ambient subgroup to an intermediate
overgroup. -/
private theorem section12HallSubgroupIn_of_le_overgroup_for_final
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {K E M : Subgroup G}
    (hHall : section12HallSubgroupIn π K M)
    (hKE : K ≤ E) (hEM : E ≤ M) :
    section12HallSubgroupIn π K E := by
  classical
  rcases hHall with ⟨_hKM, hHallM⟩
  refine ⟨hKE, ?_⟩
  refine isHallSubgroup_of (G := E) (π := π) (H := K.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (K.subgroupOf E) = Nat.card K :=
      natCard_subgroupOf_eq K E hKE
    have hcardM : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M (hKE.trans hEM)
    have hcardEF : Fintype.card (K.subgroupOf E) = Fintype.card K := by
      simpa [Nat.card_eq_fintype_card] using hcardE
    have hcardMF : Fintype.card (K.subgroupOf M) = Fintype.card K := by
      simpa [Nat.card_eq_fintype_card] using hcardM
    have hpK : p.val ∣ Fintype.card K := by
      simpa [hcardEF] using hp
    have hpM : p.val ∣ Fintype.card (K.subgroupOf M) := by
      simpa [hcardMF] using hpK
    exact hHallM.p_in_pi_of_p_dvd_card p (by
      simpa [Nat.card_eq_fintype_card] using hpM)
  · intro p hpπ hpidx
    let EsubM : Subgroup M := E.subgroupOf M
    have hKsub_le_Esub : K.subgroupOf M ≤ EsubM := by
      intro x hx
      exact hKE hx
    have hrel_eq :
        (K.subgroupOf E).index = (K.subgroupOf M).relIndex EsubM := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := K) (K := E) (L := M) hEM
      simpa [EsubM, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (K.subgroupOf E).index ∣ (K.subgroupOf M).index := by
      have hrel_dvd :
          (K.subgroupOf M).relIndex EsubM ∣ (K.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hKsub_le_Esub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

/-- Transfer a Hall-in-`M` field across subgroups of equal cardinality. -/
private theorem section12HallSubgroupIn_of_natCard_eq_for_final
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {H K M : Subgroup G}
    (hKHall : section12HallSubgroupIn π K M)
    (hHM : H ≤ M)
    (hcard : Nat.card H = Nat.card K) :
    section12HallSubgroupIn π H M := by
  classical
  rcases hKHall with ⟨hKM, hKHallSub⟩
  refine ⟨hHM, ?_⟩
  have hcardHsub : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M hHM
  have hcardKsub : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKM
  have hcardSub : Nat.card (H.subgroupOf M) = Nat.card (K.subgroupOf M) := by
    rw [hcardHsub, hcardKsub, hcard]
  have hidxEq : (H.subgroupOf M).index = (K.subgroupOf M).index := by
    have hmulH :
        (H.subgroupOf M).index * Nat.card (H.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := H.subgroupOf M)
    have hmulK :
        (K.subgroupOf M).index * Nat.card (K.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := K.subgroupOf M)
    have hmul :
        (H.subgroupOf M).index * Nat.card (H.subgroupOf M) =
          (K.subgroupOf M).index * Nat.card (K.subgroupOf M) :=
      hmulH.trans hmulK.symm
    rw [hcardSub] at hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := K.subgroupOf M)) hmul
  refine isHallSubgroup_of (G := M) (π := π) (H := H.subgroupOf M) ?_ ?_
  · intro p hpH
    have hcardSubF :
        Fintype.card (H.subgroupOf M) = Fintype.card (K.subgroupOf M) := by
      simpa [Nat.card_eq_fintype_card] using hcardSub
    have hpKNat : p.val ∣ Fintype.card (K.subgroupOf M) := by
      simpa [hcardSubF] using hpH
    exact hKHallSub.p_in_pi_of_p_dvd_card p (by
      simpa [Nat.card_eq_fintype_card] using hpKNat)
  · intro p hpπ hpidx
    exact (hKHallSub.p_in_pi_of_p_dvd_index p (by
      simpa [hidxEq] using hpidx)) hpπ

/-- A nontrivial finite subgroup contains a subgroup of prime order. -/
private theorem section12_exists_primeOrderSubgroup_of_ne_bot_for_final
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G}
    (hHne : H ≠ ⊥) :
    ∃ X : Subgroup G, X ∈ section12PrimeOrderSubgroups H := by
  classical
  have hcard_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hHne ((Subgroup.card_eq_one (H := H)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  haveI : Fact p.Prime := ⟨hpprime⟩
  rcases exists_prime_orderOf_dvd_card' (G := H) p hpdiv with ⟨zH, hzH_order⟩
  let z : G := zH
  refine ⟨Subgroup.zpowers z, ?_⟩
  have hzH : z ∈ H := zH.property
  have hz_order : orderOf z = p := by
    simpa [z, Subgroup.orderOf_coe] using hzH_order
  refine ⟨Subgroup.zpowers_le.mpr hzH, ⟨⟨p, hpprime⟩, ?_⟩⟩
  exact (Nat.card_zpowers z).trans hz_order

/-- A Sylow subgroup of a Hall subgroup is also a Sylow subgroup of the
ambient group. -/
private theorem isHallSubgroup_sylow_map_to_overgroup_sylow_for_final
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {K : Subgroup H}
    (hKHall : IsHallSubgroup π K) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H, (PH : Subgroup H) = (P : Subgroup K).map K.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup H := (P : Subgroup K).map K.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup K)) P.isPGroup' K.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup K).index * K.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := K) (K := (P : Subgroup K)))
    have hp_prod : p.val ∣ (P : Subgroup K).index * K.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpKidx
    · exact P.not_dvd_index hpPidx
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpKidx) hpπ
  let PH : Sylow p.val H := hPsubp.toSylow hnot_index
  exact ⟨PH, by simp [PH, Psub, IsPGroup.toSylow_coe]⟩

/-- If one Sylow `p`-subgroup is cyclic, then the `p`-rank is at most one. -/
private theorem primeRank_le_one_of_cyclic_sylow_for_final
    {p : ℕ} {R : Type*} [Group R] [Finite R] [Fact p.Prime]
    (S : Sylow p R) (hS_cyc : IsCyclic (S : Subgroup R)) :
    primeRank p R ≤ 1 := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · letI : IsCyclic (S : Subgroup R) := hS_cyc
    refine ⟨0, ?_⟩
    exact ⟨(S : Subgroup R), S.isPGroup', inferInstance, by simp⟩
  · intro n hn
    rcases hn with ⟨A, hAp, _hAcomm, hnA⟩
    obtain ⟨T, hA_le_T⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S T
    have hT_cyc : IsCyclic (T : Subgroup R) := by
      let e :
          (S : Subgroup R) ≃* ((g • S : Sylow p R) : Subgroup R) :=
        Subgroup.equivMapOfInjective
          (f := (MulAut.conj g).toMonoidHom) (S : Subgroup R)
          (EquivLike.injective (MulAut.conj g))
      have hconj_cyc : IsCyclic (((g • S : Sylow p R) : Subgroup R)) :=
        e.isCyclic.mp hS_cyc
      rw [← hg]
      exact hconj_cyc
    have hA_cyc : IsCyclic A := Subgroup.isCyclic_of_le hA_le_T
    exact hnA.trans (generatorRank_le_one_of_isCyclic (G := A) hA_cyc)

/-- A cyclic Hall subgroup forces every prime in its Hall set to have rank at
most one in the ambient group. -/
private theorem primeRank_le_one_of_cyclic_hall_subgroup_for_final
    {R : Type*} [Group R] [Finite R]
    {π : Set Nat.Primes} {K : Subgroup R} {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K)
    (hpπ : p ∈ π)
    (hKcyc : IsCyclic K) :
    primeRank p.val R ≤ 1 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let PK : Sylow p.val K := Classical.choice (Sylow.nonempty (p := p.val) (G := K))
  rcases isHallSubgroup_sylow_map_to_overgroup_sylow_for_final
      (H := R) (K := K) hKHall hpπ PK with
    ⟨PR, hPReq⟩
  have hPKcyclic : IsCyclic (PK : Subgroup K) := by
    letI : IsCyclic K := hKcyc
    exact Subgroup.isCyclic_of_le (show (PK : Subgroup K) ≤ ⊤ from le_top)
  let Pmap : Subgroup R := (PK : Subgroup K).map K.subtype
  have hPmapCyclic : IsCyclic Pmap := by
    let e :
        (PK : Subgroup K) ≃* Pmap :=
      Subgroup.equivMapOfInjective
        (f := K.subtype) (PK : Subgroup K) K.subtype_injective
    exact e.isCyclic.mp hPKcyclic
  have hPRcyclic : IsCyclic (PR : Subgroup R) := by
    rw [hPReq]
    simpa [Pmap] using hPmapCyclic
  exact primeRank_le_one_of_cyclic_sylow_for_final PR hPRcyclic

/-- Two complements to the same normal subgroup have equal cardinality. -/
private theorem natCard_eq_of_section12ComplementIn_same_normal_left_for_final
    {G : Type u} [Group G] [Finite G]
    {M D H K : Subgroup G}
    (hDnormal : (D.subgroupOf M).Normal)
    (hHcomp : section12ComplementIn M D H)
    (hKcomp : section12ComplementIn M K D) :
    Nat.card H = Nat.card K := by
  classical
  letI : (D.subgroupOf M).Normal := hDnormal
  have hKcompSymm : section12ComplementIn M D K := by
    refine ⟨hKcomp.2.1, hKcomp.1, ?_, hKcomp.2.2.2.symm⟩
    rw [sup_comm]
    exact hKcomp.2.2.1
  have hHlocal : (H.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := D) (K := H) hHcomp
  have hKlocal : (K.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := D) (K := K) hKcompSymm
  have hDindexH : (D.subgroupOf M).index = Nat.card (H.subgroupOf M) :=
    hHlocal.index_eq_card
  have hDindexK : (D.subgroupOf M).index = Nat.card (K.subgroupOf M) :=
    hKlocal.index_eq_card
  have hHcard : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M hHcomp.2.1
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKcomp.1
  calc
    Nat.card H = Nat.card (H.subgroupOf M) := hHcard.symm
    _ = (D.subgroupOf M).index := hDindexH.symm
    _ = Nat.card (K.subgroupOf M) := hDindexK
    _ = Nat.card K := hKcard

/-- In a complement decomposition, if the left factor is Hall for `π` and the
right factor is normal, then the right factor is Hall for `πᶜ`. -/
private theorem section12ComplementIn_right_isHall_compl_of_left_hall_for_final
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {R K U : Subgroup G}
    (hcomp : section12ComplementIn R K U)
    (hUnormal : section10NormalIn U R)
    (hKHall : section12HallSubgroupIn π K R) :
    section12HallSubgroupIn πᶜ U R := by
  classical
  rcases hcomp with ⟨hKR, hUR, hsup, hdisj⟩
  rcases hKHall with ⟨_hKR', hKHallSub⟩
  have hcompSymm : section12ComplementIn R U K := by
    refine ⟨hUR, hKR, ?_, hdisj.symm⟩
    calc
      R = K ⊔ U := hsup
      _ = U ⊔ K := sup_comm K U
  letI : (U.subgroupOf R).Normal := hUnormal.2
  have hcompLocal : (K.subgroupOf R).IsComplement' (U.subgroupOf R) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := R) (H := U) (K := K) hcompSymm
  refine ⟨hUR, ?_⟩
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := U.subgroupOf R) ?_ ?_
  · intro q hqU hqπ
    have hqKidx : q.val ∣ (K.subgroupOf R).index := by
      simpa [hcompLocal.symm.index_eq_card] using hqU
    exact (hKHallSub.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqUidx
    have hqK : q.val ∣ Nat.card (K.subgroupOf R) := by
      simpa [hcompLocal.index_eq_card] using hqUidx
    exact hqπc (hKHallSub.p_in_pi_of_p_dvd_card q hqK)
private theorem source_typeP_T6_of_U_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hUbot : U = ⊥) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  intro A0 _A1 hA0 _hA1 _hConj _hNotM
  rcases hA0.2 with ⟨p, hcard⟩
  have hA0bot : A0 = ⊥ := by
    rw [hUbot] at hA0
    exact le_bot_iff.mp hA0.1
  rw [hA0bot] at hcard
  have hpone : p.val = 1 := by
    simpa using hcard.symm
  exact False.elim (p.property.ne_one hpone)

/-- In the source Type-P branch with `U` not contained in `M_sigma`, the
recorded nilpotent Hall subgroup `M_F` must be exactly `M_sigma`.

If `M_F` were properly smaller, Theorem 15.2(d) identifies
`M_sigma = M'`; the source Type-P containment `U ≤ M'` would then put `U`
inside `M_sigma`, contradicting the branch hypothesis. -/
private theorem source_typeP_MF_eq_msigma_of_not_le_msigma
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    MF = section10Msigma M := by
  letI : IsMinCE G := hmin
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hMF15 : section15MFSubgroup M MF := by
    simpa [section16MFSubgroup, section16NilpotentNormalHallIn,
      section15MFSubgroup, section15NilpotentNormalHallIn] using hMF
  by_contra hMFne
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U0, hKU⟩
  rcases theorem_15_2_c (G := G) (M := M) (MF := MF) (K := K)
      hM hMF15 hKU.1 hMFne with
    ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
  rcases theorem_15_2_d (G := G) (M := M) (MF := MF) (K := K)
      (Q := Q) hM hMF15 hKU.1 hMFne hq hQ hQnormal hQMF with
    ⟨D0, hD0⟩
  have hUσ : U ≤ section10Msigma M := by
    intro x hx
    simpa [hD0.1] using hUleD hx
  exact hUnotσ hUσ

/-- Once source Type-P data has been reduced to `M_F = M_sigma`, the
complement and normality fields in the candidate `KUData` package with
`K = W1` are formal consequences of the recorded source complements. -/
private theorem source_typeP_W1_KUData_structural_fields
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    section12ComplementIn M W1 (U ⊔ section10Msigma M) ∧
      section12ComplementIn M (section10Msigma M) (W1 ⊔ U) ∧
      section10NormalIn (U ⊔ section10Msigma M) M ∧
      section10NormalIn U (W1 ⊔ U) := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD,
      _hUnil, hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hD_eq : ambientDerivedSubgroup M = MF ⊔ U := hDercomp.2.2.1
  have hD_eq_sigma : ambientDerivedSubgroup M = section10Msigma M ⊔ U := by
    simpa [hMFeq] using hD_eq
  have hD_eq_USigma : ambientDerivedSubgroup M = U ⊔ section10Msigma M := by
    calc
      ambientDerivedSubgroup M = MF ⊔ U := hD_eq
      _ = section10Msigma M ⊔ U := by rw [hMFeq]
      _ = U ⊔ section10Msigma M := sup_comm (section10Msigma M) U
  rcases hMcomp with ⟨hDM, hW1M, hM_eq, hD_W1_disj⟩
  rcases hDercomp with ⟨hMFD, hUD, _hD_eq', hMF_U_disj⟩
  have hSigmaM : section10Msigma M ≤ M := by
    intro x hx
    exact hDM (by simpa [hMFeq] using hMFD (by simpa [hMFeq] using hx))
  have hW1U_M : W1 ⊔ U ≤ M :=
    sup_le hW1M (hUD.trans hDM)
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1norm hw)).1
  have hcompW1USigma : section12ComplementIn M W1 (U ⊔ section10Msigma M) := by
    refine ⟨hW1M, ?_, ?_, ?_⟩
    · rw [← hD_eq_USigma]
      exact hDM
    · calc
        M = ambientDerivedSubgroup M ⊔ W1 := hM_eq
        _ = W1 ⊔ ambientDerivedSubgroup M := sup_comm (ambientDerivedSubgroup M) W1
        _ = W1 ⊔ (U ⊔ section10Msigma M) := by rw [← hD_eq_USigma]
    · rw [← hD_eq_USigma]
      exact hD_W1_disj.symm
  have hcompSigmaW1U : section12ComplementIn M (section10Msigma M) (W1 ⊔ U) := by
    refine ⟨hSigmaM, hW1U_M, ?_, ?_⟩
    · calc
        M = ambientDerivedSubgroup M ⊔ W1 := hM_eq
        _ = (section10Msigma M ⊔ U) ⊔ W1 := by rw [hD_eq_sigma]
        _ = section10Msigma M ⊔ (W1 ⊔ U) := by
          simp [sup_comm, sup_left_comm]
    · rw [Subgroup.disjoint_def]
      intro x hxSigma hxW1U
      have hW1U_mul :
          ((W1 ⊔ U : Subgroup G) : Set G) = (W1 : Set G) * (U : Set G) := by
        exact Subgroup.coe_mul_of_left_le_normalizer_right
          (H := W1) (N := U) hW1_norm_U
      have hxW1Uset : x ∈ ((W1 ⊔ U : Subgroup G) : Set G) := hxW1U
      rw [hW1U_mul, Set.mem_mul] at hxW1Uset
      rcases hxW1Uset with ⟨w, hwW1, u, huU, hwu⟩
      have hxD : x ∈ ambientDerivedSubgroup M := by
        simpa [hMFeq] using hMFD (by simpa [hMFeq] using hxSigma)
      have hwD : w ∈ ambientDerivedSubgroup M := by
        have hw_eq : w = x * u⁻¹ := by
          rw [← hwu]
          simp [mul_assoc]
        rw [hw_eq]
        exact (ambientDerivedSubgroup M).mul_mem hxD (hUD (U.inv_mem huU))
      have hw_bot : w ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hD_W1_disj hwD hwW1
      have hw_one : w = 1 := by
        simpa using hw_bot
      have hxU : x ∈ U := by
        have hx_eq : x = u := by
          simpa [hw_one] using hwu.symm
        simpa [hx_eq] using huU
      have hxMF : x ∈ MF := by
        simpa [hMFeq] using hxSigma
      exact Subgroup.disjoint_def.mp hMF_U_disj hxMF hxU
  have hUSigmaNormal : section10NormalIn (U ⊔ section10Msigma M) M := by
    have hnormD : section10NormalIn (ambientDerivedSubgroup M) M :=
      section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)
    simpa [← hD_eq_USigma] using hnormD
  have hUnormal : section10NormalIn U (W1 ⊔ U) := by
    refine ⟨le_sup_right, ?_⟩
    simpa using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := U) hW1_norm_U)
  exact ⟨hcompW1USigma, hcompSigmaW1U, hUSigmaNormal, hUnormal⟩

/-- The source Type-P centralizer field makes the action of `W1` on `U`
regular: a nontrivial element of `W1` has centralizer `W2` in `M'`, and
`W2 ≤ MF` is disjoint from the complement `U`. -/
public theorem source_typeP_W1_actsRegularlyOn_U
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    section14ActsRegularlyOn W1 U := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD,
      _hUnil, hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2leInf, _hW2cyc, _hW2ne, hCent, _hNorm⟩
  rcases hDercomp with ⟨_hMFD, hUD, _hD_eq, hMF_U_disj⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1norm hw)).1
  · intro x hxW1 hxne
    apply le_antisymm
    · intro y hy
      have hyU : y ∈ U := hy.1
      have hyD : y ∈ ambientDerivedSubgroup M := hUD hyU
      have hycent : y ∈ Subgroup.centralizer ({x} : Set G) := hy.2
      have hyDcent :
          y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := ⟨hyD, hycent⟩
      have hyW2 : y ∈ W2 := by
        simpa [hCent x hxW1 hxne] using hyDcent
      have hyMF : y ∈ MF := (hW2leInf hyW2).1
      have hybot : y ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hMF_U_disj hyMF hyU
      simpa using hybot
    · exact bot_le

/-- Once `W1` is known to be the Hall `kappa(M)` subgroup, the source
complement decompositions force the same source `U` to be Hall away from
`kappa(M) ∪ sigma(M)`.

The proof first views `E = W1 ⊔ U` as the sigma-complement in `M`; then `U`
is the normal complement to the Hall `kappa(M)` subgroup inside `E`. -/
private theorem source_typeP_U_hall_from_W1_kappa_hall
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2)
    (hW1Hallκ : section12HallSubgroupIn (section14KappaPrimes M) W1 M) :
    section12HallSubgroupIn ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
      U M := by
  classical
  let E : Subgroup G := W1 ⊔ U
  rcases source_typeP_W1_KUData_structural_fields hMFeq hsourceP with
    ⟨hcompW1USigma, hcompSigmaW1U, _hUSigmaNormal, hUnormal⟩
  have hEM : E ≤ M := by
    simpa [E] using hcompSigmaW1U.2.1
  have hUE : U ≤ E := by
    intro x hx
    exact (show x ∈ W1 ⊔ U from (le_sup_right : U ≤ W1 ⊔ U) hx)
  have hW1E : W1 ≤ E := by
    intro x hx
    exact (show x ∈ W1 ⊔ U from (le_sup_left : W1 ≤ W1 ⊔ U) hx)
  have hW1HallE : section12HallSubgroupIn (section14KappaPrimes M) W1 E :=
    section12HallSubgroupIn_of_le_overgroup_for_final hW1Hallκ hW1E hEM
  have hW1Udisj : Disjoint W1 U := by
    rw [Subgroup.disjoint_def]
    intro x hxW1 hxU
    exact Subgroup.disjoint_def.mp hcompW1USigma.2.2.2 hxW1
      (show x ∈ U ⊔ section10Msigma M from
        (le_sup_left : U ≤ U ⊔ section10Msigma M) hxU)
  have hcompW1U : section12ComplementIn E W1 U := by
    refine ⟨hW1E, hUE, ?_, hW1Udisj⟩
    simp [E]
  have hUnormalE : section10NormalIn U E := by
    simpa [E] using hUnormal
  have hUHallE : section12HallSubgroupIn (section14KappaPrimes M)ᶜ U E :=
    section12ComplementIn_right_isHall_compl_of_left_hall_for_final
      hcompW1U hUnormalE hW1HallE
  have hEHallM : section12HallSubgroupIn (section10SigmaPrimes M)ᶜ E M := by
    refine ⟨hEM, ?_⟩
    simpa [E] using
      (section12_msigma_complement_isHall_sigma_compl (G := G) hM hcompSigmaW1U)
  have hUM : U ≤ M := hUE.trans hEM
  refine ⟨hUM, ?_⟩
  refine isHallSubgroup_of (G := M)
    (π := ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ))
    (H := U.subgroupOf M) ?_ ?_
  · intro p hpUsub
    have hcardUM : Nat.card (U.subgroupOf M) = Nat.card U :=
      natCard_subgroupOf_eq U M hUM
    have hcardUMF : Fintype.card (U.subgroupOf M) = Fintype.card U := by
      simpa [Nat.card_eq_fintype_card] using hcardUM
    have hpU : p.val ∣ Fintype.card U := by
      simpa [hcardUMF] using hpUsub
    have hcardUE : Nat.card (U.subgroupOf E) = Nat.card U :=
      natCard_subgroupOf_eq U E hUE
    have hcardUEF : Fintype.card (U.subgroupOf E) = Fintype.card U := by
      simpa [Nat.card_eq_fintype_card] using hcardUE
    have hpUE : p.val ∣ Fintype.card (U.subgroupOf E) := by
      simpa [hcardUEF] using hpU
    have hpκc : p ∈ (section14KappaPrimes M)ᶜ :=
      hUHallE.2.p_in_pi_of_p_dvd_card p (by
        simpa [Nat.card_eq_fintype_card] using hpUE)
    have hpUNat : p.val ∣ Nat.card U := by
      simpa [Nat.card_eq_fintype_card] using hpU
    have hpE : p.val ∣ Nat.card E := hpUNat.trans (Subgroup.card_dvd_of_le hUE)
    have hcardEM : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hEM
    have hcardEMF : Fintype.card (E.subgroupOf M) = Fintype.card E := by
      simpa [Nat.card_eq_fintype_card] using hcardEM
    have hpEM : p.val ∣ Fintype.card (E.subgroupOf M) := by
      simpa [hcardEMF] using hpE
    have hpσc : p ∈ (section10SigmaPrimes M)ᶜ :=
      hEHallM.2.p_in_pi_of_p_dvd_card p (by
        simpa [Nat.card_eq_fintype_card] using hpEM)
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hpκσ
    exact hpκσ.elim hpκc hpσc
  · intro p hpπ hpidx
    have hpκc : p ∈ (section14KappaPrimes M)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hpκ
      exact hpπ (Or.inl hpκ)
    have hpσc : p ∈ (section10SigmaPrimes M)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hpσ
      exact hpπ (Or.inr hpσ)
    change p.val ∣ U.relIndex M at hpidx
    have hmul : U.relIndex E * E.relIndex M = U.relIndex M :=
      Subgroup.relIndex_mul_relIndex U E M hUE hEM
    have hprod : p.val ∣ U.relIndex E * E.relIndex M := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidxUE | hpidxEM
    · exact (hUHallE.2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxUE)) hpκc
    · exact (hEHallM.2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxEM)) hpσc

/-- A prime-order subgroup of the source Type-P complement `W1` has prime in
`τ₁(M) ∪ τ₃(M)`. -/
private theorem source_typeP_tau13_of_W1_prime_for_final
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
  classical
  letI : IsMinCE G := hmin
  rcases hsourceP with
    ⟨_hMFsource, hW1cyc, _hW1ne, hW1Hall, hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, hW1HallSub⟩
  rcases hX with ⟨hXW1, hXcard⟩
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpM : p.val ∣ Nat.card M := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXM)
  have hpW1 : p.val ∣ Nat.card W1 := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXW1)
  have hpW1π : p ∈ subgroupPrimeSet W1 := by
    simpa [subgroupPrimeSet] using hpW1
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hCompLocal : (W1.subgroupOf M).IsComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := ambientDerivedSubgroup M) (K := W1) hMcomp
  have hpNotSigma : p ∉ section10SigmaPrimes M := by
    intro hpSigma
    have hSigmaHallM :
        IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      (theorem_10_2_b (G := G) hM).2
    have hpSigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hprod :
          (section10MsigmaSubgroup M).index * Nat.card (section10MsigmaSubgroup M) =
            Nat.card M :=
        Subgroup.index_mul_card (H := section10MsigmaSubgroup M)
      have hprodF :
          (section10MsigmaSubgroup M).index * Fintype.card (section10MsigmaSubgroup M) =
            Fintype.card M := by
        simpa [Nat.card_eq_fintype_card] using hprod
      have hpProd :
          p.val ∣ (section10MsigmaSubgroup M).index *
              Fintype.card (section10MsigmaSubgroup M) := by
        simpa [hprodF] using hpM
      by_contra hpNotCard
      have hpNotIndex : ¬ p.val ∣ (section10MsigmaSubgroup M).index :=
        fun hpidx => (hSigmaHallM.p_in_pi_of_p_dvd_index p hpidx) hpSigma
      exact (Nat.Prime.not_dvd_mul p.property hpNotIndex hpNotCard) (by
        simpa [Nat.card_eq_fintype_card] using hpProd)
    have hMsigmaLeM : section10Msigma M ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hpSigmaSubgroupOf :
        p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
      simpa [section12Msigma_subgroupOf_eq (G := G) (M := M)] using hpSigmaSub
    have hpSigmaAmb : p.val ∣ Nat.card (section10Msigma M) := by
      have hcard :
          Nat.card ((section10Msigma M).subgroupOf M) = Nat.card (section10Msigma M) :=
        natCard_subgroupOf_eq (section10Msigma M) M hMsigmaLeM
      have hcardF :
          Fintype.card ((section10Msigma M).subgroupOf M) =
            Fintype.card (section10Msigma M) := by
        simpa [Nat.card_eq_fintype_card] using hcard
      simpa [hcardF] using hpSigmaSubgroupOf
    have hMsigmaLeDer : section10Msigma M ≤ ambientDerivedSubgroup M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨y, (theorem_10_2_c (G := G) hM).2 hy, rfl⟩
    have hpDcard : p.val ∣ Nat.card (ambientDerivedSubgroup M) :=
      hpSigmaAmb.trans (Subgroup.card_dvd_of_le hMsigmaLeDer)
    have hDleM : ambientDerivedSubgroup M ≤ M :=
      section12_ambientDerivedSubgroup_le (G := G) (E := M)
    have hpDsub : p.val ∣ Nat.card ((ambientDerivedSubgroup M).subgroupOf M) := by
      have hcard :
          Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
            Nat.card (ambientDerivedSubgroup M) :=
        natCard_subgroupOf_eq (ambientDerivedSubgroup M) M hDleM
      have hcardF :
          Fintype.card ((ambientDerivedSubgroup M).subgroupOf M) =
            Fintype.card (ambientDerivedSubgroup M) := by
        simpa [Nat.card_eq_fintype_card] using hcard
      simpa [hcardF] using hpDcard
    have hpW1idx : p.val ∣ (W1.subgroupOf M).index := by
      simpa [hCompLocal.symm.index_eq_card] using hpDsub
    exact (hW1HallSub.p_in_pi_of_p_dvd_index p hpW1idx) hpW1π
  have hW1subCyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.2 hW1cyc
  have hRankLe : primeRank p.val M ≤ 1 :=
    primeRank_le_one_of_cyclic_hall_subgroup_for_final
      (R := M) (π := subgroupPrimeSet W1) (K := W1.subgroupOf M)
      hW1HallSub hpW1π hW1subCyclic
  have hRankPos : 0 < primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hRank : primeRank p.val M = 1 := by omega
  by_cases hpDer : p ∈ subgroupPrimeSet (derivedSubgroup M)
  · exact Or.inr (by simpa [section12Tau3Primes] using ⟨hpNotSigma, hpDer, hRank⟩)
  · exact Or.inl (by simpa [section12Tau1Primes] using ⟨hpNotSigma, hpDer, hRank⟩)

/-- The source Type-P centralizer field gives a nontrivial centralizer in
`M_sigma` for every prime-order subgroup of `W1`, once `MF = M_sigma`. -/
private theorem source_typeP_msigma_centralizer_ne_bot_of_W1_prime_for_final
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
  classical
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2leInf, _hW2cyc, hW2ne, hCent, _hNorm⟩
  rcases hX with ⟨hXW1, _hXcard⟩
  haveI : Nontrivial W2 := (Subgroup.nontrivial_iff_ne_bot W2).2 hW2ne
  obtain ⟨yW2, hyW2ne⟩ := exists_ne (1 : W2)
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  have hyMsigma : y ∈ section10Msigma M := by
    have hyMF : y ∈ MF := (hW2leInf hyW2).1
    simpa [hMFeq] using hyMF
  have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hyMsigma, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hzX
    by_cases hz : z = 1
    · subst hz
      simp
    · have hzW1 : z ∈ W1 := hXW1 hzX
      have hyCentZ : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) z := by
        simpa [hCent z hzW1 hz] using hyW2
      have hcomm : Commute y z :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentZ.2
      exact hcomm.eq.symm
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨y, hyCentX⟩, ?_⟩
  intro hybot
  exact hyne (by simpa using congrArg Subtype.val hybot)

/-- Source Type-P data with `MF = M_sigma` places the maximal subgroup in
Section 14's family `𝓜_P`. -/
private theorem source_typeP_MFamilyP_of_msigma_eq_for_final
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    M ∈ section14MFamilyP G := by
  classical
  have hsourceP' : Section8.typePDefinitionData M MF U W1 W2 := hsourceP
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, hW1ne, hW1Hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, _hW1HallSub⟩
  rcases section12_exists_primeOrderSubgroup_of_ne_bot_for_final
      (G := G) hW1ne with
    ⟨X, hXprime⟩
  rcases hXprime with ⟨hXW1, p, hXcard⟩
  have hXprimeW1 : X ∈ section10PrimeOrderSubgroupsIn p W1 := by
    exact ⟨hXW1, hXcard⟩
  have hTau13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
    source_typeP_tau13_of_W1_prime_for_final
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hmin hM hsourceP' hXprimeW1
  have hCent :
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ :=
    source_typeP_msigma_centralizer_ne_bot_of_W1_prime_for_final
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hMFeq hsourceP' hXprimeW1
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpκ : p ∈ section14KappaPrimes M := by
    exact ⟨hTau13, X, ⟨hXM, hXcard⟩, hCent⟩
  exact ⟨hM, ⟨p, hpκ⟩⟩

/-- The remaining source-specific field needed to upgrade the source Type-P
pair `(W1, U)` to a Section 16 `KUData` package after `MF = M_sigma` is known.

The structural complement and normality fields are handled separately by
`source_typeP_W1_KUData_structural_fields`, the regular action is handled
by `source_typeP_W1_actsRegularlyOn_U`, and the `U` Hall-away field follows
from `source_typeP_U_hall_from_W1_kappa_hall` once this core supplies the
source/BG identification of `W1` as the Hall `kappa(M)` subgroup. -/
private theorem source_typeP_W1_KUData_hard_fields_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup M MF)
    (_hUne : U ≠ ⊥)
    (_hUnotσ : ¬ U ≤ section10Msigma M)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    section12HallSubgroupIn (section14KappaPrimes M) W1 M := by
  classical
  letI : IsMinCE G := hmin
  have hMP : M ∈ section14MFamilyP G :=
    source_typeP_MFamilyP_of_msigma_eq_for_final hmin hM hMFeq hsourceP
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U0, hKU⟩
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M := hKU.1
  have hKcomp : section12ComplementIn M K (ambientDerivedSubgroup M) :=
    theorem_14_7_h (G := G) (M := M) (K := K) hMP hKHall
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hcard : Nat.card W1 = Nat.card K :=
    natCard_eq_of_section12ComplementIn_same_normal_left_for_final
      (G := G) (M := M) (D := ambientDerivedSubgroup M) (H := W1) (K := K)
      hDnormal hMcomp hKcomp
  exact section12HallSubgroupIn_of_natCard_eq_for_final hKHall hMcomp.2.1 hcard

/-- Source Type-P data in the non-`M_sigma` branch supplies some Section 16
`KUData` complement for the same source subgroup `U`.

This is the exact remaining source/BG bridge needed for the Type-P T6 branch;
the final all-Type-I exclusion does not require identifying the source pair
`(W1, U)` with a prescribed Proposition 14.2(a) pair. -/
private theorem source_typeP_exists_KUData_of_not_le_msigma_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∃ K : Subgroup G, section16KUData M K U := by
  have hMFeq : MF = section10Msigma M :=
    source_typeP_MF_eq_msigma_of_not_le_msigma hmin hM hMF hUnotσ hsourceP
  have hW1Hallκ : section12HallSubgroupIn (section14KappaPrimes M) W1 M :=
    source_typeP_W1_KUData_hard_fields_core
      hmin hM hMF hUne hUnotσ hMFeq hsourceP
  have hUHall : section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M :=
    letI : IsMinCE G := hmin
    source_typeP_U_hall_from_W1_kappa_hall hM hMFeq hsourceP hW1Hallκ
  rcases source_typeP_W1_KUData_structural_fields hMFeq hsourceP with
    ⟨hcompW1USigma, hcompSigmaW1U, hUSigmaNormal, hUnormal⟩
  have hregular : section14ActsRegularlyOn W1 U :=
    source_typeP_W1_actsRegularlyOn_U hsourceP
  exact ⟨W1, hW1Hallκ, hcompW1USigma, hcompSigmaW1U, hUHall, hregular,
    hUSigmaNormal, hUnormal⟩

/-- The BG T6 centralizer alternative for source Type-P data in the
non-`M_sigma` branch, reduced to the exact `KUData`-existence bridge. -/
private theorem source_typeP_T6_of_not_le_msigma_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  letI : IsMinCE G := hmin
  rcases source_typeP_exists_KUData_of_not_le_msigma_core
      hmin hM hMF hUne hUnotσ hsourceP with
    ⟨K, hKU⟩
  exact section16_typeCommon_T6_of_KUData_ne_bot
    (G := G) (M := M) (MF := MF) (K := K) (U := U) hM hMF hKU hUne

/-- The remaining nontrivial-`U` BG T6 centralizer condition needed to turn
source Type-P data into BG `section16TypeCommon` data. If the source
complement lies in `M_sigma`, Section 16 fusion control gives T6 directly;
otherwise the remaining source debt is the direct non-`M_sigma` T6 transfer. -/
private theorem source_typeP_T6_of_U_ne_bot_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  letI : IsMinCE G := hmin
  by_cases hUσ : U ≤ section10Msigma M
  · rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, U0, hKU15⟩
    have hKU : section16KUData M K U0 := by
      simpa [section16KUData] using hKU15
    exact section16_typeCommon_T6_of_le_msigma
      (G := G) (M := M) (MF := MF) (K := K) (U := U0) (V := U)
      hM hMF hKU hUσ
  · exact source_typeP_T6_of_not_le_msigma_core hmin hM hMF hUne hUσ hsourceP

/-- The missing BG T6 centralizer condition needed to turn source Type-P data
into BG `section16TypeCommon` data. The trivial-`U` case is closed locally, so
the remaining source debt is the nontrivial-`U` core. -/
private theorem source_typeP_T6_for_not_typeI_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  by_cases hUbot : U = ⊥
  · exact source_typeP_T6_of_U_eq_bot hUbot
  · exact source_typeP_T6_of_U_ne_bot_core hmin hM hMF hUbot hsourceP


private theorem section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    {U' W1' W2' : Subgroup G}
    (_hP : Section8.typePDefinitionData Smax P U' W1' W2') :
    theorem_13_2_typeCommonT6FusionData Smax P U' := by
  have hMin :
      IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  haveI : IsMinCE G := hMin
  rcases hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      _hStypes, _hTtypes, _hclass⟩
  have hself : Subgroup.normalizer (Smax : Set G) = Smax :=
    section13_maximal_normalizer_eq_self_of_isMinCE hSmax
  have hT6 : theorem_13_2_typeCommonT6Data Smax P U' :=
    source_typeP_T6_for_not_typeI_core hMin hSmax _hP.1 _hP
  exact ⟨hSmax, hself, hT6⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6FusionCoreData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_typeCommonT6FusionCoreData Smax P U := by
  have hsourceOrig := _hsource
  rcases _hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases
    section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceOrig hptypeS with
    ⟨_hSmax, hself, hfusion⟩
  exact ⟨hself, hfusion⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6FusionData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_typeCommonT6FusionData Smax P U := by
  rcases
    section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6FusionCoreData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource with
    ⟨hself, hfusion⟩
  rcases hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      _hStypes, _hTtypes, _hclass⟩
  exact ⟨hSmax, hself, hfusion⟩

private theorem section13_typePData_of_typePDefinitionData_T6
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePDefinitionData M MF U W1 W2)
    (hT6 :
      ∀ A0 A1 : Subgroup G,
        section16PrimeOrderSubgroupOf A0 U →
          section16PrimeOrderSubgroupOf A1 U →
            section16ConjugateSubgroupsIn ⊤ A0 A1 →
              ¬ section16ConjugateSubgroupsIn M A0 A1 →
                subgroupCentralizerIn MF A0 = ⊥ ∨
                  subgroupCentralizerIn MF A1 = ⊥) :
    Section8.typePData M MF U W1 W2 := by
  rcases htype with
    ⟨hMF, hW1cyc, _hW1ne, hW1Hall, hMcomp, _hUleDer, hUnil,
      hW1norm, hDerComp, hMFnotcyc, hsecond, hfitting, hfittingle,
      hW2le, hW2cyc, hW2ne, hcentralizer, hnormHat⟩
  refine ⟨hMF, ?_⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup M) M :=
    section12_normalIn_ambientDerivedSubgroup
  have hHallD : section16HallSubgroupOf (ambientDerivedSubgroup M) M :=
    section13_complementIn_left_hallSubgroupOf_of_right_hallSubgroupOf
      hMcomp hDer_norm hW1Hall
  have hcompLocal : (W1.subgroupOf M).IsComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) :=
    section13_complementIn_of_normal_isComplement' hMcomp hDer_norm
  have hW1card : Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := by
    have hcardLocal : Fintype.card (W1.subgroupOf M) = Fintype.card W1 := by
      simpa [Nat.card_eq_fintype_card] using
        (section12_card_subgroupOf_eq hMcomp.2.1)
    have hrel : (ambientDerivedSubgroup M).relIndex M = Nat.card W1 := by
      simpa [Subgroup.relIndex, Nat.card_eq_fintype_card, hcardLocal] using
        hcompLocal.index_eq_card
    exact hrel.symm
  dsimp [section16TypeCommon]
  exact ⟨hHallD, hDerComp.1, hDerComp, hUnil, hW1norm, hW1cyc, hW1card,
    hMFnotcyc, hsecond, hfitting.symm, hfittingle, hW2le.trans inf_le_left,
    hW2ne, hW2cyc, hcentralizer, hnormHat,
    ⟨hT6, hW2le.trans inf_le_right⟩⟩

private theorem section13_section16TypeIII_of_source_typeIII_with_fusionData
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : Section8.typeIIIDefinitionData M MF)
    (hFusion : ∀ {U W1 W2 : Subgroup G},
      Section8.typePDefinitionData M MF U W1 W2 →
        theorem_13_2_typeCommonT6FusionData M MF U) :
    section16TypeIII M MF := by
  rcases h with ⟨U, W1, W2, hP, hExtra, hcomm, hnorm⟩
  have hT6 :=
    section13_typeCommonT6_of_fusionData (hFusion hP)
  have hPData : Section8.typePData M MF U W1 W2 :=
    section13_typePData_of_typePDefinitionData_T6 hP hT6
  exact ⟨U, W1, W2, hPData.2,
    section13_section16TypeIIToIVExtra_of_sourceCondition hExtra, hcomm,
    hnorm⟩

private theorem section13_section16TypeIV_of_source_typeIV_with_fusionData
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : Section8.typeIVDefinitionData M MF)
    (hFusion : ∀ {U W1 W2 : Subgroup G},
      Section8.typePDefinitionData M MF U W1 W2 →
        theorem_13_2_typeCommonT6FusionData M MF U) :
    section16TypeIV M MF := by
  rcases h with ⟨U, W1, W2, hP, hExtra, hncomm, hnorm⟩
  have hT6 :=
    section13_typeCommonT6_of_fusionData (hFusion hP)
  have hPData : Section8.typePData M MF U W1 W2 :=
    section13_typePData_of_typePDefinitionData_T6 hP hT6
  exact ⟨U, W1, W2, hPData.2,
    section13_section16TypeIIToIVExtra_of_sourceCondition hExtra, hncomm,
    hnorm⟩


private theorem section13_normalizer_le_of_unique_maximal_centralizer
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {A : Set G}
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hSelfNorm : Subgroup.normalizer (M : Set G) = M)
    (huniq :
      section9MaximalSubgroupsContaining (Subgroup.centralizer A) = {M}) :
    Subgroup.normalizer A ≤ M := by
  intro g hgA
  have hC_le_M : Subgroup.centralizer A ≤ M := by
    have hMmem :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer A) := by
      simp [huniq]
    exact hMmem.2
  have hMconj_mem :
      M.conjBy g ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer A) := by
    refine ⟨section10_maximal_conjBy (G := G) hMmax g, ?_⟩
    intro x hxC
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, hC_le_M ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro a haA
    have hga : g * a * g⁻¹ ∈ A :=
      (hgA a).1 haA
    have hcomm := hxC (g * a * g⁻¹) hga
    have hcomm' := congrArg (fun t : G => g⁻¹ * t * g) hcomm
    simpa [mul_assoc] using hcomm'
  have hMconj_eq : M.conjBy g = M := by
    have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
      simpa [huniq] using hMconj_mem
    simpa using hsingle
  have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
    section10_mem_normalizer_of_conjBy_eq (G := G) hMconj_eq
  simpa [hSelfNorm] using hgNormM


private theorem section13_typeII_theorem_8_12_conclusion
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 U1 U0 : Subgroup G}
    (hMin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    {Ms : Subgroup G}
    (hMs : Section8.msChoiceSource M MF Ms)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hcond : Section8.typeIIToIVSourceCondition M U W1)
    (hcomm : IsMulCommutative U)
    (hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    Section8.theorem_8_12_source_conclusion M MF U
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF)
      (Section8.a1Set MF) := by
  classical
  haveI : IsMinCE G := hMin
  let Abook : Set G := Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF
  let A0book : Set G :=
    Abook ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)
  have hII : Section8.typeIIDefinitionData M MF :=
    ⟨U, W1, W2, U1, U0, hP, hcond, hcomm, hnorm, hF⟩
  have hMsEq : Ms = MF := by
    rcases hMs with hChoiceI | hrest
    · exact False.elim (hChoiceI.2.1 hII)
    rcases hrest with hChoiceII | hrest
    · exact hChoiceII.2.2.2.2.2
    rcases hrest with hChoiceIII | hrest
    · exact False.elim (hChoiceIII.2.1 hII)
    rcases hrest with hChoiceIV | hChoiceV
    · exact False.elim (hChoiceIV.2.1 hII)
    · exact False.elim (hChoiceV.2.1 hII)
  have hNoLate :
      ¬ (Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) := by
    intro hlate
    rcases hMs with hChoiceI | hrest
    · exact hChoiceI.2.1 hII
    rcases hrest with hChoiceII | hrest
    · rcases hlate with hIII | hlate
      · exact hChoiceII.2.2.1 hIII
      rcases hlate with hIV | hV
      · exact hChoiceII.2.2.2.1 hIV
      · exact hChoiceII.2.2.2.2.1 hV
    rcases hrest with hChoiceIII | hrest
    · exact hChoiceIII.2.1 hII
    rcases hrest with hChoiceIV | hChoiceV
    · exact hChoiceIV.2.1 hII
    · exact hChoiceV.2.1 hII
  have hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book
        (Section8.a1Set MF) := by
    have hA1 : Section8.a1Set MF = Section8.a1Set Ms := by
      simp [hMsEq]
    have hAbook :
        Abook = Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms := by
      simp [Abook, hMsEq]
    refine ⟨hM, hP.1, hMs, hA1, Or.inr ?_⟩
    refine ⟨U, W1, W2, hP, Or.inl hII, hAbook, rfl, ?_⟩
    intro hlate
    exact False.elim (hNoLate hlate)
  have hSrc :
      Section8.theorem_8_12_source_data M MF U Ms Abook A0book
        (Section8.a1Set MF) := by
    refine ⟨hNotation, Or.inr ?_⟩
    exact ⟨⟨W1, W2, U1, U0, hP, hcond, hcomm, hnorm, hF⟩, rfl, rfl⟩
  have hConclusion :
      Section8.theorem_8_12_source_conclusion M MF U Abook (Section8.a1Set MF) :=
    Section8.theorem_8_12 M MF U Ms Abook A0book (Section8.a1Set MF) hMin hSrc
  simpa [Abook] using hConclusion


private theorem section13_typeII_fusionData_of_theorem_8_12
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 U1 U0 : Subgroup G}
    (hMin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    {Ms : Subgroup G}
    (hMs : Section8.msChoiceSource M MF Ms)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hcond : Section8.typeIIToIVSourceCondition M U W1)
    (hcomm : IsMulCommutative U)
    (hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    theorem_13_2_typeCommonT6FusionData M MF U := by
  classical
  haveI : IsMinCE G := hMin
  have hConclusion :=
    section13_typeII_theorem_8_12_conclusion
      hMin hM hMs hP hcond hcomm hnorm hF
  have hUnique :
      ∀ X : Set G, X.Nonempty →
        X ⊆ section16NonidentityElements (U : Set G) →
          section16CentralizerInSet MF X ≠ ⊥ →
            section9MaximalSubgroupsContaining (Subgroup.centralizer X) = {M} :=
    hConclusion.2.1
  have hself : Subgroup.normalizer (M : Set G) = M :=
    section13_maximal_normalizer_eq_self_of_isMinCE hM
  have hUniqueData :
      theorem_13_2_typeCommonT6FusionUniqueData M MF U := by
    refine ⟨hM, hself, ?_⟩
    intro X hXU hXne hCent
    have hSharpNonempty :
        (section16NonidentityElements (X : Set G)).Nonempty := by
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hXne with ⟨x, hxne⟩
      refine ⟨(x : G), ⟨x.property, ?_⟩⟩
      intro hx
      exact hxne (Subtype.ext hx)
    have hSharpU :
        section16NonidentityElements (X : Set G) ⊆
          section16NonidentityElements (U : Set G) := by
      intro x hx
      exact ⟨hXU hx.1, hx.2⟩
    have hCentSharp :
        section16CentralizerInSet MF (section16NonidentityElements (X : Set G)) ≠ ⊥ := by
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCent with ⟨yC, hyCne⟩
      let yCsharp :
          section16CentralizerInSet MF (section16NonidentityElements (X : Set G)) :=
        ⟨(yC : G), by
          constructor
          · exact yC.property.1
          · change (yC : G) ∈
              Subgroup.centralizer (section16NonidentityElements (X : Set G))
            have hyCentral : (yC : G) ∈ Subgroup.centralizer (X : Set G) :=
              yC.property.2
            rw [Subgroup.mem_centralizer_iff] at hyCentral ⊢
            intro x hx
            exact hyCentral x hx.1⟩
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yCsharp, ?_⟩
      intro hyOne
      exact hyCne (Subtype.ext (by
        simpa [yCsharp] using congrArg Subtype.val hyOne))
    have huniqSharp :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (section16NonidentityElements (X : Set G))) = {M} :=
      hUnique (section16NonidentityElements (X : Set G))
        hSharpNonempty hSharpU hCentSharp
    simpa [section13_centralizer_nonidentityElements_subgroup (G := G) X]
      using huniqSharp
  exact ⟨hM, hself, section13_typeCommonT6_of_fusionUniqueData hUniqueData⟩

private theorem section13_typeII_normalizer_le_of_theorem_8_12
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 U1 U0 : Subgroup G}
    (hMin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    {Ms : Subgroup G}
    (hMs : Section8.msChoiceSource M MF Ms)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hcond : Section8.typeIIToIVSourceCondition M U W1)
    (hcomm : IsMulCommutative U)
    (hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    ∀ A : Set G, A.Nonempty → A ⊆ ambientDerivedSubgroup M →
      A ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M := by
  classical
  haveI : IsMinCE G := hMin
  let Abook : Set G := Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF
  let A0book : Set G :=
    Abook ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)
  have hII : Section8.typeIIDefinitionData M MF :=
    ⟨U, W1, W2, U1, U0, hP, hcond, hcomm, hnorm, hF⟩
  have hMsEq : Ms = MF := by
    rcases hMs with hChoiceI | hrest
    · exact False.elim (hChoiceI.2.1 hII)
    rcases hrest with hChoiceII | hrest
    · exact hChoiceII.2.2.2.2.2
    rcases hrest with hChoiceIII | hrest
    · exact False.elim (hChoiceIII.2.1 hII)
    rcases hrest with hChoiceIV | hChoiceV
    · exact False.elim (hChoiceIV.2.1 hII)
    · exact False.elim (hChoiceV.2.1 hII)
  have hNoLate :
      ¬ (Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) := by
    intro hlate
    rcases hMs with hChoiceI | hrest
    · exact hChoiceI.2.1 hII
    rcases hrest with hChoiceII | hrest
    · rcases hlate with hIII | hlate
      · exact hChoiceII.2.2.1 hIII
      rcases hlate with hIV | hV
      · exact hChoiceII.2.2.2.1 hIV
      · exact hChoiceII.2.2.2.2.1 hV
    rcases hrest with hChoiceIII | hrest
    · exact hChoiceIII.2.1 hII
    rcases hrest with hChoiceIV | hChoiceV
    · exact hChoiceIV.2.1 hII
    · exact hChoiceV.2.1 hII
  have hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book
        (Section8.a1Set MF) := by
    have hA1 : Section8.a1Set MF = Section8.a1Set Ms := by
      simp [hMsEq]
    have hAbook :
        Abook = Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms := by
      simp [Abook, hMsEq]
    refine ⟨hM, hP.1, hMs, hA1, Or.inr ?_⟩
    refine ⟨U, W1, W2, hP, Or.inl hII, hAbook, rfl, ?_⟩
    intro hlate
    exact False.elim (hNoLate hlate)
  have hSrc :
      Section8.theorem_8_12_source_data M MF U Ms Abook A0book
        (Section8.a1Set MF) := by
    refine ⟨hNotation, Or.inr ?_⟩
    exact ⟨⟨W1, W2, U1, U0, hP, hcond, hcomm, hnorm, hF⟩, rfl, rfl⟩
  have hConclusion :
      Section8.theorem_8_12_source_conclusion M MF U Abook (Section8.a1Set MF) :=
    Section8.theorem_8_12 M MF U Ms Abook A0book (Section8.a1Set MF) hMin hSrc
  have hUnique :
      ∀ X : Set G, X.Nonempty →
        X ⊆ section16NonidentityElements (U : Set G) →
          section16CentralizerInSet MF X ≠ ⊥ →
            section9MaximalSubgroupsContaining (Subgroup.centralizer X) = {M} :=
    hConclusion.2.1
  have hSelf : Subgroup.normalizer (M : Set G) = M :=
    section13_maximal_normalizer_eq_self_of_isMinCE hM
  intro A hAne _hAD hAU hCent
  exact section13_normalizer_le_of_unique_maximal_centralizer hM hSelf
    (hUnique A hAne hAU hCent)

private def theorem_13_2_typeIISourceBGHardFields
    {G : Type u} [Group G] [Finite G]
    (M MF U : Subgroup G) : Prop :=
  groupRank U ≤ 2 ∧
    ∀ A : Set G, A.Nonempty → A ⊆ ambientDerivedSubgroup M →
      A ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M

private def theorem_13_2_typeIIRankSourceData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  IsMinCE G ∧ M ∈ section9MaximalSubgroups G ∧
    ∃ Ms : Subgroup G, Section8.msChoiceSource M MF Ms

private def theorem_13_2_typeIIRankChoiceData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  IsMinCE G ∧ ∃ Ms : Subgroup G, Section8.msChoiceSource M MF Ms

private def theorem_13_2_typeIIRankMsChoiceData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  ∃ Ms : Subgroup G, Section8.msChoiceSource M MF Ms

private theorem section13_theorem_13_2_typeIISourceBGRank_of_source
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 U1 U0 : Subgroup G}
    (hRankSource : theorem_13_2_typeIIRankSourceData M MF)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hcond : Section8.typeIIToIVSourceCondition M U W1)
    (hcomm : IsMulCommutative U)
    (hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    groupRank U ≤ 2 := by
  rcases hRankSource with ⟨hMin, hM, Ms, hMs⟩
  haveI : IsMinCE G := hMin
  exact Section8.theorem_8_12_typeII_groupRank_le_two_of_source
    (G := G) (M := M) (MF := MF) (U := U) (Ms := Ms)
    hM hP.1 hMs ⟨W1, W2, U1, U0, hP, hcond, hcomm, hnorm, hF⟩

private theorem section13_theorem_13_2_typeIIRankMsChoiceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hII : Section8.typeIIDefinitionData Smax P) :
    theorem_13_2_typeIIRankMsChoiceData Smax P := by
  rcases hsource with
    ⟨hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, _hMin⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  exact hChoice Smax P hSmax hptypeS.1 (Or.inr (Or.inl _hII))

private theorem section13_theorem_13_2_typeIIRankChoiceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hII : Section8.typeIIDefinitionData Smax P) :
    theorem_13_2_typeIIRankChoiceData Smax P := by
  exact ⟨
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_typeIIRankMsChoiceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource _hII⟩

private theorem section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hII : Section8.typeIIDefinitionData Smax P) :
    theorem_13_2_typeIIRankSourceData Smax P := by
  rcases section13_theorem_13_2_typeIIRankChoiceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource _hII with
    ⟨hMin, Ms, hMs⟩
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      _hStypes, _hTtypes, _hclass⟩
  exact ⟨hMin, hSmax, Ms, hMs⟩

private theorem section13_theorem_13_2_typeIISourceBGHardFields_of_source
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 U1 U0 : Subgroup G}
    (hRankSource : theorem_13_2_typeIIRankSourceData M MF)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hcond : Section8.typeIIToIVSourceCondition M U W1)
    (hcomm : IsMulCommutative U)
    (hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    theorem_13_2_typeIISourceBGHardFields M MF U := by
  rcases hRankSource with ⟨hMin, hM, Ms, hMs⟩
  exact ⟨section13_theorem_13_2_typeIISourceBGRank_of_source
      ⟨hMin, hM, Ms, hMs⟩ hP hcond hcomm hnorm hF,
    section13_typeII_normalizer_le_of_theorem_8_12
      hMin hM hMs hP hcond hcomm hnorm hF⟩

private theorem section13_section16TypeII_of_source_typeII_with_fusionData
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : Section8.typeIIDefinitionData M MF)
    (hRankSource : theorem_13_2_typeIIRankSourceData M MF) :
    section16TypeII M MF := by
  rcases h with ⟨U, W1, W2, U1, U0, hP, hExtra, hcomm, hnorm, hF⟩
  rcases hRankSource with ⟨hMin, hM, Ms, hMs⟩
  have hFusionData : theorem_13_2_typeCommonT6FusionData M MF U :=
    section13_typeII_fusionData_of_theorem_8_12
      hMin hM hMs hP hExtra hcomm hnorm hF
  have hT6 :=
    section13_typeCommonT6_of_fusionData hFusionData
  have hPData : Section8.typePData M MF U W1 W2 :=
    section13_typePData_of_typePDefinitionData_T6 hP hT6
  have hHard : theorem_13_2_typeIISourceBGHardFields M MF U :=
    section13_theorem_13_2_typeIISourceBGHardFields_of_source
      ⟨hMin, hM, Ms, hMs⟩ hP hExtra hcomm hnorm hF
  exact ⟨U, W1, W2, hPData.2,
    section13_section16TypeIIToIVExtra_of_sourceCondition hExtra, hcomm,
    hHard.1, hExtra.1, hnorm, hHard.2⟩

private theorem section13_typePDefinitionData_W1_card_eq_relIndex
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePDefinitionData M MF U W1 W2) :
    Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := by
  rcases htype with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hMFnotcyc, _hsecond, _hfitting,
      _hfittingle, _hW2le, _hW2cyc, _hW2ne, _hcentralizer,
      _hnormHat⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup M) M :=
    section12_normalIn_ambientDerivedSubgroup
  have hcompLocal : (W1.subgroupOf M).IsComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) :=
    section13_complementIn_of_normal_isComplement' hMcomp hDer_norm
  have hcardLocal : Fintype.card (W1.subgroupOf M) = Fintype.card W1 := by
    simpa [Nat.card_eq_fintype_card] using
      (section12_card_subgroupOf_eq hMcomp.2.1)
  have hrel : (ambientDerivedSubgroup M).relIndex M = Nat.card W1 := by
    simpa [Subgroup.relIndex, Nat.card_eq_fintype_card, hcardLocal] using
      hcompLocal.index_eq_card
  exact hrel.symm

private theorem section13_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 U' W1' W2' : Subgroup G}
    (hcur : Section8.typePDefinitionData M MF U W1 W2)
    (hbranch : Section8.typePDefinitionData M MF U' W1' W2')
    (hcond : Section8.typeIIToIVSourceCondition M U' W1') :
    Section8.typeIIToIVSourceCondition M U W1 := by
  have hW1_card : Nat.card W1 = (ambientDerivedSubgroup M).relIndex M :=
    section13_typePDefinitionData_W1_card_eq_relIndex hcur
  have hW1'_card : Nat.card W1' = (ambientDerivedSubgroup M).relIndex M :=
    section13_typePDefinitionData_W1_card_eq_relIndex hbranch
  rcases hcond with ⟨hU'ne, hW1'prime, hTI⟩
  refine ⟨?_, ?_, hTI⟩
  · intro hUbot
    rcases hcur with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, _hUnil,
        _hW1norm, hDerComp, _hMFnotcyc, _hsecond, _hfitting,
        _hfittingle, _hW2le, _hW2cyc, _hW2ne, _hcentralizer,
        _hnormHat⟩
    rcases hbranch with
      ⟨_hMF', _hW1cyc', _hW1ne', _hW1Hall', _hMcomp', _hU'leDer,
        _hUnil', _hW1norm', hDerComp', _hMFnotcyc', _hsecond',
        _hfitting', _hfittingle', _hW2le', _hW2cyc', _hW2ne',
        _hcentralizer', _hnormHat'⟩
    rcases hDerComp with ⟨_hMFleDer, _hUleDer', hDer_eq, _hMFUdisj⟩
    rcases hDerComp' with ⟨_hMFleDer', hU'leDer, _hDer_eq',
      hMFU'disj⟩
    have hDer_le_MF : ambientDerivedSubgroup M ≤ MF := by
      rw [hDer_eq, hUbot]
      simp
    have hU'leMF : U' ≤ MF := hU'leDer.trans hDer_le_MF
    have hU'leBot : U' ≤ (⊥ : Subgroup G) := by
      intro x hx
      exact (Subgroup.disjoint_def.mp hMFU'disj) (hU'leMF hx) hx
    exact hU'ne (le_bot_iff.mp hU'leBot)
  · rcases hW1'prime with ⟨r, hcardPrime⟩
    exact ⟨r, by
      calc
        Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := hW1_card
        _ = Nat.card W1' := hW1'_card.symm
        _ = r.val := hcardPrime⟩

private def theorem_13_2_case_9_7_hypothesis92BridgeData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 : Subgroup G) : Prop :=
  Section8.typePData Smax P U W1 W2 ∧
    Section8.typePDefinitionData Smax P U W1 W2 ∧
    (Section8.typeIIToIVSourceCondition Smax U W1 ∧
      (section16TypeII Smax P →
        IsMulCommutative U ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ Smax ∧
          ∃ U1 U0 : Subgroup G,
            Section8.typeFData (ambientDerivedSubgroup Smax) P U U1 U0) ∧
      (section16TypeIII Smax P →
        IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ Smax) ∧
      (section16TypeIV Smax P →
        ¬ IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ Smax)) ∧
    (section16TypeII Smax P ∨ section16TypeIII Smax P ∨
      section16TypeIV Smax P)

private def theorem_13_2_case_9_7_hypothesis92SourceCoreData
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 _ : Subgroup G) : Prop :=
  Section8.typeIIToIVSourceCondition M U W1 ∧
    (section16TypeII M MF →
      IsMulCommutative U ∧
        ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
        ∃ U1 U0 : Subgroup G,
          Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) ∧
    (section16TypeIII M MF →
      IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ M) ∧
    (section16TypeIV M MF →
      ¬ IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ M)

private def theorem_13_2_case_9_7_hypothesis92SourceImplicationsData
    {G : Type u} [Group G] [Finite G]
    (M MF U : Subgroup G) : Prop :=
  (section16TypeII M MF →
    IsMulCommutative U ∧
      ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
      ∃ U1 U0 : Subgroup G,
        Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0) ∧
    (section16TypeIII M MF →
      IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ M) ∧
    (section16TypeIV M MF →
      ¬ IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ M)

private theorem section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn Smax A0 A1 →
              subgroupCentralizerIn P A0 = ⊥ ∨ subgroupCentralizerIn P A1 = ⊥ := by
  exact section13_typeCommonT6_of_fusionData
    (section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6FusionData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource)

public theorem section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typePData Smax P U W1 W2 := by
  have hT6 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  rcases _hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  exact section13_typePData_of_typePDefinitionData_T6 hptypeS hT6

public theorem section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typeIIToIVSourceCondition Smax U W1 := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  rcases _hsource with
    ⟨hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, hMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      hStypes, _hTtypes, _hclass⟩
  rcases hStypes with hII | hrest
  · rcases hII with ⟨U', W1', W2', U1, U0, hP', hcond, _hUcomm,
      _hNormNotLe, _hF⟩
    exact section13_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
      hptypeS hP' hcond
  · rcases hrest with hIII | hrest
    · rcases hIII with ⟨U', W1', W2', hP', hcond, _hUcomm, _hNormLe⟩
      exact section13_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
        hptypeS hP' hcond
    · rcases hrest with hIV | hV
      · rcases hIV with ⟨U', W1', W2', hP', hcond, _hUncomm, _hNormLe⟩
        exact section13_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
          hptypeS hP' hcond
      · exact False.elim (Section10.theorem_10_10 ⟨Smax, P, hSmax, hMF, hV⟩)

private theorem section13_complement_isHall_compl_of_isHall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {K D : Subgroup R}
    (hKHall : IsHallSubgroup π K)
    (hcomp : K.IsComplement' D) :
    IsHallSubgroup πᶜ D := by
  classical
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := D) ?_ ?_
  · intro q hqD hqπ
    have hqKidx : q.val ∣ K.index := by
      simpa [hcomp.symm.index_eq_card] using hqD
    exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqDidx
    have hqK : q.val ∣ Nat.card K := by
      simpa [hcomp.index_eq_card] using hqDidx
    exact hqπc (hKHall.p_in_pi_of_p_dvd_card q hqK)

private theorem section13_eq_conjBy_of_subgroupOf_map_conj
    {G : Type u} [Group G] {D U V : Subgroup G}
    (hUD : U ≤ D) (hVD : V ≤ D) {d : D}
    (hconj :
      V.subgroupOf D =
        (U.subgroupOf D).map (MulAut.conj d).toMonoidHom) :
    V = U.conjBy (d : G) := by
  ext x
  constructor
  · intro hxV
    have hxloc : (⟨x, hVD hxV⟩ : D) ∈ V.subgroupOf D := by
      simpa [Subgroup.mem_subgroupOf] using hxV
    rw [hconj] at hxloc
    rcases Subgroup.mem_map.mp hxloc with ⟨y, hyUloc, hyx⟩
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf] using hyUloc
    exact Subgroup.mem_map.mpr ⟨(y : G), hyU, by
      have hyxG := congrArg Subtype.val hyx
      simpa [MulAut.conj_apply] using hyxG⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyU, hyx⟩
    have hyD : y ∈ D := hUD hyU
    have hxD : x ∈ D := by
      rw [← hyx]
      exact D.mul_mem (D.mul_mem d.property hyD) (D.inv_mem d.property)
    have hxloc : (⟨x, hxD⟩ : D) ∈ V.subgroupOf D := by
      rw [hconj]
      refine Subgroup.mem_map.mpr ⟨(⟨y, hyD⟩ : D), ?_, ?_⟩
      · simpa [Subgroup.mem_subgroupOf] using hyU
      · apply Subtype.ext
        simpa [MulAut.conj_apply] using hyx
    simpa [Subgroup.mem_subgroupOf] using hxloc

private theorem section13_hall_complement_in_ambientDerived_of_typeP_complement
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hptype : Section8.typePDefinitionData M MF U W1 W2) :
    IsHallSubgroup (subgroupPrimeSet MF)ᶜ
      (U.subgroupOf (ambientDerivedSubgroup M)) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hptype with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, hCompU, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hnormHat⟩
  have hMFHallM : section12HallSubgroupIn (subgroupPrimeSet MF) MF M :=
    ⟨Section12.section16MFSubgroup_le hMF,
      Section12.section16MFSubgroup_subgroupOf_isHall hMF⟩
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hMFHallD : section12HallSubgroupIn (subgroupPrimeSet MF) MF D :=
    section12HallSubgroupIn_of_le_overgroup_for_final
      hMFHallM (by simpa [D] using hCompU.1) hDleM
  have hMFnormD : section10NormalIn MF D := by
    simpa [D] using
      section13_mf_normalIn_ambientDerived_of_typeP
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
          _hW1norm, hCompU, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
          _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hnormHat⟩
  have hCompLocal :
      (MF.subgroupOf D).IsComplement' (U.subgroupOf D) := by
    exact (section13_complementIn_of_normal_isComplement'
      (G := G) (H := D) (K := MF) (L := U)
      (by simpa [D] using hCompU) hMFnormD).symm
  exact section13_complement_isHall_compl_of_isHall hMFHallD.2 hCompLocal

private theorem section13_exists_conj_eq_of_typeP_complements
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 V W1' W2' : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hU : Section8.typePDefinitionData M MF U W1 W2)
    (hV : Section8.typePDefinitionData M MF V W1' W2') :
    ∃ d : ambientDerivedSubgroup M, U = V.conjBy (d : G) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hUHallD :
      IsHallSubgroup (subgroupPrimeSet MF)ᶜ (U.subgroupOf D) := by
    simpa [D] using
      section13_hall_complement_in_ambientDerived_of_typeP_complement hU
  have hVHallD :
      IsHallSubgroup (subgroupPrimeSet MF)ᶜ (V.subgroupOf D) := by
    simpa [D] using
      section13_hall_complement_in_ambientDerived_of_typeP_complement hV
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDneTop : D ≠ ⊤ := by
    intro hDtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      exact hDleM (by simp [hDtop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvD : IsSolvable D :=
    IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDneTop)
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := D) hsolvD
      (π := (subgroupPrimeSet MF)ᶜ)
      (H₁ := V.subgroupOf D) (H₂ := U.subgroupOf D)
      hVHallD hUHallD with
    ⟨d, hd⟩
  have hUD : U ≤ D := by
    rcases hU with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
        _hW1norm, hCompU, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
        _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hnormHat⟩
    simpa [D] using hCompU.2.1
  have hVD : V ≤ D := by
    rcases hV with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
        _hW1norm, hCompV, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
        _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hnormHat⟩
    simpa [D] using hCompV.2.1
  exact ⟨d, section13_eq_conjBy_of_subgroupOf_map_conj
    (G := G) (D := D) (U := V) (V := U) hVD hUD hd⟩

private theorem section13_isMulCommutative_of_eq_conjBy
    {G : Type u} [Group G] {U V : Subgroup G} {d : G}
    (hEq : U = V.conjBy d) (hcomm : IsMulCommutative V) :
    IsMulCommutative U := by
  subst U
  rw [Subgroup.conjBy]
  exact Subgroup.map_isMulCommutative
    (f := (MulAut.conj d).toMonoidHom) (H := V)

private theorem section13_not_isMulCommutative_of_eq_conjBy
    {G : Type u} [Group G] {U V : Subgroup G} {d : G}
    (hEq : U = V.conjBy d) (hncomm : ¬ IsMulCommutative V) :
    ¬ IsMulCommutative U := by
  intro hcommU
  have hVeq : V = U.conjBy d⁻¹ := by
    rw [hEq]
    exact (Subgroup.conjBy_inv V d).symm
  exact hncomm (section13_isMulCommutative_of_eq_conjBy hVeq hcommU)

private theorem section13_normalizer_le_of_conjBy_eq
    {G : Type u} [Group G]
    {M U V : Subgroup G} {d : G}
    (hdM : d ∈ M)
    (hEq : V = U.conjBy d)
    (hNormV : Subgroup.normalizer (V : Set G) ≤ M) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  intro n hn
  let a : G := d * n * d⁻¹
  have hUn : U.conjBy n = U :=
    section11_conjBy_eq_of_mem_normalizer (G := G) hn
  have haNormV : a ∈ Subgroup.normalizer (V : Set G) := by
    apply section10_mem_normalizer_of_conjBy_eq (G := G)
    calc
      V.conjBy a = (U.conjBy d).conjBy a := by rw [hEq]
      _ = U.conjBy (a * d) := Subgroup.conjBy_conjBy U d a
      _ = U.conjBy (d * n) := by
        congr 1
        simp [a, mul_assoc]
      _ = (U.conjBy n).conjBy d :=
        (Subgroup.conjBy_conjBy U n d).symm
      _ = U.conjBy d := by rw [hUn]
      _ = V := hEq.symm
  have haM : a ∈ M := hNormV haNormV
  have hn_eq : n = d⁻¹ * a * d := by
    simp [a, mul_assoc]
  rw [hn_eq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hdM) haM) hdM

private theorem section13_not_normalizer_le_of_eq_conjBy
    {G : Type u} [Group G]
    {M U V : Subgroup G} {d : G}
    (hdM : d ∈ M)
    (hEq : U = V.conjBy d)
    (hNormV : ¬ Subgroup.normalizer (V : Set G) ≤ M) :
    ¬ Subgroup.normalizer (U : Set G) ≤ M := by
  intro hNormU
  exact hNormV (section13_normalizer_le_of_conjBy_eq hdM hEq hNormU)

private theorem section13_section12ComplementIn_conjBy
    {G : Type u} [Group G]
    {H K L : Subgroup G} (g : G)
    (hcomp : section12ComplementIn H K L) :
    section12ComplementIn (H.conjBy g) (K.conjBy g) (L.conjBy g) := by
  rcases hcomp with ⟨hKH, hLH, hH, hDis⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKH
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hLH
  · calc
      H.conjBy g = (K ⊔ L).conjBy g := by rw [hH]
      _ = K.conjBy g ⊔ L.conjBy g := by
        simpa [Subgroup.conjBy] using
          (Subgroup.map_sup K L (MulAut.conj g).toMonoidHom)
  · rw [disjoint_iff] at hDis ⊢
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxK, hxL⟩
      rcases Subgroup.mem_map.mp hxK with ⟨k, hkK, hkx⟩
      rcases Subgroup.mem_map.mp hxL with ⟨l, hlL, hlx⟩
      have hk_eq_l : k = l := by
        have hconj_eq : g * k * g⁻¹ = g * l * g⁻¹ := by
          simpa [MulAut.conj_apply] using hkx.trans hlx.symm
        have hback := congrArg (fun z : G => g⁻¹ * z * g) hconj_eq
        simpa [mul_assoc] using hback
      have hk_bot : k ∈ (⊥ : Subgroup G) := by
        have hk_inter : k ∈ K ⊓ L := ⟨hkK, by simpa [hk_eq_l] using hlL⟩
        simpa [hDis] using hk_inter
      have hk_one : k = 1 := by simpa using hk_bot
      rw [← hkx]
      simp [MulAut.conj_apply, hk_one]
    · intro x hx
      have hx_one : x = 1 := by simpa using hx
      simp [hx_one]

private theorem section13_section10NormalIn_conjBy
    {G : Type u} [Group G]
    {K L : Subgroup G} (g : G)
    (hNorm : section10NormalIn K L) :
    section10NormalIn (K.conjBy g) (L.conjBy g) := by
  rcases hNorm with ⟨hKL, hNormal⟩
  refine ⟨?_, ?_⟩
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKL
  · let eL : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
    have hsub :
        Subgroup.map eL.toMonoidHom (K.subgroupOf L) =
          (K.conjBy g).subgroupOf (L.conjBy g) := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
        change ((x : L.conjBy g) : G) ∈ K.conjBy g
        exact Subgroup.mem_map.mpr ⟨(k : L), hkK, by
          have hkxG := congrArg (fun y : L.conjBy g => (y : G)) hkx
          change g * ((k : L) : G) * g⁻¹ = (x : G) at hkxG
          exact hkxG⟩
      · intro hx
        change ((x : L.conjBy g) : G) ∈ K.conjBy g at hx
        rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
        have hkL : k ∈ L := hKL hkK
        refine Subgroup.mem_map.mpr ⟨(⟨k, hkL⟩ : L), ?_, ?_⟩
        · simpa [Subgroup.mem_subgroupOf] using hkK
        · apply Subtype.ext
          exact hkx
    have hmap := hNormal.map eL.toMonoidHom eL.surjective
    rwa [hsub] at hmap

private theorem section13_isFrobeniusGroupWithKernelComplement_map_mulEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) {K R : Subgroup A}
    (hFrob : IsFrobeniusGroupWithKernelComplement K R) :
    IsFrobeniusGroupWithKernelComplement
      (K.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  classical
  rcases hFrob with ⟨hKnorm, hComp, hDisj, hKne, hRne⟩
  have hKmap_ne : K.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hKne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := e.toMonoidHom) e.injective).1 hbot)
  have hRmap_ne : R.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hRne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := R) (f := e.toMonoidHom) e.injective).1 hbot)
  have hKmap_norm : (K.map e.toMonoidHom).Normal :=
    hKnorm.map e.toMonoidHom e.surjective
  have hCompMap :
      (K.map e.toMonoidHom).IsComplement' (R.map e.toMonoidHom) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxR
      rcases Subgroup.mem_map.mp hxK with ⟨k, hkK, hkx⟩
      rcases Subgroup.mem_map.mp hxR with ⟨r, hrR, hrx⟩
      have hkr : k = r := e.injective (hkx.trans hrx.symm)
      have hkbot : k ∈ (⊥ : Subgroup A) :=
        hComp.disjoint.le_bot ⟨hkK, by simpa [hkr] using hrR⟩
      have hxone : x = 1 := by
        rw [← hkx]
        simpa using congrArg e hkbot
      simp [hxone]
    · rw [Set.eq_univ_iff_forall]
      intro b
      let a : A := e.symm b
      rcases hComp.2 a with ⟨kr, hkr⟩
      rcases kr with ⟨k, r⟩
      rcases k with ⟨k, hkK⟩
      rcases r with ⟨r, hrR⟩
      refine ⟨e k, Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩,
        e r, Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩, ?_⟩
      calc
        e k * e r = e (k * r) := (e.map_mul k r).symm
        _ = e a := by
          have hkrA : k * r = a := by
            simpa using hkr
          rw [hkrA]
        _ = b := e.apply_symm_apply b
  refine (lemma_3_1 (K.map e.toMonoidHom) (R.map e.toMonoidHom)
    hKmap_ne hRmap_ne hKmap_norm hCompMap).mpr ?_
  intro x hxne
  rcases x.property with ⟨r, hrR, hrx⟩
  let rSub : R := ⟨r, hrR⟩
  have hrne : rSub ≠ 1 := by
    intro hrone
    apply hxne
    apply Subtype.ext
    rw [← hrx]
    have hrA : r = 1 := by
      exact congrArg (fun x : R => (x : A)) hrone
    simp [hrA]
  have hcentral :=
    (lemma_3_1 K R hKne hRne hKnorm hComp).mp
      ⟨hKnorm, hComp, hDisj, hKne, hRne⟩ rSub hrne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hyCent⟩
  rcases Subgroup.mem_map.mp hyK with ⟨k, hkK, hky⟩
  have hkCent : k ∈ elementCentralizerIn K (r : A) := by
    refine ⟨hkK, ?_⟩
    change k ∈ Subgroup.centralizer ({r} : Set A)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    have hcommB : y * (x : B) = (x : B) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyCent
    rw [← hky, ← hrx] at hcommB
    simpa using hcommB
  have hkbot : k ∈ (⊥ : Subgroup A) := by
    rw [← hcentral]
    exact hkCent
  have hkone : k = 1 := by
    simpa using hkbot
  rw [← hky, hkone]
  simp

private theorem section13_section12FrobeniusJoinWithKernel_conjBy
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G} (g : G)
    (hFrob : section12FrobeniusJoinWithKernel K R) :
    section12FrobeniusJoinWithKernel (K.conjBy g) (R.conjBy g) := by
  let S : Subgroup G := K ⊔ R
  let eS : S ≃* S.conjBy g := (MulAut.conj g).subgroupMap S
  have hFrobS :
      IsFrobeniusGroupWithKernelComplement
        (K.subgroupOf S) (R.subgroupOf S) := by
    simpa [section12FrobeniusJoinWithKernel, S] using hFrob
  have hmap :
      IsFrobeniusGroupWithKernelComplement
        ((K.subgroupOf S).map eS.toMonoidHom)
        ((R.subgroupOf S).map eS.toMonoidHom) :=
    section13_isFrobeniusGroupWithKernelComplement_map_mulEquiv
      (e := eS) hFrobS
  have hKmap :
      (K.subgroupOf S).map eS.toMonoidHom =
        (K.conjBy g).subgroupOf (S.conjBy g) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
      change ((x : S.conjBy g) : G) ∈ K.conjBy g
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(k : S), ?_, ?_⟩
      · exact hkK
      · change g * ((k : S) : G) * g⁻¹ = (x : G)
        have hkxG := congrArg Subtype.val hkx
        change g * ((k : S) : G) * g⁻¹ = (x : G) at hkxG
        exact hkxG
    · intro hx
      change ((x : S.conjBy g) : G) ∈ K.conjBy g at hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
      refine Subgroup.mem_map.mpr ⟨⟨k, ?_⟩, hkK, ?_⟩
      · exact (le_sup_left : K ≤ K ⊔ R) hkK
      · apply Subtype.ext
        change g * k * g⁻¹ = (x : G)
        exact hkx
  have hRmap :
      (R.subgroupOf S).map eS.toMonoidHom =
        (R.conjBy g).subgroupOf (S.conjBy g) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨r, hrR, hrx⟩
      change ((x : S.conjBy g) : G) ∈ R.conjBy g
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(r : S), ?_, ?_⟩
      · exact hrR
      · change g * ((r : S) : G) * g⁻¹ = (x : G)
        have hrxG := congrArg Subtype.val hrx
        change g * ((r : S) : G) * g⁻¹ = (x : G) at hrxG
        exact hrxG
    · intro hx
      change ((x : S.conjBy g) : G) ∈ R.conjBy g at hx
      rcases Subgroup.mem_map.mp hx with ⟨r, hrR, hrx⟩
      refine Subgroup.mem_map.mpr ⟨⟨r, ?_⟩, hrR, ?_⟩
      · exact (le_sup_right : R ≤ K ⊔ R) hrR
      · apply Subtype.ext
        change g * r * g⁻¹ = (x : G)
        exact hrx
  have hSconj : S.conjBy g = K.conjBy g ⊔ R.conjBy g := by
    simpa [S, Subgroup.conjBy] using
      (Subgroup.map_sup (f := (MulAut.conj g).toMonoidHom) K R)
  rw [section12FrobeniusJoinWithKernel]
  rw [← hSconj]
  rw [hKmap, hRmap] at hmap
  exact hmap

private theorem section13_typeFData_of_eq_conjBy
    {G : Type u} [Group G] [Finite G]
    {D MF U V U1 U0 : Subgroup G} {d : G}
    (hdD : d ∈ D)
    (hEq : U = V.conjBy d)
    (hF : Section8.typeFData D MF V U1 U0) :
    ∃ U1' U0' : Subgroup G, Section8.typeFData D MF U U1' U0' := by
  classical
  rcases hF with
    ⟨hSolv, hOdd, hMF, hMFpos, hMFlt, hVne, hComp, hU1le,
      hU1comm, hU1norm, hCent, hU0le, hExp, hFrob⟩
  refine ⟨U1.conjBy d, U0.conjBy d, ?_⟩
  have hDconj : D.conjBy d = D :=
    section11_conjBy_eq_of_mem_normalizer (H := D) (Subgroup.le_normalizer hdD)
  have hMFleD : MF ≤ D := Section12.section16MFSubgroup_le hMF
  have hdNormMF : d ∈ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleD).1
      (Section12.section16MFSubgroup_subgroupOf_normal hMF) hdD
  have hMFconj : MF.conjBy d = MF :=
    section11_conjBy_eq_of_mem_normalizer (H := MF) hdNormMF
  refine ⟨hSolv, hOdd, hMF, hMFpos, hMFlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hVdne : V.conjBy d ≠ ⊥ := section12_conjBy_ne_bot hVne d
    simpa [hEq] using hVdne
  · have hCompConj := section13_section12ComplementIn_conjBy (G := G) d hComp
    simpa [hDconj, hMFconj, hEq] using hCompConj
  · simpa [Subgroup.conjBy, hEq] using
      (Subgroup.map_mono (f := (MulAut.conj d).toMonoidHom) hU1le)
  · letI : IsMulCommutative U1 := hU1comm
    rw [Subgroup.conjBy]
    exact Subgroup.map_isMulCommutative
      (f := (MulAut.conj d).toMonoidHom) (H := U1)
  · have hNormConj := section13_section10NormalIn_conjBy (G := G) d hU1norm
    simpa [hEq] using hNormConj
  · intro x hxMF hxne z hz
    have hz' : z ∈ elementCentralizerIn (V.conjBy d) x := by
      simpa [hEq] using hz
    rcases hz' with ⟨hzVd, hzCent⟩
    have hdInvNormMF : d⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normalizer (MF : Set G)).inv_mem hdNormMF
    have hyMF : d⁻¹ * x * d ∈ MF := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hdInvNormMF x).1 hxMF
    have hyne : d⁻¹ * x * d ≠ 1 := by
      intro hy
      apply hxne
      calc
        x = d * (d⁻¹ * x * d) * d⁻¹ := by group
        _ = 1 := by simp [hy]
    have hzBackV : d⁻¹ * z * d ∈ V := by
      rcases Subgroup.mem_map.mp hzVd with ⟨v0, hv0, hv0z⟩
      rw [← hv0z]
      simpa [MulAut.conj_apply, mul_assoc] using hv0
    have hzBackCent :
        d⁻¹ * z * d ∈ Subgroup.centralizer ({d⁻¹ * x * d} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hzComm : z * x = x * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hzCent
      calc
        (d⁻¹ * z * d) * (d⁻¹ * x * d) =
            d⁻¹ * (z * x) * d := by group
        _ = d⁻¹ * (x * z) * d := by rw [hzComm]
        _ = (d⁻¹ * x * d) * (d⁻¹ * z * d) := by group
    have hzBackU1 : d⁻¹ * z * d ∈ U1 :=
      hCent (d⁻¹ * x * d) hyMF hyne ⟨hzBackV, hzBackCent⟩
    exact Subgroup.mem_map.mpr ⟨d⁻¹ * z * d, hzBackU1, by
      simp [MulAut.conj_apply, mul_assoc]⟩
  · simpa [Subgroup.conjBy, hEq] using
      (Subgroup.map_mono (f := (MulAut.conj d).toMonoidHom) hU0le)
  · have hU0exp :
        Monoid.exponent (U0.conjBy d) = Monoid.exponent U0 := by
      let eU0 : U0 ≃* U0.conjBy d := (MulAut.conj d).subgroupMap U0
      simpa using (Monoid.exponent_eq_of_mulEquiv eU0).symm
    have hVexp :
        Monoid.exponent (V.conjBy d) = Monoid.exponent V := by
      let eV : V ≃* V.conjBy d := (MulAut.conj d).subgroupMap V
      simpa using (Monoid.exponent_eq_of_mulEquiv eV).symm
    rw [hEq, hU0exp, hVexp, hExp]
  · have hFrobConj :=
      section13_section12FrobeniusJoinWithKernel_conjBy (G := G) d hFrob
    simpa [hMFconj] using hFrobConj

private theorem section13_theorem_13_2_case_9_7_hypothesis92SourceImplicationsData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_hypothesis92SourceImplicationsData Smax P U := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  rcases _hsource with
    ⟨hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, hMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      _hStypes, _hTtypes, _hclass⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hII
    rcases Section8.theorem_8_8_typeII_to_source_public
        (G := G) (M := Smax) (MF := P) hSmax hMF hII with
      ⟨U', W1', W2', U1', U0', hP', _hcond, hcomm', hnorm', hF'⟩
    rcases section13_exists_conj_eq_of_typeP_complements
        (G := G) (M := Smax) (MF := P) (U := U) (W1 := W1) (W2 := W2)
        (V := U') (W1' := W1') (W2' := W2') hSmax hptypeS hP' with
      ⟨d0, hUconj⟩
    have hdM : (d0 : G) ∈ Smax :=
      (section12_ambientDerivedSubgroup_le (G := G) (E := Smax)) d0.property
    rcases section13_typeFData_of_eq_conjBy
        (G := G) (D := ambientDerivedSubgroup Smax) (MF := P)
        (U := U) (V := U') (U1 := U1') (U0 := U0') (d := (d0 : G))
        d0.property hUconj hF' with
      ⟨U1, U0, hF⟩
    exact ⟨section13_isMulCommutative_of_eq_conjBy hUconj hcomm',
      section13_not_normalizer_le_of_eq_conjBy hdM hUconj hnorm',
      ⟨U1, U0, hF⟩⟩
  · intro hIII
    rcases Section8.theorem_8_8_typeIII_to_source_public
        (G := G) (M := Smax) (MF := P) hSmax hMF hIII with
      ⟨U', W1', W2', hP', _hcond, hcomm', hnorm'⟩
    rcases section13_exists_conj_eq_of_typeP_complements
        (G := G) (M := Smax) (MF := P) (U := U) (W1 := W1) (W2 := W2)
        (V := U') (W1' := W1') (W2' := W2') hSmax hptypeS hP' with
      ⟨d0, hUconj⟩
    have hdM : (d0 : G) ∈ Smax :=
      (section12_ambientDerivedSubgroup_le (G := G) (E := Smax)) d0.property
    have hU'conj : U' = U.conjBy (d0 : G)⁻¹ := by
      rw [hUconj]
      exact (Subgroup.conjBy_inv U' (d0 : G)).symm
    exact ⟨section13_isMulCommutative_of_eq_conjBy hUconj hcomm',
      section13_normalizer_le_of_conjBy_eq (Smax.inv_mem hdM) hU'conj hnorm'⟩
  · intro hIV
    rcases Section8.theorem_8_8_typeIV_to_source_public
        (G := G) (M := Smax) (MF := P) hSmax hMF hIV with
      ⟨U', W1', W2', hP', _hcond, hncomm', hnorm'⟩
    rcases section13_exists_conj_eq_of_typeP_complements
        (G := G) (M := Smax) (MF := P) (U := U) (W1 := W1) (W2 := W2)
        (V := U') (W1' := W1') (W2' := W2') hSmax hptypeS hP' with
      ⟨d0, hUconj⟩
    have hdM : (d0 : G) ∈ Smax :=
      (section12_ambientDerivedSubgroup_le (G := G) (E := Smax)) d0.property
    have hU'conj : U' = U.conjBy (d0 : G)⁻¹ := by
      rw [hUconj]
      exact (Subgroup.conjBy_inv U' (d0 : G)).symm
    exact ⟨section13_not_isMulCommutative_of_eq_conjBy hUconj hncomm',
      section13_normalizer_le_of_conjBy_eq (Smax.inv_mem hdM) hU'conj hnorm'⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis92SourceCoreData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_hypothesis92SourceCoreData Smax P U W1 W2 := by
  rcases
    section13_theorem_13_2_case_9_7_hypothesis92SourceImplicationsData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    ⟨hII, hIII, hIV⟩
  exact ⟨
    section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    hII, hIII, hIV⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis92BGTypes_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    section16TypeII Smax P ∨ section16TypeIII Smax P ∨
      section16TypeIV Smax P := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  have hsourceOrig := _hsource
  have hFusion : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource hP
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, hMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      hStypes, _hTtypes, _hclass⟩
  rcases hStypes with hII | hrest
  · have hRankSource :=
      section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig hII
    exact Or.inl
      (section13_section16TypeII_of_source_typeII_with_fusionData
        hII hRankSource)
  · rcases hrest with hIII | hrest
    · exact Or.inr <| Or.inl
        (section13_section16TypeIII_of_source_typeIII_with_fusionData hIII hFusion)
    · rcases hrest with hIV | hV
      · exact Or.inr <| Or.inr
          (section13_section16TypeIV_of_source_typeIV_with_fusionData hIV hFusion)
      · exact False.elim (Section10.theorem_10_10 ⟨Smax, P, hSmax, hMF, hV⟩)

private theorem section13_theorem_13_2_case_9_7_hypothesis92BridgeData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_hypothesis92BridgeData Smax P U W1 W2 := by
  exact ⟨
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    (by
      rcases _hsource with
        ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
          _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
      exact hptypeS),
    section13_theorem_13_2_case_9_7_hypothesis92SourceCoreData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_case_9_7_hypothesis92BGTypes_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1) := by
  have hbridge :=
    section13_theorem_13_2_case_9_7_hypothesis92BridgeData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, hMF,
      _hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hcaseII,
      _hStypes, _hTtypes, _hmaxclass⟩
  rcases hbridge with ⟨htypeP, hPsource, hcore, htypes⟩
  rcases hcore with ⟨hcondition, hII, hIII, hIV⟩
  exact
    { maximal := hSmax
      mf := hMF
      typeP := htypeP
      typePDefinitionData := hPsource
      typeIIToIVSourceCondition := hcondition
      typeIISource := hII
      typeIIISource := hIII
      typeIVSource := hIV
      typeCases := htypes
      q_eq := rfl }

private theorem section13_theorem_13_2_typeIIIIVVData_core_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P) :
    Section10.typeIIIIVVData Smax P W1 W2 (section16HatW W1 W2) := by
  have h92full : Section9.hypothesis_9_2_statement Smax P U W1 W2
      (Nat.card W1) :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  letI : IsMinCE G := hMin
  have hFusion : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsource hP
  refine ⟨rfl, U, h92full.typePDefinitionData, ?_⟩
  rcases hTypeIIIIV with hIII | hIV
  · have hIIIbg : section16TypeIII Smax P :=
      section13_section16TypeIII_of_source_typeIII_with_fusionData hIII hFusion
    rcases h92full.typeIIISource hIIIbg with ⟨hcomm, hnorm⟩
    exact Or.inl ⟨h92full.typeIIToIVSourceCondition, hcomm, hnorm⟩
  · have hIVbg : section16TypeIV Smax P :=
      section13_section16TypeIV_of_source_typeIV_with_fusionData hIV hFusion
    rcases h92full.typeIVSource hIVbg with ⟨hncomm, hnorm⟩
    exact Or.inr (Or.inl ⟨h92full.typeIIToIVSourceCondition, hncomm, hnorm⟩)

private theorem section13_theorem_13_2_hypothesis52FullData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∃ Ms : Subgroup G, ∃ Abook : Set G,
      ∃ d52 : Section8.section8Hypothesis52FullData Smax Ms W1 W2 Abook,
        P ≤ Ms ∧ d52.tau = τS ∧
          typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 d52.W d52.sigma ∧
          ((Section8.typeIIIDefinitionData Smax P ∨
              Section8.typeIVDefinitionData Smax P ∨
                Section8.typeVDefinitionData Smax P) →
            Ms = ambientDerivedSubgroup Smax) := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, hFourSixS, _hFourSixT⟩
  exact section13_hypothesis52FullData_with_late_of_typePFourSix
    hSTypeP hFourSixS
private theorem section13_theorem_13_2_hypothesis10_of_typeIIIIV_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P) :
    ∃ S : Finset (Section1.ClassFunction Smax),
      Section10.hypothesis_10_1_supported_data Smax P W1 W2
        (section16HatW W1 W2) S τS := by
  classical
  have hsourceFull := hsource
  have hType : Section10.typeIIIIVVData Smax P W1 W2
      (section16HatW W1 W2) :=
    section13_theorem_13_2_typeIIIIVVData_core_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource hTypeIIIIV
  rcases Section12.exists_puncturedInducedFamily (derivedSubgroup Smax) with
    ⟨S, hSderived0⟩
  have hSderived : Section10.derivedInducedFamily Smax S := by
    simpa [Section10.derivedInducedFamily, Section7.puncturedInducedFamily]
      using hSderived0
  rcases hsource with
    ⟨hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmaxMax, _hTmaxMax,
      _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hSType, _hTType, _hCover⟩
  have hSTypePcopy := hSTypeP
  rcases hSTypePcopy with
    ⟨hPMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      hW2lePSecond, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hPleS : P ≤ Smax :=
    hDerComp.1.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Smax))
  have hW1leS : W1 ≤ Smax := hW1Hall.1
  have hW2leP : W2 ≤ P := (le_inf_iff.mp hW2lePSecond).1
  have hW2leS : W2 ≤ Smax := hW2leP.trans hPleS
  have hWsupS : W1 ⊔ W2 ≤ Smax := sup_le hW1leS hW2leS
  rcases hFourSixS with
    ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, i0, j0, μloc, δSign,
      ωloc, σloc, hNotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBookSource⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hNotation10Full := hNotation10
  rcases hNotation10 with
    ⟨MFsrc, Ms, Abook, A0book, A1book, hSource, hWloc, _hA0,
      h46loc, _h33, _hIso, _hVirt, _hPrin, _hSigmaCyclic, _h45, _h48,
      _hTauIso, _hPackage⟩
  rcases hSource with
    ⟨_hApre, _hA0sub, hNotationBook, H_A0, hA0M, hτDade⟩
  have hMFsrc_eq : MFsrc = P :=
    section16MFSubgroup_unique hNotationBook.2.1 hPMF
  subst MFsrc
  have hLateType :
      Section8.typeIIIDefinitionData Smax P ∨
        Section8.typeIVDefinitionData Smax P ∨
          Section8.typeVDefinitionData Smax P := by
    rcases hTypeIIIIV with hIII | hIV
    · exact Or.inl hIII
    · exact Or.inr (Or.inl hIV)
  have hMsEq : Ms = ambientDerivedSubgroup Smax :=
    Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
      hNotationBook hLateType
  have hMsSubEq : Ms.subgroupOf Smax = derivedSubgroup Smax := by
    rw [hMsEq]
    exact section12_ambientDerivedSubgroup_subgroupOf_eq
  have hDade :
      Section10.dadeIsometryRelativeToA0SupportedSourceData Smax P τS :=
    ⟨Ms, Abook, A0book, A1book, H_A0, hNotationBook, hA0M, hτDade⟩
  have h46 :
      ∃ A46 : Set Smax,
        Section4Scratch.hypothesis_4_6_statement
          (derivedSubgroup Smax)
          (W1.subgroupOf Smax)
          (W2.subgroupOf Smax)
          ((W1 ⊔ W2).subgroupOf Smax)
          (derivedSubgroup Smax)
          A46 := by
    have h46loc' := h46loc
    rw [hWloc, hMsSubEq] at h46loc'
    exact ⟨A, h46loc'⟩
  have hNotation10Exists :
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W10 : Subgroup Smax, ∃ A10 A010 : Set Smax, ∃ i010 : I,
      ∃ j010 : J, ∃ μ10 : I → J → Section1.ClassFunction Smax,
      ∃ δ10 : J → ℤ, ∃ ω10 : I → J → Section1.ClassFunction W10,
      ∃ σ10 : Section1.ClassFunction W10 →ₗ[ℂ] Section1.ClassFunction G,
        @Section10.section10FourSixNotationSupportedData G _ _ I J instI instJ
          decI decJ Smax W1 W2 W10 A10 A010 i010 j010 μ10 δ10 ω10
          σ10 τS :=
    ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, i0, j0,
      μloc, δSign, ωloc, σloc, hNotation10Full⟩
  rcases section13_theorem_13_2_hypothesis52FullData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull with
    ⟨Ms52, Abook52, d52, _hPleMs52, hd52τ, _hSigmaAgree, hMs52Late⟩
  have hMs52Eq : Ms52 = ambientDerivedSubgroup Smax := hMs52Late hLateType
  have hS8der :
      Section8.section8InducedNonkernelFamily Smax
        (ambientDerivedSubgroup Smax) S :=
    Section10.section8InducedNonkernelFamily_of_typeP_derivedInducedFamily
      hSTypeP hSderived
  have hS8 : Section8.section8InducedNonkernelFamily Smax Ms52 S := by
    simpa [hMs52Eq] using hS8der
  have h52d : Section5.hypothesis_5_2_statement S d52.tau :=
    Section8.theorem_8_15_hypothesis_5_2_of_fullData hMin d52 hS8
  have h52 : Section5.hypothesis_5_2_statement S τS := by
    rwa [hd52τ] at h52d
  exact ⟨S, hSmaxMax, hType, hSderived, hW1leS, hW2leS, hWsupS, hDade,
    h46, hNotation10Exists, h52⟩
private theorem section13_theorem_13_2_hypothesis11_of_typeIIIIV_hoReduction_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P)
    {S : Finset (Section1.ClassFunction Smax)}
    (h10 : Section10.hypothesis_10_1_supported_data Smax P W1 W2
      (section16HatW W1 W2) S τS)
    {H0 : Subgroup G} {hp : Nat.Primes}
    (hho : Section9.hoReductionData Smax P U W2 H0 hp) :
    Section11.hypothesis_11_2_data Smax P P U C H0 W1 W2 S τS hp.val q := by
  classical
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hpW2, hqW1, hCeq, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  have hFusion : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig hP
  have hTypeIIIIV16 :
      section16TypeIII Smax P ∨ section16TypeIV Smax P := by
    rcases hTypeIIIIV with hIII | hIV
    · exact Or.inl
        (section13_section16TypeIII_of_source_typeIII_with_fusionData hIII hFusion)
    · exact Or.inr
        (section13_section16TypeIV_of_source_typeIV_with_fusionData hIV hFusion)
  have hOddS : Odd (Nat.card Smax) := by
    letI : IsMinCE G := hMin
    exact odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card Smax)
  have hSTypePcopy := hSTypeP
  rcases hSTypePcopy with
    ⟨_hPMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, hUleDer,
      _hUnil, _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hPleDer : P ≤ ambientDerivedSubgroup Smax := hDerComp.1
  have h92 :
      Section9.hypothesis_9_2_statement Smax P U W1 W2 q := by
    have h92Nat :=
      section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig
    exact { h92Nat with q_eq := by simp [hqW1] }
  rcases hho with
    ⟨hH0P, _hPSmax, hH0NormalS, hH0NormalP, hH0LtP, hElem, hTypeData⟩
  have hH0S : H0 ≤ Smax :=
    hH0P.trans (hPleDer.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Smax)))
  rcases hElem with ⟨hH0NormalP', hElemAbelian⟩
  rcases hTypeData hTypeIIIIV16 with ⟨hW2card, hChief, hNotCent⟩
  have hQuot :
      ∃ hH0H : (H0.subgroupOf P).Normal,
        letI : (H0.subgroupOf P).Normal := hH0H
        Nontrivial (P ⧸ H0.subgroupOf P) ∧
          IsElementaryAbelian hp.val (P ⧸ H0.subgroupOf P) := by
    refine ⟨hH0NormalP', ?_⟩
    letI : (H0.subgroupOf P).Normal := hH0NormalP'
    constructor
    · have hH0P_ne_top : H0.subgroupOf P ≠ ⊤ := by
        intro htop
        have hle : P ≤ H0 := (Subgroup.subgroupOf_eq_top).1 htop
        exact hH0LtP.not_ge hle
      exact (QuotientGroup.nontrivial_iff
        (N := H0.subgroupOf P)).2 hH0P_ne_top
    · exact hElemAbelian
  have hComm : ¬ ⁅U, P⁆ ≤ H0 := by
    intro hle
    exact hNotCent ((Section9.quotientCentralizedBy_iff_commutator_le_sec9).2 hle)
  have hpW2 : hp.val = Nat.card W2 := hW2card.symm
  exact
    ⟨h10, rfl, hTypeIIIIV16, hPleDer, hUleDer, hCeq, hH0P,
      ⟨hH0S, hH0NormalS⟩, hp.property, hQuot, hChief, hComm, hpW2,
      hqW1, hSTypeP, hOddS, h92⟩

private theorem section13_theorem_13_2_H0_eq_bot_of_typeIIIIV_hoReduction_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P)
    {H0 : Subgroup G} {hp : Nat.Primes}
    (hho : Section9.hoReductionData Smax P U W2 H0 hp) :
    H0 = ⊥ := by
  rcases section13_theorem_13_2_hypothesis10_of_typeIIIIV_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource hTypeIIIIV with
    ⟨S, h10⟩
  have h11 :
      Section11.hypothesis_11_2_data Smax P P U C H0 W1 W2 S τS hp.val q :=
    section13_theorem_13_2_hypothesis11_of_typeIIIIV_hoReduction_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource hTypeIIIIV h10 hho
  exact (Section11.theorem_11_7 Smax P P U C H0 W1 W2 S τS hp.val q h11).2.2

private theorem section13_theorem_13_2_case_9_7_hoReductionBotData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∃ hp : Nat.Primes, hp.val = p ∧
      Section9.hoReductionData Smax P U W2 (⊥ : Subgroup G) hp := by
  classical
  have hsourceFull := _hsource
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  have h92Nat :
      Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1) :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  have hsourceSwap :=
    section13_hypothesis_13_1_sourceData_swap (G := G) hsourceFull
  have h92NatSwap :
      Section9.hypothesis_9_2_statement Tmax Q V W2 W1 (Nat.card W2) :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
      hsourceSwap
  have hW1prime : Nat.Prime (Nat.card W1) :=
    section13_nat_prime_card_of_hasPrimeOrder
      h92Nat.typeIIToIVSourceCondition.2.1
  have hW2prime : Nat.Prime (Nat.card W2) :=
    section13_nat_prime_card_of_hasPrimeOrder
      h92NatSwap.typeIIToIVSourceCondition.2.1
  rcases Section9.theorem_9_4 Smax P U W1 W2 (Nat.card W1) h92Nat with
    ⟨H0, hp, hho⟩
  have hH0bot : H0 = (⊥ : Subgroup G) := by
    rcases h92Nat.typeCases with hII | hIII | hIV
    · have hquotCard :
          Nat.card (P ⧸ H0.subgroupOf P) = hp.val ^ Nat.card W1 :=
        Section9.theorem_9_6_typeII_quotient_cardinality_source_core_sec9
          Smax P U W1 W2 H0 hp h92Nat hho hII
      have hPcard :
          Nat.card P = Nat.card W2 ^ Nat.card W1 :=
        ((Section9.theorem_9_3 Smax P U W1 W2 (Nat.card W1) h92Nat).1 hII).2
      have hquotDvdP : Nat.card (P ⧸ H0.subgroupOf P) ∣ Nat.card P :=
        Subgroup.card_quotient_dvd_card (s := H0.subgroupOf P)
      have hpPowDvd : hp.val ^ Nat.card W1 ∣ Nat.card W2 ^ Nat.card W1 := by
        rw [hquotCard, hPcard] at hquotDvdP
        exact hquotDvdP
      have hqne : Nat.card W1 ≠ 0 := hW1prime.pos.ne'
      have hpDvdPow : hp.val ∣ Nat.card W2 ^ Nat.card W1 :=
        (dvd_pow_self hp.val hqne).trans hpPowDvd
      have hp_eq_w2 : hp.val = Nat.card W2 :=
        Nat.prime_eq_prime_of_dvd_pow hp.property hW2prime hpDvdPow
      rcases hho with
        ⟨_hH0leP, _hPleS, _hH0NormalS, hH0NormalP, _hH0ltP,
          _hElem, _hTypeData⟩
      haveI : (H0.subgroupOf P).Normal := hH0NormalP
      have hlag :
          Nat.card P =
            Nat.card (P ⧸ H0.subgroupOf P) * Nat.card (H0.subgroupOf P) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := H0.subgroupOf P)
      have hpow_eq_mul :
          Nat.card W2 ^ Nat.card W1 =
            Nat.card W2 ^ Nat.card W1 * Nat.card (H0.subgroupOf P) := by
        calc
          Nat.card W2 ^ Nat.card W1 = Nat.card P := hPcard.symm
          _ = Nat.card (P ⧸ H0.subgroupOf P) * Nat.card (H0.subgroupOf P) :=
            hlag
          _ = Nat.card W2 ^ Nat.card W1 * Nat.card (H0.subgroupOf P) := by
            rw [hquotCard, hp_eq_w2]
      have hpowPos : 0 < Nat.card W2 ^ Nat.card W1 := pow_pos hW2prime.pos _
      have hcardH0sub : Nat.card (H0.subgroupOf P) = 1 := by
        refine Nat.eq_of_mul_eq_mul_left hpowPos ?_
        simpa using hpow_eq_mul.symm
      have hH0sub_bot : H0.subgroupOf P = ⊥ :=
        Subgroup.eq_bot_of_card_eq (H0.subgroupOf P) hcardH0sub
      exact (Subgroup.subgroupOf_eq_bot.mp hH0sub_bot).eq_bot_of_le _hH0leP
    · have hIII_source : Section8.typeIIIDefinitionData Smax P :=
        Section8.theorem_8_8_typeIII_to_source_public
          (G := G) h92Nat.maximal h92Nat.mf hIII
      exact
        section13_theorem_13_2_H0_eq_bot_of_typeIIIIV_hoReduction_sourceContext
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
          hsourceFull (Or.inl hIII_source) hho
    · have hIV_source : Section8.typeIVDefinitionData Smax P :=
        Section8.theorem_8_8_typeIV_to_source_public
          (G := G) h92Nat.maximal h92Nat.mf hIV
      exact
        section13_theorem_13_2_H0_eq_bot_of_typeIIIIV_hoReduction_sourceContext
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
          hsourceFull (Or.inr hIV_source) hho
  subst H0
  have hp_eq : hp.val = p := by
    rcases _hsource with
      ⟨_hcase, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation⟩
    rcases h92Nat.typeCases with hII | hIII | hIV
    · have hquotCard :
          Nat.card (P ⧸ (⊥ : Subgroup G).subgroupOf P) = hp.val ^ Nat.card W1 :=
        Section9.theorem_9_6_typeII_quotient_cardinality_source_core_sec9
          Smax P U W1 W2 (⊥ : Subgroup G) hp h92Nat hho hII
      have hPcard :
          Nat.card P = Nat.card W2 ^ Nat.card W1 :=
        ((Section9.theorem_9_3 Smax P U W1 W2 (Nat.card W1) h92Nat).1 hII).2
      have hquotBotCard :
          Nat.card (P ⧸ (⊥ : Subgroup G).subgroupOf P) = Nat.card P := by
        let e : P ⧸ (⊥ : Subgroup G).subgroupOf P ≃* P :=
          (QuotientGroup.quotientMulEquivOfEq
            (Subgroup.bot_subgroupOf (G := G) (H := P))).trans
            (QuotientGroup.quotientBot (G := P))
        exact Nat.card_congr e.toEquiv
      have hpPowEq : hp.val ^ Nat.card W1 = Nat.card W2 ^ Nat.card W1 := by
        calc
          hp.val ^ Nat.card W1 =
              Nat.card (P ⧸ (⊥ : Subgroup G).subgroupOf P) := hquotCard.symm
          _ = Nat.card P := hquotBotCard
          _ = Nat.card W2 ^ Nat.card W1 := hPcard
      have hqne : Nat.card W1 ≠ 0 := hW1prime.pos.ne'
      have hpDvdPow : hp.val ∣ Nat.card W2 ^ Nat.card W1 := by
        rw [← hpPowEq]
        exact dvd_pow_self hp.val hqne
      have hp_eq_w2 : hp.val = Nat.card W2 :=
        Nat.prime_eq_prime_of_dvd_pow hp.property hW2prime hpDvdPow
      exact hp_eq_w2.trans hp_card.symm
    · exact ((hho.2.2.2.2.2.2 (Or.inl hIII)).1).symm.trans hp_card.symm
    · exact ((hho.2.2.2.2.2.2 (Or.inr hIV)).1).symm.trans hp_card.symm
  exact ⟨hp, hp_eq, hho⟩

private theorem section13_le_setNormalizer_of_le_normalizer
    {G : Type u} [Group G] {M : Subgroup G} {A : Set G}
    (h : M ≤ Subgroup.normalizer A) :
    M ≤ Section2.setNormalizer A := by
  intro m hm
  change Section2.normalizesSet A m
  intro a
  have hmnorm := h hm
  change ∀ a : G, a ∈ A ↔ m * a * m⁻¹ ∈ A at hmnorm
  simpa [Section2.conjBy] using (hmnorm a).symm


private theorem section13_theorem_13_2_Smax_maximal_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Smax ∈ section9MaximalSubgroups G := by
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  exact hcase.2.2.2.2.2.1

private theorem section13_ASet_le_normalizer_of_le_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M U : Subgroup G}
    (hUσ : U ≤ section10Msigma M) :
    M ≤ Subgroup.normalizer (section16ASet M U) := by
  classical
  have hconj_mem :
      ∀ {m a : G}, m ∈ M → a ∈ section16ASet M U →
        m * a * m⁻¹ ∈ section16ASet M U := by
    intro m a hm ha
    rcases ha with ⟨haHat, haProd, hane⟩
    rcases haProd with ⟨u, huU, s, hsσ, ha_eq⟩
    have huσ : u ∈ section10Msigma M := hUσ huU
    have haσ : a ∈ section10Msigma M := by
      rw [← ha_eq]
      exact (section10Msigma M).mul_mem huσ hsσ
    have hmNormSigma : m ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      section12_le_normalizer_msigma (M := M) hm
    have hconjσ : m * a * m⁻¹ ∈ section10Msigma M :=
      (Subgroup.mem_normalizer_iff.mp hmNormSigma a).1 haσ
    have hconjne : m * a * m⁻¹ ≠ 1 := by
      intro h
      exact hane (by
        have h' := congrArg (fun t : G => m⁻¹ * t * m) h
        simpa [mul_assoc] using h')
    have hconjM : m * a * m⁻¹ ∈ M :=
      section11_msigma_le M hconjσ
    have hconjCent : (m * a * m⁻¹) ∈
        elementCentralizerIn (section10Msigma M) (m * a * m⁻¹) := by
      refine ⟨hconjσ, ?_⟩
      change m * a * m⁻¹ ∈ Subgroup.centralizer ({m * a * m⁻¹} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hconjCentNe :
        elementCentralizerIn (section10Msigma M) (m * a * m⁻¹) ≠ ⊥ := by
      intro hbot
      have hxbot : m * a * m⁻¹ ∈ (⊥ : Subgroup G) := by
        simpa [hbot] using hconjCent
      exact hconjne (by simpa using hxbot)
    refine ⟨⟨hconjM, hconjCentNe⟩, ?_, hconjne⟩
    exact ⟨1, U.one_mem, m * a * m⁻¹, hconjσ, by simp⟩
  intro m hm
  change ∀ a : G, a ∈ section16ASet M U ↔
    m * a * m⁻¹ ∈ section16ASet M U
  intro a
  constructor
  · intro ha
    exact hconj_mem hm ha
  · intro ha
    have hminv : m⁻¹ ∈ M := M.inv_mem hm
    have hback :
        m⁻¹ * (m * a * m⁻¹) * (m⁻¹)⁻¹ ∈ section16ASet M U :=
      hconj_mem hminv ha
    simpa [mul_assoc] using hback

private theorem section13_typeP_ASet_le_setNormalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Smax ≤ Section2.setNormalizer (section16ASet Smax U) := by
  classical
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  have hSmaxMax : Smax ∈ section9MaximalSubgroups G :=
    section13_theorem_13_2_Smax_maximal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  rcases _hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hptypeS with
    ⟨hPMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, hUnil,
      _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  by_cases hUσ : U ≤ section10Msigma Smax
  · exact section13_le_setNormalizer_of_le_normalizer
      (section13_ASet_le_normalizer_of_le_msigma
        (G := G) (M := Smax) (U := U) hUσ)
  · rcases source_typeP_exists_KUData_of_not_le_msigma_core
        hMin hSmaxMax hPMF
        (by
          intro hUbot
          exact hUσ (by rw [hUbot]; exact bot_le))
        hUσ
        (by
          exact ⟨hPMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, hUnil,
            _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
            _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩) with
      ⟨K, hKU⟩
    exact section13_le_setNormalizer_of_le_normalizer
      (section16_ASet_le_normalizer_public
        (G := G) (M := Smax) (K := K) (U := U) hSmaxMax hKU)


private theorem section13_typeP_ASet_subset_A0book_of_typePFourSix_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hTypeCases :
      Section8.typeIIDefinitionData M MF ∨
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF)
    (hTypeIIBg :
      Section8.typeIIDefinitionData M MF → section16TypeII M MF)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    ∃ A0book : Set G, ∃ H_A0 : G → Subgroup G,
      ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
        section16ASet M U ⊆ A0book ∧
          ∀ α : Section1.ClassFunction M,
            τ α = Section2.dadeTransform H_A0 hA0M.subset_L α := by
  classical
  have hPcopy := hP
  rcases hPcopy with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleDer,
      _hUnil, _hW1norm, _hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hMsigmaLeDer : section10Msigma M ≤ ambientDerivedSubgroup M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨y, (theorem_10_2_c (G := G) hM).2 hy, rfl⟩
  rcases hFourSix with
    ⟨_I, _instI, _decI, _J, _instJ, _decJ, _W, _A, _A0, _i0, _j0,
      _μ, _δSign, _ω, _σ, _hNotation, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, hBookSource⟩⟩
  rcases hBookSource with
    ⟨Ms, Abook, A0book, A1book, H_A0, hA0M, hNotationBook, hAbook,
      hA0book, _hMFleMs, hMsSharp, hτDade⟩
  have hASetSub : section16ASet M U ⊆ A0book := by
    rcases hTypeCases with hII | hLate
    · have hMsEq : Ms = MF :=
        Section8.msChoiceSource_eq_mf_of_typeII hNotationBook.2.2.1 hII
      subst Ms
      have hASetSubAbook : section16ASet M U ⊆ Abook :=
        Section8.typeII_section16ASet_subset_notation_A_source_data
          hM hMF (hTypeIIBg hII) hII hP hNotationBook
      intro x hx
      rw [hA0book]
      exact Or.inl (hASetSubAbook hx)
    · have hMsEq : Ms = ambientDerivedSubgroup M :=
        Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
          hNotationBook hLate
      intro x hx
      rcases Set.mem_mul.mp hx.2.1 with ⟨u0, huU, s0, hsSigma, hxEq⟩
      have hxDer : x ∈ ambientDerivedSubgroup M := by
        rw [← hxEq]
        exact (ambientDerivedSubgroup M).mul_mem
          (hUleDer huU) (hMsigmaLeDer hsSigma)
      let l : M := ⟨x, hx.1.1⟩
      apply hMsSharp l
      constructor
      · simpa [hMsEq, l] using hxDer
      · simpa [l] using hx.2.2
  exact ⟨A0book, H_A0, hA0M, hASetSub, hτDade⟩
private theorem section13_theorem_13_2_case_9_7_dadeASet_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section9.dadeIsometryRelativeToASet Smax U τS := by
  classical
  have hsourceFull := _hsource
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull
  letI : IsMinCE G := hMin
  have hSmax : Smax ∈ section9MaximalSubgroups G :=
    section13_theorem_13_2_Smax_maximal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull
  rcases _hsource with
    ⟨hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMinSource, hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax,
      _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII,
      hSTypeCases, _hTTypeCases, _hCover⟩
  have hptypeSfull := hptypeS
  have hTypeIIBg :
      Section8.typeIIDefinitionData Smax P → section16TypeII Smax P := by
    intro hII
    exact section13_section16TypeII_of_source_typeII_with_fusionData hII
      (section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceFull hII)
  have hnormA : Smax ≤ Section2.setNormalizer (section16ASet Smax U) :=
    section13_typeP_ASet_le_setNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull
  rcases section13_typeP_ASet_subset_A0book_of_typePFourSix_source
      hSmax hptypeSfull hSTypeCases hTypeIIBg hFourSixS with
    ⟨A0book, H_A0, hA0M, hA_sub_A0, hτA0⟩
  have hAMG : Section2.Hypothesis2 (section16ASet Smax U) Smax H_A0 :=
    Section2.proposition_2_11_hypothesis hA0M hA_sub_A0 hnormA
  refine ⟨H_A0, hAMG, ?_⟩
  intro χ hχA
  exact (hτA0 χ).trans
    (((Section2.proposition_2_11
        A0book (section16ASet Smax U) Smax H_A0)
        hA_sub_A0 hnormA hA0M).2
      hA0M.subset_L hAMG.subset_L χ hχA)

private theorem section13_theorem_13_2_case_9_7_kernelInducedFamilyBot_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
      (⊥ : Subgroup G) Sfam := by
  rcases _hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hPnoncyc, _hsecond, _hfitting, _hfittingle,
      _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hnormHat⟩
  rcases hDerComp with ⟨_hPder, _hUder, hder_eq, _hdisj⟩
  rw [hder_eq]
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
          (((a : (P ⊔ U).subgroupOf Smax) : Smax) : G) ∈ (⊥ : Subgroup G) := by
        simpa [Subgroup.mem_subgroupOf] using a.property
      simpa [Subgroup.mem_bot] using haBot
    have ha : (a : (P ⊔ U).subgroupOf Smax) = 1 := by
      exact Subtype.ext haS
    simp [ha, Section1.degree]
  · intro hχ
    rcases hχ with ⟨θ, hθirr, hθnotker, _hθbot, hχeq⟩
    rw [hmem χ]
    exact ⟨θ, hθirr, hθnotker, hχeq⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis52b_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section5.hypothesis_5_2_b_statement Sfam τS := by
  rcases _hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, hDadeS, _hDadeT,
      _hnotation⟩
  exact hDadeS

private theorem section13_theorem_13_2_case_9_7_hypothesis95CoreData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_hypothesis95CoreData Smax P U W1 W2 Sfam τS p := by
  exact ⟨
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_case_9_7_hoReductionBotData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_case_9_7_dadeASet_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_case_9_7_kernelInducedFamilyBot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_case_9_7_hypothesis52b_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource⟩

private theorem section13_theorem_13_2_case_9_7_hypothesis95BotData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_hypothesis95BotData Smax P U W1 W2 C Sfam τS p := by
  have hBarU : Section9.quotientBarUCardinality U C u :=
    section13_theorem_13_2_quotientBarUCardinality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource
  rcases _hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases section13_theorem_13_2_case_9_7_hypothesis95CoreData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation⟩ with
    ⟨h92, hpdata, hDade, hSfam, h52⟩
  rcases hpdata with ⟨hp, hp_eq, hpdata⟩
  let Cprime : Subgroup G := (_root_.commutator C).map C.subtype
  exact ⟨Cprime, hp, hp_eq,
    ⟨h92, ⟨hp, hpdata⟩, section13_quotientCentralizerIn_bot_of_subgroupCentralizerIn hC,
      ⟨u, hBarU⟩, section13_commutator_map_subtype_le C, rfl, hDade, hSfam,
      h52⟩,
    hpdata⟩

private theorem section13_theorem_13_2_case_9_7_corePrereqData_of_hypothesis95BotData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hdata : theorem_13_2_case_9_7_hypothesis95BotData Smax P U W1 W2 C
      Sfam τS p) :
    theorem_13_2_case_9_7_corePrereqData Smax P U W1 W2 p q := by
  have hsourceFull := hsource
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hdata with ⟨Cprime, hp, hp_eq, h95, hpdata⟩
  have h92Nat :
      Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1) :=
    h95.hypothesis92
  have h92q : Section9.hypothesis_9_2_statement Smax P U W1 W2 q := by
    exact { h92Nat with q_eq := by simp [hq_card] }
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull
  letI : IsMinCE G := hMin
  rcases Section9.theorem_9_6_source_core_sec9 Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS Sfam hp h95 hpdata with
    ⟨_hUC, hchief, hWbar2, hcard⟩
  have h96 : Section9.quotientChiefFactorData_9_6 Smax P (⊥ : Subgroup G) W1 hp :=
    Section9.quotientChiefFactorData_9_6_of_source_facts Smax P U W1 W2
      (⊥ : Subgroup G) hp h92Nat hpdata hchief hWbar2 hcard
  exact ⟨h92q, ⟨hp, hp_eq, hpdata, h96⟩⟩

private theorem section13_theorem_13_2_case_9_7_corePrereqData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_corePrereqData Smax P U W1 W2 p q := by
  exact section13_theorem_13_2_case_9_7_corePrereqData_of_hypothesis95BotData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource
    (section13_theorem_13_2_case_9_7_hypothesis95BotData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource)

private theorem section13_theorem_13_2_case_9_7_prereqData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_prereqData Smax P U W1 W2 C p q u := by
  rcases section13_theorem_13_2_case_9_7_corePrereqData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource with
    ⟨h92, hp96⟩
  exact ⟨h92, hp96,
    section13_theorem_13_2_quotientBarUCardinality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource⟩

private theorem section13_theorem_13_2_case_9_7_setupData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_case_9_7_setupData Smax P U W1 W2 C p q u := by
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases section13_theorem_13_2_case_9_7_prereqData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation⟩ with
    ⟨h92, hp96, hBarU⟩
  exact ⟨h92, hp96, section13_quotientCentralizerIn_bot_of_subgroupCentralizerIn hC,
    hBarU⟩

private theorem section13_theorem_13_2_case_9_7_sourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u ∨
      case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource
  letI : IsMinCE G := hMin
  exact section13_theorem_13_2_case_9_7_sourceData_from_setupData
    (section13_theorem_13_2_case_9_7_setupData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource)

public theorem theorem_13_2_case_9_7_sourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u ∨
      case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  exact section13_theorem_13_2_case_9_7_sourceData_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource

private theorem section13_theorem_13_2_uBoundBranchData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_uBoundBranchData p q u := by
  rcases section13_theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    hcaseA | hcaseB
  · exact section13_theorem_13_2_uBoundBranchData_of_caseA hcaseA
  · exact section13_theorem_13_2_uBoundBranchData_of_caseB hcaseB


/-! ## Proof placeholders -/

private def theorem_13_2_typeAndUBranchData
    {G : Type u} [Group G] [Finite G]
    (Smax P U : Subgroup G) (p q : ℕ) : Prop :=
  (Section8.typeIIDefinitionData Smax P ∧ IsMulCommutative U ∧ U ≠ ⊥) ∨
    (Section8.typeIIIDefinitionData Smax P ∧ p ≤ q ∧ IsMulCommutative U ∧ U ≠ ⊥)

private def theorem_13_2_typeAndUCurrentBranchData
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 : Subgroup G) (p q : ℕ) : Prop :=
  (Section8.typeIIDefinitionData Smax P ∨
      (Section8.typeIIIDefinitionData Smax P ∧ p ≤ q)) ∧
    Section8.typeIIToIVSourceCondition Smax U W1 ∧
    IsMulCommutative U


private theorem section13_theorem_13_2_hypothesis11_of_typeIIIIV_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P)
    {S : Finset (Section1.ClassFunction Smax)}
    (h10 : Section10.hypothesis_10_1_supported_data Smax P W1 W2
      (section16HatW W1 W2) S τS)
    (hcaseS : case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u ∨
      case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u) :
    Section11.hypothesis_11_2_data Smax P P U C ⊥ W1 W2 S τS p q := by
  classical
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, hpW2, hqW1, hCeq, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  have hFusion : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig hP
  have hTypeIIIIV16 :
      section16TypeIII Smax P ∨ section16TypeIV Smax P := by
    rcases hTypeIIIIV with hIII | hIV
    · exact Or.inl
        (section13_section16TypeIII_of_source_typeIII_with_fusionData hIII hFusion)
    · exact Or.inr
        (section13_section16TypeIV_of_source_typeIV_with_fusionData hIV hFusion)
  have hOddS : Odd (Nat.card Smax) := by
    letI : IsMinCE G := hMin
    exact odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card Smax)
  have hSTypePcopy := hSTypeP
  rcases hSTypePcopy with
    ⟨_hPMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, hUleDer,
      _hUnil, _hW1norm, hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hPleDer : P ≤ ambientDerivedSubgroup Smax := hDerComp.1
  have hcaseCore :
      Section9.hypothesis_9_2_statement Smax P U W1 W2 q ∧
        ∃ hp : Nat.Primes,
          hp.val = p ∧ Section9.hoReductionData Smax P U W2 ⊥ hp := by
    rcases hcaseS with hcaseA | hcaseB
    · rcases hcaseA with ⟨_hbar, _a, hcaseAcore⟩
      exact
        ⟨Section9.case_9_7_a_hypothesis_9_2_sec9 hcaseAcore,
          Section9.case_9_7_a_hoReductionData_sec9 hcaseAcore⟩
    · exact
        ⟨Section9.case_9_7_b_hypothesis_9_2_sec9 hcaseB,
          Section9.case_9_7_b_hoReductionData_sec9 hcaseB⟩
  rcases hcaseCore with ⟨h92, hpData⟩
  rcases hpData with ⟨hpP, hpPeq, hho⟩
  rcases hho with
    ⟨hBotP, _hPSmax, hBotNormalS, hBotNormalP, hBotLtP, hElem, hTypeData⟩
  rcases hElem with ⟨hBotNormalP', hElemAbelian⟩
  rcases hTypeData hTypeIIIIV16 with ⟨_hW2card, hChief, hNotCent⟩
  have hpPrime : Nat.Prime p := by
    simpa [hpPeq] using hpP.property
  have hQuot :
      ∃ hH0H : ((⊥ : Subgroup G).subgroupOf P).Normal,
        letI : ((⊥ : Subgroup G).subgroupOf P).Normal := hH0H
        Nontrivial (P ⧸ (⊥ : Subgroup G).subgroupOf P) ∧
          IsElementaryAbelian p (P ⧸ (⊥ : Subgroup G).subgroupOf P) := by
    refine ⟨hBotNormalP', ?_⟩
    letI : ((⊥ : Subgroup G).subgroupOf P).Normal := hBotNormalP'
    constructor
    · have hBotP_ne_top : (⊥ : Subgroup G).subgroupOf P ≠ ⊤ := by
        intro htop
        have hle : P ≤ (⊥ : Subgroup G) :=
          (Subgroup.subgroupOf_eq_top).1 htop
        exact hBotLtP.not_ge hle
      exact (QuotientGroup.nontrivial_iff
        (N := (⊥ : Subgroup G).subgroupOf P)).2 hBotP_ne_top
    · simpa [hpPeq] using hElemAbelian
  have hComm : ¬ ⁅U, P⁆ ≤ (⊥ : Subgroup G) := by
    intro hle
    exact hNotCent ((Section9.quotientCentralizedBy_iff_commutator_le_sec9).2 hle)
  exact
    ⟨h10, rfl, hTypeIIIIV16, hPleDer, hUleDer, hCeq, bot_le,
      ⟨bot_le, hBotNormalS⟩, hpPrime, hQuot, hChief, hComm, hpW2,
      hqW1, hSTypeP, hOddS, h92⟩

private theorem section13_sourceChoice_not_typeIII_of_typeIV
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hChoice : hypothesis_13_1_sourceChoiceData G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hIV : Section8.typeIVDefinitionData M MF) :
    ¬ Section8.typeIIIDefinitionData M MF := by
  rcases hChoice M MF hM hMF
      (Or.inr (Or.inr (Or.inr (Or.inl hIV)))) with
    ⟨Ms, hMs⟩
  rcases hMs with hI | hII | hIII | hIVcase | hV
  · rcases hI with ⟨_hI, _hnotII, hnotIII, _hnotIV, _hnotV, _hMs⟩
    exact hnotIII
  · rcases hII with ⟨_hnotI, _hII, hnotIII, _hnotIV, _hnotV, _hMs⟩
    exact hnotIII
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, hnotIV, _hnotV, _hMs⟩
    exact fun _hIII' => hnotIV hIV
  · rcases hIVcase with ⟨_hnotI, _hnotII, hnotIII, _hIV, _hnotV, _hMs⟩
    exact hnotIII
  · rcases hV with ⟨_hnotI, _hnotII, hnotIII, _hnotIV, _hV, _hMs⟩
    exact hnotIII

private theorem section13_theorem_13_2_pf119Output_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P) :
    q > p ∧ section16TypeIII Smax P := by
  classical
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  letI : IsMinCE G := hMin
  rcases section13_theorem_13_2_hypothesis10_of_typeIIIIV_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource hTypeIIIIV with
    ⟨S, h10⟩
  have hcaseS :
      case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u ∨
        case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section13_theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  have h11 :
      Section11.hypothesis_11_2_data Smax P P U C (⊥ : Subgroup G)
        W1 W2 S τS p q :=
    section13_theorem_13_2_hypothesis11_of_typeIIIIV_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource hTypeIIIIV h10 hcaseS
  rcases
      Section10.exists_section10FourSixNotationSupportedData_of_hypothesis_10_1_supported_data
        h10 with
    ⟨I, instI, decI, J, instJ, decJ, Wloc, A, A0, i0, j0, μ, δSign,
      ω, σ, hNotation⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hHCle : P ⊔ C ≤ Smax := by
    have h11copy := h11
    rcases h11copy with
      ⟨_h10, _hHMF, _htype, hPleDer, hUleDer, hCeq, _hH0leH,
        _hH0norm, _hp, _hQuot, _hChief, _hComm, _hpW2, _hqW1,
        _hTypeP, _hOddAnd92⟩
    have hDerLe : ambientDerivedSubgroup Smax ≤ Smax :=
      section12_ambientDerivedSubgroup_le (G := G) (E := Smax)
    have hPleS : P ≤ Smax := hPleDer.trans hDerLe
    have hCleU : C ≤ U := by
      rw [hCeq]
      exact inf_le_left
    have hCleS : C ≤ Smax := hCleU.trans (hUleDer.trans hDerLe)
    exact sup_le hPleS hCleS
  let SHC : Finset (Section1.ClassFunction Smax) :=
    S.filter fun χ => Section1.subgroupInKernel' χ ((P ⊔ C).subgroupOf Smax)
  have hSHC : Section11.section11Subfamily (P ⊔ C) S SHC := by
    dsimp [SHC]
    exact section13_section11Subfamily_filter (X := P ⊔ C) S hHCle
  rcases Section11.section11Subfamily_H_sup_C_nonempty_of_hypothesis
      Smax P P U C (⊥ : Subgroup G) W1 W2 S SHC τS p q h11 hSHC with
    ⟨ζ, hζ⟩
  rcases section13_exists_transformedIrreducibleFamily Wloc σ with
    ⟨R, hR⟩
  rcases Section11.theorem_11_9
      Smax P P U C (⊥ : Subgroup G) W1 W2 Wloc A A0 S SHC R i0 j0
      μ δSign ω σ τS ζ p q h11 hNotation hSHC hζ hR with
    ⟨_hOrth, hqgt, _hCaseB, hIIIbg⟩
  exact ⟨hqgt, hIIIbg⟩

private theorem section13_theorem_13_2_typeIII_q_gt_p_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hIII : Section8.typeIIIDefinitionData Smax P) :
    q > p := by
  exact (section13_theorem_13_2_pf119Output_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
    _hsource (Or.inl _hIII)).1

private theorem section13_theorem_13_2_typeIV_contradiction_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hIV : Section8.typeIVDefinitionData Smax P) :
    False := by
  have hIIIbg : section16TypeIII Smax P :=
    (section13_theorem_13_2_pf119Output_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource (Or.inr _hIV)).2
  have hsourceCopy := _hsource
  rcases hsourceCopy with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD, _hc,
      _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, _hTmax, hMF,
      _hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hStypes, _hTtypes, _hmaxclass⟩
  have hIII : Section8.typeIIIDefinitionData Smax P :=
    Section8.theorem_8_8_typeIII_to_source_public (G := G) hSmax hMF hIIIbg
  exact (section13_sourceChoice_not_typeIII_of_typeIV hChoice hSmax hMF _hIV) hIII


private theorem section13_theorem_13_2_typeAlternatives_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typeIIDefinitionData Smax P ∨
      Section8.typeIIIDefinitionData Smax P ∨
      Section8.typeIVDefinitionData Smax P ∨
      Section8.typeVDefinitionData Smax P := by
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, hSType, _hTType,
      _hCover⟩
  exact hSType

private theorem section13_theorem_13_2_not_typeV_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ¬ Section8.typeVDefinitionData Smax P := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  intro hV
  exact Section10.theorem_10_10 ⟨Smax, P, hSmax, hSF, hV⟩

public theorem section13_theorem_13_2_typeIIIIVVData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeIIIIV :
      Section8.typeIIIDefinitionData Smax P ∨ Section8.typeIVDefinitionData Smax P) :
    Section10.typeIIIIVVData Smax P W1 W2 (section16HatW W1 W2) := by
  have h92full : Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1) :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  letI : IsMinCE G := hMin
  have hFusion : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsource hP
  refine ⟨rfl, U, h92full.typePDefinitionData, ?_⟩
  rcases hTypeIIIIV with hIII | hIV
  · have hIIIbg : section16TypeIII Smax P :=
      section13_section16TypeIII_of_source_typeIII_with_fusionData hIII hFusion
    rcases h92full.typeIIISource hIIIbg with ⟨hcomm, hnorm⟩
    exact Or.inl ⟨h92full.typeIIToIVSourceCondition, hcomm, hnorm⟩
  · have hIVbg : section16TypeIV Smax P :=
      section13_section16TypeIV_of_source_typeIV_with_fusionData hIV hFusion
    rcases h92full.typeIVSource hIVbg with ⟨hncomm, hnorm⟩
    exact Or.inr (Or.inl ⟨h92full.typeIIToIVSourceCondition, hncomm, hnorm⟩)


public theorem theorem_13_2_section16TypeIII_of_source_typeIII
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hIII : Section8.typeIIIDefinitionData Smax P) :
    section16TypeIII Smax P := by
  have hFusion : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsource hP
  exact section13_section16TypeIII_of_source_typeIII_with_fusionData hIII hFusion


public theorem section13_odd_card_subgroup_of_odd_group
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (hoddG : Odd (Nat.card G)) :
    Odd (Nat.card M) :=
  odd_of_card_dvd hoddG (Subgroup.card_subgroup_dvd_card M)


private theorem section13_theorem_13_2_not_typeIV_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ¬ Section8.typeIVDefinitionData Smax P := by
  exact section13_theorem_13_2_typeIV_contradiction_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
    _hsource

private theorem section13_theorem_13_2_typeIII_p_le_q_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hIII : Section8.typeIIIDefinitionData Smax P) :
    p ≤ q := by
  exact Nat.le_of_lt
    (section13_theorem_13_2_typeIII_q_gt_p_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource hIII)

private theorem section13_theorem_13_2_typeBranchData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typeIIDefinitionData Smax P ∨
      (Section8.typeIIIDefinitionData Smax P ∧ p ≤ q) := by
  rcases section13_theorem_13_2_typeAlternatives_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    hII | hIII | hIV | hV
  · exact Or.inl hII
  · exact Or.inr ⟨hIII,
      section13_theorem_13_2_typeIII_p_le_q_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource hIII⟩
  · exact False.elim
      (section13_theorem_13_2_not_typeIV_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource hIV)
  · exact False.elim
      (section13_theorem_13_2_not_typeV_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource hV)

private theorem section13_theorem_13_2_currentTypeIIToIVCondition_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typeIIToIVSourceCondition Smax U W1 := by
  have h92full :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  exact h92full.typeIIToIVSourceCondition

private theorem section13_theorem_13_2_currentU_commutative_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    IsMulCommutative U := by
  have h92full :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  have hnotIV : ¬ Section8.typeIVDefinitionData Smax P :=
    section13_theorem_13_2_not_typeIV_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  rcases h92full.typeCases with hII | hIII | hIV
  · exact (h92full.typeIISource hII).1
  · exact (h92full.typeIIISource hIII).1
  · exact False.elim (hnotIV
      ⟨U, W1, W2, h92full.typePDefinitionData, h92full.typeIIToIVSourceCondition,
        (h92full.typeIVSource hIV).1, (h92full.typeIVSource hIV).2⟩)

private theorem section13_theorem_13_2_typeAndUCurrentBranchData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_typeAndUCurrentBranchData Smax P U W1 p q := by
  exact ⟨
    section13_theorem_13_2_typeBranchData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_currentTypeIIToIVCondition_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_currentU_commutative_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource⟩

private theorem section13_theorem_13_2_typeAndUBranchData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_typeAndUBranchData Smax P U p q := by
  rcases section13_theorem_13_2_typeAndUCurrentBranchData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    ⟨hbranch, hcondition, hUcomm⟩
  have hUne : U ≠ ⊥ := hcondition.1
  rcases hbranch with hII | hIII
  · exact Or.inl ⟨hII, hUcomm, hUne⟩
  · rcases hIII with ⟨hIII, hpq⟩
    exact Or.inr ⟨hIII, hpq, hUcomm, hUne⟩

private def theorem_13_2_typeAndUCoreFields
    {G : Type u} [Group G] [Finite G]
    (Smax P U : Subgroup G) (p q : ℕ) : Prop :=
  (Section8.typeIIDefinitionData Smax P ∨ Section8.typeIIIDefinitionData Smax P) ∧
    (q < p → Section8.typeIIDefinitionData Smax P) ∧
    IsMulCommutative U ∧
    U ≠ ⊥

private theorem section13_theorem_13_2_typeAndUCoreFields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_typeAndUCoreFields Smax P U p q := by
  rcases section13_theorem_13_2_typeAndUBranchData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    hII | hIII
  · rcases hII with ⟨hII, hUcomm, hUne⟩
    exact ⟨Or.inl hII, fun _ => hII, hUcomm, hUne⟩
  · rcases hIII with ⟨hIII, hpq, hUcomm, hUne⟩
    exact ⟨Or.inr hIII, fun hqp => False.elim (not_lt_of_ge hpq hqp), hUcomm,
      hUne⟩

private theorem section13_theorem_13_2_type_and_U_fields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    (Section8.typeIIDefinitionData Smax P ∨ Section8.typeIIIDefinitionData Smax P) ∧
      (q < p → Section8.typeIIDefinitionData Smax P) ∧
      IsMulCommutative U ∧
      section12FrobeniusJoinWithKernel U W1 := by
  rcases section13_theorem_13_2_typeAndUCoreFields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource with
    ⟨htype, hlarge, hUcomm, hUne⟩
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  exact ⟨htype, hlarge, hUcomm,
    section13_frobenius_U_sup_W1_of_typePDefinitionData hptypeS hUne⟩

private def theorem_13_2_PFieldsUpstreamData
    {G : Type u} [Group G] [Finite G]
    (Smax P W1 W2 : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ) : Prop :=
  Section10.typeIIElementaryConclusion Smax P W1 W2 Sfam τS ∨
    (IsElementaryAbelian p P ∧ Nat.card P = p ^ q)

private theorem section13_theorem_13_2_P_fields_from_upstreamData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hdata : theorem_13_2_PFieldsUpstreamData Smax P W1 W2 Sfam τS p q) :
    IsElementaryAbelian p P ∧ Nat.card P = p ^ q := by
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hdata with h10 | h11
  · rcases h10 with ⟨hPelem, hPcard, _hcoh⟩
    exact ⟨by simpa [hp_card] using hPelem,
      by simpa [hp_card, hq_card] using hPcard⟩
  · exact h11

private theorem section13_section16TypeI_of_source_typeI_with_msChoice
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : Section8.msChoiceSource M MF Ms)
    (hSrcI : Section8.typeIDefinitionData M MF) :
    section16TypeI M MF := by
  classical
  have hNot :
      ¬ Section8.typeIIDefinitionData M MF ∧
        ¬ Section8.typeIIIDefinitionData M MF ∧
        ¬ Section8.typeIVDefinitionData M MF ∧
          ¬ Section8.typeVDefinitionData M MF := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
      exact ⟨hnotII, hnotIII, hnotIV, hnotV⟩
    · exact False.elim (hII.1 hSrcI)
    · exact False.elim (hIII.1 hSrcI)
    · exact False.elim (hIV.1 hSrcI)
    · exact False.elim (hV.1 hSrcI)
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact hTypeI
  · exact False.elim
      (hNot.1 (Section8.theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
  · exact False.elim
      (hNot.2.1
        (Section8.theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
  · exact False.elim
      (hNot.2.2.1
        (Section8.theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
  · exact False.elim
      (hNot.2.2.2
        (Section8.theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))

private theorem section13_theorem_13_2_caseBData_bg_classifierChoice_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
      section16MFSubgroup M MF →
        Section8.typeIDefinitionData M MF →
          ∃ Ms : Subgroup G, Section8.msChoiceSource M MF Ms := by
  rcases _hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, _hMin⟩
  intro M MF hM hMF hTypeI
  exact hChoice M MF hM hMF (Or.inl hTypeI)

private theorem section13_theorem_13_2_caseBData_bg_classifier_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      (∃ g : G, M = Smax.conjBy g) ∨
        (∃ g : G, M = Tmax.conjBy g) ∨
          ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  have hChoice :=
    section13_theorem_13_2_caseBData_bg_classifierChoice_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  rcases _hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax,
      _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      _hStypes, _hTtypes, hclass⟩
  intro M hM
  rcases hclass M hM with hS | hT | hI
  · exact Or.inl hS
  · exact Or.inr (Or.inl hT)
  · rcases hI with ⟨MF, hMF, hSrcI⟩
    rcases hChoice M MF hM hMF hSrcI with ⟨Ms, hMs⟩
    exact Or.inr (Or.inr ⟨MF, hMF,
      section13_section16TypeI_of_source_typeI_with_msChoice
        (G := G) hM hMF hMs hSrcI⟩)

private theorem section13_theorem_13_2_caseBData_bg_hardFields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ¬ section16TypeI Smax P ∧
      ¬ section16TypeI Tmax Q ∧
        ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
          (∃ g : G, M = Smax.conjBy g) ∨
            (∃ g : G, M = Tmax.conjBy g) ∨
              ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF := by
  have hsourceOrig := _hsource
  have hsourceSwap :=
    section13_hypothesis_13_1_sourceData_swap (G := G) hsourceOrig
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceOrig
  letI : IsMinCE G := hMin
  rcases _hsource with
    ⟨hcase, hptypeS, hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, hSmax, hTmax, hSMF, hTMF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT, _hStypes,
      _hTtypes, _hclass⟩
  have hFusionS :
      theorem_13_2_typeCommonT6FusionData Smax P U :=
    section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceOrig hptypeS
  have hFusionT :
      theorem_13_2_typeCommonT6FusionData Tmax Q V :=
    section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
      hsourceSwap hptypeT
  have hT6S := section13_typeCommonT6_of_fusionData hFusionS
  have hT6T := section13_typeCommonT6_of_fusionData hFusionT
  have hPDataS : Section8.typePData Smax P U W1 W2 :=
    section13_typePData_of_typePDefinitionData_T6 hptypeS hT6S
  have hPDataT : Section8.typePData Tmax Q V W2 W1 :=
    section13_typePData_of_typePDefinitionData_T6 hptypeT hT6T
  exact ⟨
    section16_not_typeI_of_typeCommon hSmax hSMF hPDataS.2,
    section16_not_typeI_of_typeCommon hTmax hTMF hPDataT.2,
    section13_theorem_13_2_caseBData_bg_classifier_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceOrig⟩

public theorem section13_theorem_13_2_caseBData_bg_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q := by
  have hsourceOrig := _hsource
  have hsourceSwap :=
    section13_hypothesis_13_1_sourceData_swap (G := G) hsourceOrig
  have hFusionS : ∀ {U' W1' W2' : Subgroup G},
      Section8.typePDefinitionData Smax P U' W1' W2' →
        theorem_13_2_typeCommonT6FusionData Smax P U' := by
    intro U' W1' W2' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig hP
  have hFusionT : ∀ {V' W2' W1' : Subgroup G},
      Section8.typePDefinitionData Tmax Q V' W2' W1' →
        theorem_13_2_typeCommonT6FusionData Tmax Q V' := by
    intro V' W2' W1' hP
    exact
      section13_theorem_13_2_typeCommonT6FusionData_of_sourceTypeP
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
        hsourceSwap hP
  rcases _hsource with
    ⟨hcase, hptypeS, hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar⟩
  rcases hcase with
    ⟨hWprod, hWcyc, hW1ne, hW2ne, hWnorm, hSmax, hTmax, hSMF, hTMF,
      hSeq, hTeq, hSdisj, hTdisj, hSTeq, hIIorT, _hStypes, _hTtypes,
      _hclass⟩
  have hT6S :=
    section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceOrig
  have hT6T :=
    section13_theorem_13_2_case_9_7_hypothesis92TypeCommonT6_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
      hsourceSwap
  have hPDataS : Section8.typePData Smax P U W1 W2 :=
    section13_typePData_of_typePDefinitionData_T6 hptypeS hT6S
  have hPDataT : Section8.typePData Tmax Q V W2 W1 :=
    section13_typePData_of_typePDefinitionData_T6 hptypeT hT6T
  have hSeq_bg : Smax = W1 ⊔ ambientDerivedSubgroup Smax := by
    simpa [sup_comm] using hSeq
  have hTeq_bg : Tmax = W2 ⊔ ambientDerivedSubgroup Tmax := by
    simpa [sup_comm] using hTeq
  have hSinf : ambientDerivedSubgroup Smax ⊓ W1 = ⊥ := by
    apply le_antisymm
    · intro x hx
      exact (Subgroup.disjoint_def.mp hSdisj) hx.1 hx.2
    · exact bot_le
  have hTinf : ambientDerivedSubgroup Tmax ⊓ W2 = ⊥ := by
    apply le_antisymm
    · intro x hx
      exact (Subgroup.disjoint_def.mp hTdisj) hx.1 hx.2
    · exact bot_le
  rcases hPDataS.2 with
    ⟨_hSHall, _hSPleDer, _hScomp, _hSunil, _hSW1norm, _hSW1cyc,
      _hSW1card, _hSPnotcyc, _hSsecond, _hSfitting, _hSfittingle,
      _hSW2le, _hSW2ne, _hSW2cyc, _hScentralizer, _hSnormHat,
      _hST6, hW2leSecond⟩
  rcases hPDataT.2 with
    ⟨_hTHall, _hTQleDer, _hTcomp, _hTunil, _hTW2norm, _hTW2cyc,
      _hTW2card, _hTQnotcyc, _hTsecond, _hTfitting, _hTfittingle,
      _hTW1le, _hTW1ne, _hTW1cyc, _hTcentralizer, _hTnormHat,
      _hTT6, hW1leSecond⟩
  rcases
    section13_theorem_13_2_caseBData_bg_hardFields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceOrig with
    ⟨hSnotI, hTnotI, hclassifier⟩
  have hIIorT_bg : section16TypeII Smax P ∨ section16TypeII Tmax Q := by
    rcases hIIorT with hII | hII
    · have hRankSource :=
        section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
          hsourceOrig hII
      exact Or.inl
        (section13_section16TypeII_of_source_typeII_with_fusionData
          hII hRankSource)
    · have hRankSource :=
        section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
          Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
          hsourceSwap hII
      exact Or.inr
        (section13_section16TypeII_of_source_typeII_with_fusionData
          hII hRankSource)
  have hStypes_bg :
      section16TypeII Smax P ∨ section16TypeIII Smax P ∨
        section16TypeIV Smax P ∨ section16TypeV Smax P := by
    rcases
      section13_theorem_13_2_case_9_7_hypothesis92BGTypes_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig with
      hII | hIII | hIV
    · exact Or.inl hII
    · exact Or.inr <| Or.inl hIII
    · exact Or.inr <| Or.inr <| Or.inl hIV
  have hTtypes_bg :
      section16TypeII Tmax Q ∨ section16TypeIII Tmax Q ∨
        section16TypeIV Tmax Q ∨ section16TypeV Tmax Q := by
    rcases
      section13_theorem_13_2_case_9_7_hypothesis92BGTypes_of_sourceContext
        Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c
        hsourceSwap with
      hII | hIII | hIV
    · exact Or.inl hII
    · exact Or.inr <| Or.inl hIII
    · exact Or.inr <| Or.inr <| Or.inl hIV
  exact ⟨hWprod, hWcyc, hW1ne, hW2ne, hWnorm, hSmax, hTmax, hSMF,
    hTMF, hSnotI, hTnotI, hSeq_bg, hTeq_bg, hSinf, hTinf, hW2leSecond,
    hW1leSecond, hSTeq, hclassifier, hIIorT_bg, hStypes_bg, hTtypes_bg,
    ⟨U, V, hPDataS.2, hPDataT.2⟩⟩

private theorem section13_theorem_13_2_typeII_section16TypeII_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hII : Section8.typeIIDefinitionData Smax P) :
    section16TypeII Smax P := by
  have hRankSource :=
    section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource _hII
  exact section13_section16TypeII_of_source_typeII_with_fusionData
    _hII hRankSource

public theorem section13_theorem_13_2_current_typeII_not_normalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeII : Section8.typeIIDefinitionData Smax P) :
    ¬ Subgroup.normalizer (U : Set G) ≤ Smax := by
  have hBgII : section16TypeII Smax P :=
    section13_theorem_13_2_typeII_section16TypeII_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource hTypeII
  have h92full :=
    section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  exact (h92full.typeIISource hBgII).2.1

private theorem section13_theorem_13_2_coherence911BridgeData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D Cprime : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h95 : Section9.Hypothesis_9_5 Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS Sfam) :
    Section9.theorem_9_11_hypothesis52BridgeData Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS Sfam := by
  classical
  constructor
  · exact _h95.hypothesis52b
  · intro K U8 Ms A R8 _h815 hfamily
    have hMin : IsMinCE G :=
      section13_theorem_13_2_global_isMinCE_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource
    have hSsource : nonkernelInducedFamily Smax (P ⊔ U) P Sfam := by
      rcases _hsource with
        ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
          _hUcard, _hVcard, hSfam, _hTail⟩
      exact hSfam
    rcases section13_theorem_13_2_hypothesis52FullData_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource with
      ⟨Ms52, _Abook52, d52, hPleMs52, hd52τ, _hSigmaAgree, _hLate⟩
    have hS8 : Section8.section8InducedNonkernelFamily Smax Ms52 Sfam :=
      section13_section8InducedNonkernelFamily_of_nonkernelInducedFamily_typeP
        _h95.hypothesis92.typePDefinitionData hPleMs52 hSsource hfamily.1
        (section13_nonkernelInducedFamily_conjugate_closed
          Smax (P ⊔ U) P Sfam hSsource)
    have h52d : Section5.hypothesis_5_2_statement Sfam d52.tau :=
      Section8.theorem_8_15_hypothesis_5_2_of_fullData hMin d52 hS8
    refine ⟨τS, ?_, ?_⟩
    · rwa [hd52τ] at h52d
    · intro X
      rfl

private theorem section13_theorem_13_2_typeIIElementaryConclusion_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hII : Section8.typeIIDefinitionData Smax P) :
    Section10.typeIIElementaryConclusion Smax P W1 W2 Sfam τS := by
  rcases section13_theorem_13_2_case_9_7_hypothesis95BotData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    ⟨Cprime, _hp, _hp_eq, h95, _hpdata⟩
  have hcaseBG :
      Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q :=
    section13_theorem_13_2_caseBData_bg_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  have htypeII : section16TypeII Smax P :=
    section13_theorem_13_2_typeII_section16TypeII_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource _hII
  haveI : IsMinCE G := by
    rcases _hsource with
      ⟨_h88, _hSP, _hTP, _hp, _hq, _hC, _hD, _hc, _hd, _hu, _hv,
        _hSfam, _hTfam, _hDadeS, _hDadeT, _hChar, _hDadeDiff, _hZeroDegree,
        _hConjIndex, _hConjBetaTau, _hChoice, hmin,
        _hFourSixS, _hFourSixT⟩
    exact hmin
  have hUcomm : IsMulCommutative U :=
    section13_theorem_13_2_currentU_commutative_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource
  have hCeq : C = subgroupCentralizerIn U P := by
    rcases _hsource with
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hC
  have hCU : C ≤ U := by
    rw [hCeq]
    exact inf_le_left
  have hCcomm : IsMulCommutative C := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply Subtype.ext
    letI : IsMulCommutative U := hUcomm
    exact setLike_mul_comm
      (s := U) (hCU x.property) (hCU y.property)
  haveI : IsMulCommutative C := hCcomm
  have hcommC : _root_.commutator C = ⊥ := commutator_eq_bot (G := C)
  have hCprimeBot : Cprime = (⊥ : Subgroup G) := by
    rw [h95.Cprime_eq_commutator, hcommC]
    simp
  have hkernel :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
        ((⊥ : Subgroup G) ⊔ Cprime) Sfam := by
    simpa [hCprimeBot] using h95.kernelInduced
  have hbridge :
      Section9.theorem_9_11_hypothesis52BridgeData Smax P U W1 W2
        (⊥ : Subgroup G) C Cprime τS Sfam :=
    section13_theorem_13_2_coherence911BridgeData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Cprime Sfam Tfam τS τT
      p q u v c d _hsource h95
  rcases Section10.theorem_10_11 W W1 W2 Smax Tmax P Q Smax P U
      (⊥ : Subgroup G) C Cprime Sfam τS hcaseBG with
    ⟨_hpW1, _hpW2, hconcl⟩
  exact hconcl hbridge h95 htypeII

private theorem section13_isElementaryAbelian_of_mulEquiv
    {A : Type u} {B : Type u} [Group A] [Group B]
    (p : ℕ)
    (e : A ≃* B) :
    IsElementaryAbelian p A →
      IsElementaryAbelian p B := by
  intro hElem
  letI : IsElementaryAbelian p A := hElem
  refine
    { toIsMulCommutative := { is_comm := Std.Commutative.mk ?_ }
      exponent_dvd_p := ?_ }
  · intro a b
    have hcomm : e.symm a * e.symm b = e.symm b * e.symm a := mul_comm' _ _
    apply_fun e at hcomm
    simpa [e.map_mul] using hcomm
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    have hxsrc : (e.symm x) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A) (e.symm x)
    apply_fun e at hxsrc
    simpa [map_pow] using hxsrc

private theorem section13_theorem_13_2_typeIII_P_fields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hIII : Section8.typeIIIDefinitionData Smax P) :
    IsElementaryAbelian p P ∧ Nat.card P = p ^ q := by
  have hsourceFull := _hsource
  rcases _hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hsourceTail⟩
  rcases section13_theorem_13_2_case_9_7_hypothesis95BotData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull with
    ⟨Cprime, hp, hp_eq, h95, hpdata⟩
  have hpdataFull := hpdata
  rcases hpdata with
    ⟨_hbot_le, _hP_le_S, _hbot_norm_S, hbot_norm_P, _hbot_lt,
      hquotElem, _hIIIIV⟩
  letI : ((⊥ : Subgroup G).subgroupOf P).Normal := hbot_norm_P
  have hbot_sub : (⊥ : Subgroup G).subgroupOf P = (⊥ : Subgroup P) := by
    rw [Subgroup.bot_subgroupOf]
  let e : P ⧸ (⊥ : Subgroup G).subgroupOf P ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hbot_sub).trans
      (QuotientGroup.quotientBot (G := P))
  have hPelem : IsElementaryAbelian p P := by
    rcases hquotElem with ⟨_hnorm, hElemQuot⟩
    have hPelem_hp : IsElementaryAbelian hp.val P :=
      section13_isElementaryAbelian_of_mulEquiv hp.val e hElemQuot
    simpa [hp_eq] using hPelem_hp
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull
  letI : IsMinCE G := hMin
  have hquotCard :
      Nat.card (P ⧸ (⊥ : Subgroup G).subgroupOf P) = hp.val ^ Nat.card W1 := by
    rcases Section9.theorem_9_6_source_core_sec9 Smax P U W1 W2
        (⊥ : Subgroup G) C Cprime τS Sfam hp h95 hpdataFull with
      ⟨_hUC, _hchief, _hWbar, hcard⟩
    exact hcard
  have hcardQuotP :
      Nat.card (P ⧸ (⊥ : Subgroup G).subgroupOf P) = Nat.card P :=
    Nat.card_congr e.toEquiv
  have hPcard : Nat.card P = p ^ q := by
    calc
      Nat.card P = Nat.card (P ⧸ (⊥ : Subgroup G).subgroupOf P) := hcardQuotP.symm
      _ = hp.val ^ Nat.card W1 := hquotCard
      _ = p ^ q := by rw [hp_eq, hq_card]
  exact ⟨hPelem, hPcard⟩

private theorem section13_theorem_13_2_PFieldsUpstreamData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_PFieldsUpstreamData Smax P W1 W2 Sfam τS p q := by
  rcases section13_theorem_13_2_typeAndUCurrentBranchData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    ⟨hbranch, _hcondition, _hUcomm⟩
  rcases hbranch with hII | hIII
  · exact Or.inl
      (section13_theorem_13_2_typeIIElementaryConclusion_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource hII)
  · rcases hIII with ⟨hIII, _hpq⟩
    exact Or.inr
      (section13_theorem_13_2_typeIII_P_fields_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        _hsource hIII)

private theorem section13_theorem_13_2_P_fields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
      IsElementaryAbelian p P ∧
      Nat.card P = p ^ q := by
  exact section13_theorem_13_2_P_fields_from_upstreamData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
    (section13_theorem_13_2_PFieldsUpstreamData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource)

private theorem section13_theorem_13_2_u_bound_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    u ≤ (p ^ q - 1) / (p - 1) := by
  exact section13_theorem_13_2_u_bound_from_branchData
    (section13_theorem_13_2_uBoundBranchData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource)

private def theorem_13_2_coherence911Data
    {G : Type u} [Group G] [Finite G]
    (Smax P U W1 W2 C : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G) :
    Prop :=
  ∃ Cprime : Subgroup G,
    Section9.theorem_9_11_hypothesis52BridgeData Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS Sfam ∧
    Section9.Hypothesis_9_5 Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS Sfam ∧
    Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
      ((⊥ : Subgroup G) ⊔ Cprime) Sfam

private theorem section13_theorem_13_2_coherence_from_911Data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax P U W1 W2 C : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (hdata : theorem_13_2_coherence911Data Smax P U W1 W2 C Sfam τS) :
    Section6.coherentFamily Sfam τS := by
  rcases hdata with ⟨Cprime, hbridge, h95, hkernel⟩
  have hcoh : Section9.coherentFamilyForT Smax Sfam τS :=
    Section9.theorem_9_11_of_hypothesis52BridgeData Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS
      Sfam Sfam hbridge h95 hkernel
  simpa [Section9.coherentFamilyForT] using hcoh

private theorem section13_theorem_13_2_coherence911KernelFamily_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D Cprime : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h95 : Section9.Hypothesis_9_5 Smax P U W1 W2
      (⊥ : Subgroup G) C Cprime τS Sfam) :
    Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
      ((⊥ : Subgroup G) ⊔ Cprime) Sfam := by
  have hUcomm : IsMulCommutative U :=
    section13_theorem_13_2_currentU_commutative_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d _hsource
  have hCeq : C = subgroupCentralizerIn U P := by
    rcases _hsource with
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation⟩
    exact hC
  have hCU : C ≤ U := by
    rw [hCeq]
    exact inf_le_left
  have hCcomm : IsMulCommutative C := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply Subtype.ext
    letI : IsMulCommutative U := hUcomm
    exact setLike_mul_comm
      (s := U) (hCU x.property) (hCU y.property)
  haveI : IsMulCommutative C := hCcomm
  have hcommC : _root_.commutator C = ⊥ := commutator_eq_bot (G := C)
  have hbot : Cprime = (⊥ : Subgroup G) := by
    rw [_h95.Cprime_eq_commutator, hcommC]
    simp
  simpa [hbot] using
    (section13_theorem_13_2_case_9_7_kernelInducedFamilyBot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource)

private theorem section13_theorem_13_2_coherence911Data_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_2_coherence911Data Smax P U W1 W2 C Sfam τS := by
  rcases section13_theorem_13_2_case_9_7_hypothesis95BotData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource with
    ⟨Cprime, _hp, _hp_eq, h95, _hred⟩
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  have hkernel :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) P
        ((⊥ : Subgroup G) ⊔ Cprime) Sfam :=
    section13_theorem_13_2_coherence911KernelFamily_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Cprime Sfam Tfam τS τT
      p q u v c d _hsource h95
  have hbridge :
      Section9.theorem_9_11_hypothesis52BridgeData Smax P U W1 W2
        (⊥ : Subgroup G) C Cprime τS Sfam :=
    section13_theorem_13_2_coherence911BridgeData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Cprime Sfam Tfam τS τT
      p q u v c d _hsource h95
  exact ⟨Cprime, hbridge, h95, hkernel⟩

private theorem section13_theorem_13_2_coherence_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section6.coherentFamily Sfam τS := by
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  letI : IsMinCE G := hMin
  exact section13_theorem_13_2_coherence_from_911Data
    (section13_theorem_13_2_coherence911Data_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource)


private theorem section13_typeP_not_frobeniusWithKernel
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    ¬ Section7.frobeniusWithKernel M MF := by
  classical
  intro hfrob
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, hW1Hall, hMcomp, _hUleDer,
      _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, hW2le, _hW2cyc, hW2ne, hCentralizer, _hNormalizer⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne with ⟨xW1, hxW1ne⟩
  let x : G := xW1
  have hxW1 : x ∈ W1 := xW1.property
  have hxne : x ≠ 1 := by
    intro hx
    exact hxW1ne (Subtype.ext hx)
  have hxM : x ∈ M := hW1Hall.1 hxW1
  have hMFleDer : MF ≤ ambientDerivedSubgroup M := hDerComp.1
  have hxnotMF : x ∉ MF := by
    intro hxMF
    have hxDer : x ∈ ambientDerivedSubgroup M := hMFleDer hxMF
    have hxBot : x ∈ (⊥ : Subgroup G) :=
      hMcomp.2.2.2.le_bot ⟨hxDer, hxW1⟩
    exact hxne (by simpa using hxBot)
  have hcentBot : Section2.centralizerIn MF x = ⊥ := by
    rcases hfrob with ⟨hHL, hHnormal, R, hcomp, hHne, hRne, hfixedR⟩
    exact
      Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
        (L0 := M) (H := MF)
        ⟨hHL, hHnormal, R, hcomp, hHne, hRne, hfixedR⟩ x hxM hxnotMF
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨yW2, hyW2ne⟩
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  have hyMF : y ∈ MF := (hW2le hyW2).1
  have hyCentDer : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
    simpa [hCentralizer x hxW1 hxne] using hyW2
  have hyCentMF : y ∈ Section2.centralizerIn MF x := by
    exact ⟨hyMF, hyCentDer.2⟩
  have hyBot : y ∈ (⊥ : Subgroup G) := by
    simpa [hcentBot] using hyCentMF
  exact hyne (by simpa using hyBot)

private theorem section13_typeP_not_section8FrobeniusGroupWithKernel
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    ¬ Section8.section8FrobeniusGroupWithKernel M MF := by
  intro hfrob
  rcases hfrob with ⟨E, hcomp, hfrobJoin⟩
  have hfrob7 : Section7.frobeniusWithKernel M MF :=
    Section12.frobeniusWithKernel_of_section12FrobeniusJoinWithKernel
      hcomp (Section12.section16MFSubgroup_subgroupOf_normal hP.1) hfrobJoin
  exact section13_typeP_not_frobeniusWithKernel hP hfrob7

private theorem section13_typeI_support_branch_contradiction_of_theorem_12_7
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF X : Subgroup G} {Xset : Set G} {x : G} {L LF : Subgroup G}
    (hSupp : Section8.supportConclusionDataSource M MF X Xset x L LF)
    (hTypeI : Section8.typeIDefinitionData L LF)
    (hxAminus :
      x ∈ Section8.section8CentralizerUnion L LF \ Section8.a1Set LF) :
    False := by
  rcases hSupp with
    ⟨hLmax, hLF, _hUnique, _hSemiL, _hSemiC, _hCoprime, _hCases⟩
  have hfrob : Section7.frobeniusWithKernel L LF :=
    Section12.theorem_12_7 L LF hLmax hLF hTypeI
  have hxTypeIA : x ∈ Section12.typeIASet L LF := by
    simpa [Section12.typeIASet_eq_section8CentralizerUnion L LF] using hxAminus.1
  have hxSharp : x ∈ section16NonidentityElements (LF : Set G) := by
    simpa [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L LF hfrob]
      using hxTypeIA
  have hxA1 : x ∈ Section8.a1Set LF := by
    simpa [Section8.a1Set] using hxSharp
  exact hxAminus.2 hxA1

public theorem section13_theorem_13_2_H_punctured_tiNormalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet H) Smax := by
  classical
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  letI : IsMinCE G := hMin
  have hHfit : H = section8FittingSubgroup Smax := by
    rcases hsource with
      ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd, _hUcard,
        _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
    calc
      H = P ⊔ C := hH
      _ = P ⊔ subgroupCentralizerIn U P := by rw [hC]
      _ = section8FittingSubgroup Smax := by
        exact (Section8.theorem_8_5_a Smax P U W1 W2 hptypeS).symm
  have hfitTI :
      section16TISubset
        (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) := by
    rcases
      section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource with
      ⟨_hUne, _hW1prime, hFittingTI⟩
    exact hFittingTI
  have hnormFit :
      Subgroup.normalizer
        (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) =
          Smax := by
    rcases hsource with
      ⟨hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
        _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
    rcases hcase with
      ⟨_hWprod, _hWcyc, _hW1ne_case, _hW2ne_case, _hWnorm, hSmax, _hTmax,
        _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
        _hStypes, _hTtypes, _hclass⟩
    rcases hptypeS with
      ⟨_hSMFsrc, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
        _hW1normU, _hcompDU, _hPnotCyc, _hSecondLe, hFittingEq, _hFittingLeD,
        hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
    have hW2leF : W2 ≤ section8FittingSubgroup Smax := by
      intro x hx
      rw [← hFittingEq]
      exact (show P ≤ P ⊔ subgroupCentralizerIn Smax P from le_sup_left)
        ((hW2le hx).1)
    have hW2_card_ne_one : Nat.card W2 ≠ 1 := by
      intro hcard
      exact hW2ne ((Subgroup.eq_bot_iff_card (H := W2)).2 hcard)
    rcases Nat.exists_prime_and_dvd (n := Nat.card W2) hW2_card_ne_one with
      ⟨r, hrprime, hrdiv⟩
    let rP : Nat.Primes := ⟨r, hrprime⟩
    have hrW2 : rP ∈ subgroupPrimeSet W2 := by
      rw [subgroupPrimeSet]
      change r ∣ Nat.card W2
      exact hrdiv
    have hrF : rP ∈ subgroupPrimeSet (section8FittingSubgroup Smax) :=
      section8_subgroupPrimeSet_mono hW2leF hrW2
    have hSmax8 : Smax ∈ section8MaximalSubgroups G := by
      simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hSmax
    have hnormF : Subgroup.normalizer (section8FittingSubgroup Smax : Set G) = Smax :=
      section8_normalizer_fittingSubgroup_eq (G := G) (M := Smax) (q := rP)
        hSmax8 hrF
    have hsharp_norm :
        Subgroup.normalizer
            (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) =
          Subgroup.normalizer (section8FittingSubgroup Smax : Set G) := by
      apply le_antisymm
      · intro g hg
        change ∀ x : G,
          x ∈ section16NonidentityElements (section8FittingSubgroup Smax : Set G) ↔
            g * x * g⁻¹ ∈
              section16NonidentityElements (section8FittingSubgroup Smax : Set G) at hg
        change ∀ x : G, x ∈ section8FittingSubgroup Smax ↔
          g * x * g⁻¹ ∈ section8FittingSubgroup Smax
        intro x
        constructor
        · intro hxH
          by_cases hx1 : x = 1
          · simp [hx1]
          · have hxSharp :
                x ∈ section16NonidentityElements
                  (section8FittingSubgroup Smax : Set G) := ⟨hxH, hx1⟩
            exact ((hg x).1 hxSharp).1
        · intro hxConjH
          by_cases hx1 : x = 1
          · simp [hx1]
          · have hxConj_ne : g * x * g⁻¹ ≠ 1 := by
              intro heq
              apply hx1
              have heq' := congrArg (fun y : G => g⁻¹ * y * g) heq
              simpa [mul_assoc] using heq'
            have hxConjSharp :
                g * x * g⁻¹ ∈ section16NonidentityElements
                  (section8FittingSubgroup Smax : Set G) := ⟨hxConjH, hxConj_ne⟩
            exact ((hg x).2 hxConjSharp).1
      · intro g hg
        change ∀ x : G, x ∈ section8FittingSubgroup Smax ↔
          g * x * g⁻¹ ∈ section8FittingSubgroup Smax at hg
        change ∀ x : G,
          x ∈ section16NonidentityElements (section8FittingSubgroup Smax : Set G) ↔
            g * x * g⁻¹ ∈
              section16NonidentityElements (section8FittingSubgroup Smax : Set G)
        intro x
        constructor
        · intro hx
          refine ⟨(hg x).1 hx.1, ?_⟩
          intro heq
          exact hx.2 (by
            have heq' := congrArg (fun y : G => g⁻¹ * y * g) heq
            simpa [mul_assoc] using heq')
        · intro hx
          refine ⟨(hg x).2 hx.1, ?_⟩
          intro hx1
          exact hx.2 (by simp [hx1])
    simpa [hsharp_norm] using hnormF
  have hTI : section16TISubset (Section7.puncturedSubgroupSet H) := by
    simpa [hHfit, Section7.puncturedSubgroupSet, section16NonidentityElements]
      using hfitTI
  have hnorm : Subgroup.normalizer (Section7.puncturedSubgroupSet H) = Smax := by
    simpa [hHfit, Section7.puncturedSubgroupSet, section16NonidentityElements]
      using hnormFit
  exact ⟨hTI, hnorm⟩

private theorem section13_elementCentralizer_le_of_section16TI
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {M : Subgroup G} {a : G}
    (hTI : section16TISubsetWithNormalizer A M)
    (ha : a ∈ A) (ha1 : a ≠ 1) :
    Section2.elementCentralizer a ≤ M := by
  intro g hg
  have hga : g * a * g⁻¹ = a := by
    have hcomm : a * g = g * a := by
      simpa [Section2.elementCentralizer, Subgroup.mem_centralizer_iff] using hg
    calc
      g * a * g⁻¹ = a * g * g⁻¹ := by rw [hcomm]
      _ = a := by simp [mul_assoc]
  have haConj : a ∈ section16ConjugateSet A g := ⟨a, ha, hga.symm⟩
  rcases hTI.1 g with hconj | hsmall
  · have hgNormA : g ∈ Subgroup.normalizer A := by
      change ∀ x : G, x ∈ A ↔ g * x * g⁻¹ ∈ A
      intro x
      constructor
      · intro hx
        have hxconj : g * x * g⁻¹ ∈ section16ConjugateSet A g :=
          ⟨x, hx, rfl⟩
        simpa [hconj] using hxconj
      · intro hx
        have hxconj : g * x * g⁻¹ ∈ section16ConjugateSet A g := by
          simpa [hconj] using hx
        rcases hxconj with ⟨y, hy, hyx⟩
        have hxy : x = y := by
          calc
            x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hyx]
            _ = y := by group
        simpa [hxy] using hy
    simpa [hTI.2] using hgNormA
  · have haone_mem : a ∈ ({1} : Set G) := hsmall ⟨ha, haConj⟩
    exact False.elim (ha1 (by simpa using haone_mem))

public theorem section13_dadeTransform_eq_inducedCFLinear_of_section16TI
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (M : Subgroup G) (R : G → Subgroup G)
    (hTI : section16TISubsetWithNormalizer A M)
    (h22 : Section2.Hypothesis2 A M R)
    (χ : Section1.ClassFunction M)
    (hχ : Section2.CFOn M A χ) :
    Section2.dadeTransform R h22.subset_L χ =
      Section1.inducedCFLinear M χ := by
  classical
  have hconst :
      ∀ ψ : Theory.Character.ConjClassFunction G,
        Theory.Character.IsIrreducibleConjCharacter ψ →
          ∀ ⦃a h0 : G⦄, a ∈ A → h0 ∈ R a →
            Section1.ofConjClassFunction ψ (a * h0) =
              Section1.ofConjClassFunction ψ a := by
    intro ψ _hψ a h0 ha hh0
    have hcent_le_M : Section2.elementCentralizer a ≤ M :=
      section13_elementCentralizer_le_of_section16TI hTI ha
        (h22.subset_punctured a ha)
    have hprod := h22.centralizer_eq_product ha
    have hRa_bot : R a = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxR
      have hxCent : x ∈ Section2.elementCentralizer a := hprod.left_le hxR
      have hxM : x ∈ M := hcent_le_M hxCent
      have hxInf : x ∈ R a ⊓ Section2.centralizerIn M a :=
        ⟨hxR, ⟨hxM, hxCent⟩⟩
      simpa [hprod.inf_eq_bot] using hxInf
    have hh0bot : h0 ∈ (⊥ : Subgroup G) := by
      simpa [hRa_bot] using hh0
    have hh0one : h0 = 1 := Subgroup.mem_bot.mp hh0bot
    simp [hh0one]
  have hdade :
      Section2.dadeTransform R h22.subset_L χ = Section1.inducedCF M χ :=
    Section12.dadeTransform_eq_inducedCF_of_irreducible_dade_coset_constancy_on_support
      A A M R subset_rfl h22 h22.subset_L χ hχ hconst
  simpa [Section1.inducedCFLinear_apply] using hdade


private def section13_bookAZeroData
    {G : Type u} [Group G] [Finite G]
    (M MF _ W1 W2 : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (A0book : Set G) (H_A0 : G → Subgroup G) : Prop :=
  ∃ Ms : Subgroup G, ∃ Abook A1book : Set G,
    ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book ∧
      Abook = Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms ∧
      A0book =
        Abook ∪ section16ConjugatesOfSetBySet
          (section16HatW W1 W2) (M : Set G) ∧
      MF ≤ Ms ∧
      (∀ l : M,
        (l : G) ∈
          section16NonidentityElements ((Ms : Subgroup G) : Set G) →
            (l : G) ∈ A0book) ∧
      ∀ α : Section1.ClassFunction M,
        τ α = Section2.dadeTransform H_A0 hA0M.subset_L α

private theorem section13_bookAZeroData_of_typePFourSix_source
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_hP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    ∃ A0book : Set G, ∃ H_A0 : G → Subgroup G,
      section13_bookAZeroData M MF U W1 W2 τ A0book H_A0 := by
  classical
  rcases hFourSix with
    ⟨I, instI, decI, J, instJ, decJ, W46, A, A0, i0, j0, μ, δSign, ω, σ,
      _hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, hBookSource⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hBookSource with
    ⟨Ms, Abook, A0book, A1book, H_A0, hA0M, hNotationBook, hAbook,
      hA0book, hMFleMs, hQVU, hτDade⟩
  exact
    ⟨A0book, H_A0, Ms, Abook, A1book, hA0M, hNotationBook, hAbook,
      hA0book, hMFleMs, hQVU, hτDade⟩

private theorem section13_typePFAZeroSet_subset_bookAZero_of_bookData
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {A0book : Set G} {H_A0 : G → Subgroup G}
    (hBook : section13_bookAZeroData M MF U W1 W2 τ A0book H_A0) :
    typePFAZeroSet M W1 W2 MF ⊆ A0book := by
  rcases hBook with
    ⟨Ms, Abook, _A1book, _hA0M, _hNotation, hAbook, hA0book, hMFleMs,
      _hMsSharp, _hτDade⟩
  intro x hx
  rw [typePFAZeroSet] at hx
  rw [hA0book, hAbook]
  rcases hx with hxA | hxHat
  · left
    rcases hxA with ⟨y, hyMF, hxCent⟩
    exact ⟨y, ⟨hMFleMs hyMF.1, hyMF.2⟩, hxCent⟩
  · exact Or.inr hxHat

private theorem section13_typeP_ASet_subset_bookAZero_of_bookData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {A0book : Set G} {H_A0 : G → Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hTypeCases :
      Section8.typeIIDefinitionData M MF ∨
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF)
    (hTypeIIBg :
      Section8.typeIIDefinitionData M MF → section16TypeII M MF)
    (hBook : section13_bookAZeroData M MF U W1 W2 τ A0book H_A0) :
    section16ASet M U ⊆ A0book := by
  classical
  have hPcopy := hP
  rcases hPcopy with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleDer,
      _hUnil, _hW1norm, _hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hMsigmaLeDer : section10Msigma M ≤ ambientDerivedSubgroup M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨y, (theorem_10_2_c (G := G) hM).2 hy, rfl⟩
  rcases hBook with
    ⟨Ms, Abook, _A1book, _hA0M, hNotationBook, _hAbook,
      hA0book, _hMFleMs, hMsSharp, _hτDade⟩
  rcases hTypeCases with hII | hLate
  · have hMsEq : Ms = MF :=
      Section8.msChoiceSource_eq_mf_of_typeII hNotationBook.2.2.1 hII
    subst Ms
    have hASetSubAbook : section16ASet M U ⊆ Abook :=
      Section8.typeII_section16ASet_subset_notation_A_source_data
        hM hMF (hTypeIIBg hII) hII hP hNotationBook
    intro x hx
    rw [hA0book]
    exact Or.inl (hASetSubAbook hx)
  · have hMsEq : Ms = ambientDerivedSubgroup M :=
      Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
        hNotationBook hLate
    intro x hx
    rcases Set.mem_mul.mp hx.2.1 with ⟨u0, huU, s0, hsSigma, hxEq⟩
    have hxDer : x ∈ ambientDerivedSubgroup M := by
      rw [← hxEq]
      exact (ambientDerivedSubgroup M).mul_mem
        (hUleDer huU) (hMsigmaLeDer hsSigma)
    let l : M := ⟨x, hx.1.1⟩
    apply hMsSharp l
    constructor
    · simpa [hMsEq, l] using hxDer
    · simpa [l] using hx.2.2

private theorem section13_book_AZero_TI_of_typeP_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G} {Abook A0book A1book : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (hAbook : Abook =
      Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hA0book :
      A0book =
        Abook ∪ section16ConjugatesOfSetBySet
          (section16HatW W1 W2) (M : Set G))
    (hMFleMs : MF ≤ Ms)
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    section16TISubsetWithNormalizer A0book M := by
  classical
  have hPfull := hP
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer,
      _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, hW2le, _hW2cyc, hW2ne, _hCentralizer, _hNormalizer⟩
  rcases hMF.1 with ⟨hMFleM, hMFnorm, _hMFnil, _hMFHall⟩
  have hNotationFull := hNotation
  rcases hNotation with ⟨_hM, _hMFsrc, hMs, _hA1, _hCases⟩
  have h13 :=
    Section8.theorem_8_13 M MF Ms Abook A0book A1book A0book
      (by infer_instance) hNotationFull (Or.inr rfl)
  have hDempty : ∀ x : G, x ∈ Section8.section8DSet M A0book → False := by
    intro x hxD
    rcases h13.2.2.1 x hxD with ⟨L, hLmem, _hLuniq⟩
    rcases h13.2.2.2 x hxD L hLmem with ⟨LF, hSupp⟩
    have hSuppFull := hSupp
    rcases hSupp with
      ⟨_hLmax, _hLF, _hUnique, _hSemiL, _hSemiC, _hCoprime, hCases⟩
    rcases hCases with hTypeI | hTypeII
    · exact
        section13_typeI_support_branch_contradiction_of_theorem_12_7
          (G := G) hSuppFull hTypeI.1 hTypeI.2
    · exact section13_typeP_not_section8FrobeniusGroupWithKernel
        hPfull hTypeII.2.2
  let Dsub : Subgroup G := ambientDerivedSubgroup M
  have hDleM : Dsub ≤ M := by
    simpa [Dsub] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDnorm : (Dsub.subgroupOf M).Normal := by
    simpa [Dsub] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hMnormD : M ≤ Subgroup.normalizer (Dsub : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).1 hDnorm
  have hMnormMF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnorm
  have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hTypeI, _hnII, _hnIII, _hnIV, _hnV, hMs_eq⟩
      simpa [hMs_eq] using hMnormMF
    · rcases hII with ⟨_hnI, _hTypeII, _hnIII, _hnIV, _hnV, hMs_eq⟩
      simpa [hMs_eq] using hMnormMF
    · rcases hIII with ⟨_hnI, _hnII, _hTypeIII, _hnIV, _hnV, hMs_eq⟩
      simpa [hMs_eq, Dsub] using hMnormD
    · rcases hIV with ⟨_hnI, _hnII, _hnIII, _hTypeIV, _hnV, hMs_eq⟩
      simpa [hMs_eq, Dsub] using hMnormD
    · rcases hV with ⟨_hnI, _hnII, _hnIII, _hnIV, _hTypeV, hMs_eq⟩
      simpa [hMs_eq] using hMnormMF
  have hMnormA :
      M ≤ Subgroup.normalizer Abook := by
    have hraw :=
      Section8.theorem_8_16_le_normalizer_centralizerUnion
        (G := G) (M := M) (C := Dsub) (H := Ms) hMnormD hMnormMs
    simpa [Dsub, hAbook] using hraw
  have hMnormHat :
      M ≤ Subgroup.normalizer
        (section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)) :=
    Section8.theorem_8_16_le_normalizer_conjugates_by_M
      (G := G) (M := M) (X := section16HatW W1 W2)
  have hMnormA0 :
      M ≤ Subgroup.normalizer A0book := by
    have hraw :=
      Section8.theorem_8_16_le_normalizer_union
        (G := G) (M := M)
        (X := Abook)
        (Y := section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
        hMnormA hMnormHat
    simpa [hA0book] using hraw
  have hXne : ∃ x : G, x ∈ A0book ∧ x ≠ 1 := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨yW2, hyW2ne⟩
    let y : G := yW2
    have hyW2 : y ∈ W2 := yW2.property
    have hyne : y ≠ 1 := by
      intro hy
      exact hyW2ne (Subtype.ext hy)
    have hyMF : y ∈ MF := (hW2le hyW2).1
    have hyDer : y ∈ ambientDerivedSubgroup M := hDerComp.1 hyMF
    have hyA : y ∈ Abook := by
      rw [hAbook]
      refine ⟨y, ⟨hMFleMs hyMF, hyne⟩, ?_⟩
      exact ⟨⟨hyDer, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, hyne⟩
    refine ⟨y, ?_, hyne⟩
    rw [hA0book]
    exact Or.inl hyA
  have hcent :
      ∀ x : G, x ∈ A0book → x ≠ 1 →
        Subgroup.centralizer ({x} : Set G) ≤ M := by
    intro x hx _hxne
    by_cases hle : Subgroup.centralizer ({x} : Set G) ≤ M
    · exact hle
    · exact False.elim (hDempty x ⟨hx, hle⟩)
  exact
    Section8.theorem_8_16_tiWithNormalizer_of_fusion_centralizers
      (G := G) (M := M) (X := A0book)
      hMnormA0 hXne h13.1 hcent

private theorem section13_book_AZero_TI_of_typePFourSix_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (_hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ)
    {A0book : Set G} {H_A0 : G → Subgroup G}
    (hBook : section13_bookAZeroData M MF U W1 W2 τ A0book H_A0) :
    section16TISubsetWithNormalizer A0book M := by
  rcases hBook with
    ⟨Ms, Abook, A1book, _hA0M, hNotation, hAbook, hA0book, hMFleMs,
      _hQVU, _hτDade⟩
  exact
    section13_book_AZero_TI_of_typeP_source (G := G) (M := M) (MF := MF)
      (Ms := Ms) (U := U) (W1 := W1) (W2 := W2) (Abook := Abook)
      (A0book := A0book) (A1book := A1book)
      hNotation hAbook hA0book hMFleMs hP

private theorem section13_agreesWithInductionOnTypeP_AZero_of_typePFourSix_TI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    ∀ χ : Section1.ClassFunction M,
      Section2.CFOn M (typePFAZeroSet M W1 W2 MF) χ →
        τ χ = Section1.inducedCFLinear M χ := by
  classical
  rcases section13_bookAZeroData_of_typePFourSix_source
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (τ := τ) hP hFourSix with
    ⟨A0book, H_A0, hBook⟩
  have hBookFull := hBook
  rcases hBook with
    ⟨_Ms, _Abook, _A1book, hA0M, _hNotation, _hAbook, _hA0book,
      _hMFleMs, _hMsSharp, hτDade⟩
  have hTI : section16TISubsetWithNormalizer A0book M :=
    section13_book_AZero_TI_of_typePFourSix_source
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (τ := τ) hP hFourSix hBookFull
  have hsub : typePFAZeroSet M W1 W2 MF ⊆ A0book :=
    section13_typePFAZeroSet_subset_bookAZero_of_bookData hBookFull
  intro χ hχ
  have hχbook : Section2.CFOn M A0book χ := by
    refine ⟨hχ.1, ?_⟩
    intro x hxA0
    exact hχ.2 x (fun hx => hxA0 (hsub hx))
  calc
    τ χ = Section2.dadeTransform H_A0 hA0M.subset_L χ := hτDade χ
    _ = Section1.inducedCFLinear M χ :=
      section13_dadeTransform_eq_inducedCFLinear_of_section16TI
        A0book M H_A0 hTI hA0M χ hχbook

private theorem section13_agreesWithInductionOnBookAZero_of_typePFourSix_TI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hTypeCases :
      Section8.typeIIDefinitionData M MF ∨
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF)
    (hTypeIIBg :
      Section8.typeIIDefinitionData M MF → section16TypeII M MF)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hFourSix : typePFourSixTauSourceData M MF U W1 W2 τ) :
    agreesWithInductionOnBookAZero M MF U W1 W2 τ := by
  classical
  rcases section13_bookAZeroData_of_typePFourSix_source
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (τ := τ) hP hFourSix with
    ⟨A0book, H_A0, hBook⟩
  rcases hBook with
    ⟨Ms, Abook, A1book, hA0M, hNotation, hAbook, hA0book, hMFleMs,
      hQVU, hτDade⟩
  have hBook' : section13_bookAZeroData M MF U W1 W2 τ A0book H_A0 :=
    ⟨Ms, Abook, A1book, hA0M, hNotation, hAbook, hA0book, hMFleMs, hQVU,
      hτDade⟩
  have hTI : section16TISubsetWithNormalizer A0book M :=
    section13_book_AZero_TI_of_typePFourSix_source
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (τ := τ) hP hFourSix hBook'
  have hTypePSub : typePFAZeroSet M W1 W2 MF ⊆ A0book :=
    section13_typePFAZeroSet_subset_bookAZero_of_bookData hBook'
  have hFittingSub :
      ∀ l : M,
        (l : G) ∈
            section16NonidentityElements (section8FittingSubgroup M : Set G) →
          (l : G) ∈ A0book := by
    intro l hl
    exact hTypePSub
      (fittingPunctured_subset_typePFAZeroSet_of_typePDefinitionData hP hl)
  have hASetSub : section16ASet M U ⊆ A0book :=
    section13_typeP_ASet_subset_bookAZero_of_bookData
      hM hP hTypeCases hTypeIIBg hBook'
  refine ⟨Ms, A0book, H_A0, hA0M, hNotation.2.2.1, hTI, hQVU,
    hFittingSub, hASetSub, hτDade, ?_⟩
  intro χ hχ
  calc
    τ χ = Section2.dadeTransform H_A0 hA0M.subset_L χ := hτDade χ
    _ = Section1.inducedCFLinear M χ :=
      section13_dadeTransform_eq_inducedCFLinear_of_section16TI
        A0book M H_A0 hTI hA0M χ hχ

private theorem section13_theorem_13_2_tau_agreesWithInductionOnTypeP_AZero_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ χ : Section1.ClassFunction Smax,
      Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) χ →
        τS χ = Section1.inducedCFLinear Smax χ := by
  classical
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  letI : IsMinCE G := hMin
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, hFourSixS, _hFourSixT⟩
  exact section13_agreesWithInductionOnTypeP_AZero_of_typePFourSix_TI
    Smax P U W1 W2 τS hptypeS hFourSixS

private theorem section13_theorem_13_2_agreesWithInductionOnBookAZero_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    agreesWithInductionOnBookAZero Smax P U W1 W2 τS := by
  classical
  have hsourceFull := hsource
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  letI : IsMinCE G := hMin
  have hSmax : Smax ∈ section9MaximalSubgroups G :=
    section13_theorem_13_2_Smax_maximal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsourceFull
  rcases hsource with
    ⟨hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax,
      _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII,
      hSTypeCases, _hTTypeCases, _hCover⟩
  have hTypeIIBg :
      Section8.typeIIDefinitionData Smax P → section16TypeII Smax P := by
    intro hII
    exact section13_section16TypeII_of_source_typeII_with_fusionData hII
      (section13_theorem_13_2_typeIIRankSourceData_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceFull hII)
  exact section13_agreesWithInductionOnBookAZero_of_typePFourSix_TI
    Smax P U W1 W2 τS hSmax hSTypeCases hTypeIIBg hptypeS hFourSixS

private theorem section13_theorem_13_2_tau_agreesWithInductionFields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    agreesWithInductionOnAZero Smax P U W1 W2 τS ∧
      agreesWithInductionOnBookAZero Smax P U W1 W2 τS := by
  refine ⟨⟨trivial,
    section13_theorem_13_2_tau_agreesWithInductionOnTypeP_AZero_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource⟩,
    section13_theorem_13_2_agreesWithInductionOnBookAZero_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource⟩

private theorem section13_theorem_13_2_tau_agreesWithInductionOnAZero_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    agreesWithInductionOnAZero Smax P U W1 W2 τS := by
  exact
    (section13_theorem_13_2_tau_agreesWithInductionFields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource).1

/-- The source-selected book `A₀` contains the exact Type-P carrier and carries
the Dade transform defining `τS`. -/
public theorem theorem_13_2_typePFAZero_dadePackage
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∃ A0book : Set G, ∃ H_A0 : G → Subgroup G,
      ∃ hA0M : Section2.Hypothesis2 A0book Smax H_A0,
        typePFAZeroSet Smax W1 W2 P ⊆ A0book ∧
          ∀ α : Section1.ClassFunction Smax,
            τS α = Section2.dadeTransform H_A0 hA0M.subset_L α := by
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, hFourSixS, _hFourSixT⟩
  rcases section13_bookAZeroData_of_typePFourSix_source
      (M := Smax) (MF := P) (U := U) (W1 := W1) (W2 := W2)
      (τ := τS) hptypeS hFourSixS with
    ⟨A0book, H_A0, hBook⟩
  have hBookFull := hBook
  rcases hBook with
    ⟨_Ms, _Abook, _A1book, hA0M, _hNotation, _hAbook, _hA0book,
      _hMFleMs, _hMsSharp, hτDade⟩
  exact ⟨A0book, H_A0, hA0M,
    section13_typePFAZeroSet_subset_bookAZero_of_bookData hBookFull,
    hτDade⟩

public theorem theorem_13_2_agreesWithInductionOnBookAZero
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    agreesWithInductionOnBookAZero Smax P U W1 W2 τS := by
  exact
    (section13_theorem_13_2_tau_agreesWithInductionFields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource).2

private theorem section13_theorem_13_2_coherence_and_AZero_fields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
      Section6.coherentFamily Sfam τS ∧
      agreesWithInductionOnBookAZero Smax P U W1 W2 τS ∧
      agreesWithInductionOnAZero Smax P U W1 W2 τS := by
  exact ⟨
    section13_theorem_13_2_coherence_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_agreesWithInductionOnBookAZero_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource,
    section13_theorem_13_2_tau_agreesWithInductionOnAZero_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource⟩

private theorem section13_theorem_13_2_remaining_fields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    (Section8.typeIIDefinitionData Smax P ∨ Section8.typeIIIDefinitionData Smax P) ∧
      (q < p → Section8.typeIIDefinitionData Smax P) ∧
      IsMulCommutative U ∧
      section12FrobeniusJoinWithKernel U W1 ∧
      IsElementaryAbelian p P ∧
      Nat.card P = p ^ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧
      Section6.coherentFamily Sfam τS ∧
      agreesWithInductionOnBookAZero Smax P U W1 W2 τS ∧
      agreesWithInductionOnAZero Smax P U W1 W2 τS := by
  rcases section13_theorem_13_2_type_and_U_fields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨htype, htypeLarge, hUcomm, hfrobUW1⟩
  rcases section13_theorem_13_2_P_fields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨hPelem, hPcard⟩
  have huBound : u ≤ (p ^ q - 1) / (p - 1) :=
    section13_theorem_13_2_u_bound_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  rcases section13_theorem_13_2_coherence_and_AZero_fields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨hcoh, hBook, hTau⟩
  exact ⟨htype, htypeLarge, hUcomm, hfrobUW1, hPelem, hPcard, huBound,
    hcoh, hBook, hTau⟩

/-- Proof placeholder for `theorem_13_2_statement`. -/
public theorem theorem_13_2
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
      section16MFSubgroup Smax P ∧
        (Section8.typeIIDefinitionData Smax P ∨ Section8.typeIIIDefinitionData Smax P) ∧
        (q < p → Section8.typeIIDefinitionData Smax P) ∧
        IsMulCommutative U ∧
        section12FrobeniusJoinWithKernel U W1 ∧
        IsElementaryAbelian p P ∧
        Nat.card P = p ^ q ∧
        u ≤ (p ^ q - 1) / (p - 1) ∧
        Section6.coherentFamily Sfam τS ∧
        agreesWithInductionOnBookAZero Smax P U W1 W2 τS ∧
        agreesWithInductionOnAZero Smax P U W1 W2 τS ∧
        (q < p → ¬ Subgroup.normalizer (U : Set G) ≤ Smax) := by
  intro hsource
  have hsourceOrig := hsource
  rcases hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWnorm, _hSmax, _hTmax, hSMF,
      _hTMF, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hTypeII,
      _hStypes, _hTtypes, _hmaxclass⟩
  rcases section13_theorem_13_2_remaining_fields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig with
    ⟨htype, htypeLarge, hUcomm, hfrobUW1, hPelem, hPcard, huBound,
      hcoh, hBook, hTau⟩
  have hnorm : q < p → ¬ Subgroup.normalizer (U : Set G) ≤ Smax := by
    intro hq_lt_p
    have hSrcII : Section8.typeIIDefinitionData Smax P := htypeLarge hq_lt_p
    have hBgII : section16TypeII Smax P :=
      section13_theorem_13_2_typeII_section16TypeII_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig hSrcII
    have h92full :=
      section13_theorem_13_2_case_9_7_hypothesis92_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
        hsourceOrig
    exact (h92full.typeIISource hBgII).2.1
  exact ⟨hSMF, htype, htypeLarge, hUcomm, hfrobUW1, hPelem, hPcard, huBound,
    hcoh, hBook, hTau, hnorm⟩
end CFSG.Section13
