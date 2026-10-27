module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_9

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section9

universe v
universe w
universe u

public theorem theorem_9_10_case_b_from_no_forbidden_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p q u : ℕ)
    (S SH0Cprime : Finset (Section1.ClassFunction M)) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      (∃ hp : Nat.Primes, hp.val = p ∧ hoReductionData M MF U W2 H0 hp) →
        q = Nat.card W1 →
          quotientBarUCardinality U C u →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF
                (H0 ⊔ Cprime) SH0Cprime →
              (¬ ∃ χ : Section1.ClassFunction M,
                χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
                  case_9_7_b_data M MF U W1 W2 H0 C p q u := by
  intro h95 hp hq hBarU hSH0Cprime hno
  subst q
  have h95Full := h95
  rcases hp with ⟨hp, hp_eq, hpdata⟩
  rcases h95 with
    ⟨h92, _hp95, hCU, _hBarU95, hCprimeC, _hCprimeEq, _hDade, hS⟩
  have h92full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h92
  have hp96 :
      ∃ hp' : Nat.Primes,
        hp'.val = p ∧
          hoReductionData M MF U W2 H0 hp' ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp' := by
    refine ⟨hp, hp_eq, hpdata, ?_⟩
    rcases theorem_9_6_source_core_sec9 M MF U W1 W2 H0 C Cprime T S hp
        h95Full hpdata with
      ⟨_hUC, hchief, hWbar2, hcard⟩
    exact quotientChiefFactorData_9_6_of_source_facts M MF U W1 W2 H0 hp
      h92full hpdata hchief hWbar2 hcard
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  let N := ambientDerivedSubgroup M
  have hS_N : kernelInducedFamily M N MF H0 S := by
    simpa [N] using hS
  have hUN : U ≤ N := by
    simpa [N] using complement_le_right_sec9 hcomp
  have hCN : C ≤ N := le_trans hCU.1 hUN
  have hH0C_N : H0 ⊔ C ≤ N := sup_le hS_N.1 hCN
  let SH0C : Finset (Section1.ClassFunction M) :=
    kernelInducedSubfamily_sec9 M N MF (H0 ⊔ C) S
  have hSH0C_N : kernelInducedFamily M N MF (H0 ⊔ C) SH0C :=
    kernelInducedFamily_subfamily_of_le_sec9 M N MF H0 (H0 ⊔ C) S
      hH0C_N le_sup_left hS_N
  have hSH0C :
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C := by
    simpa [N] using hSH0C_N
  rcases theorem_9_7_source_core_sec9 M MF U W1 W2 H0 C p (Nat.card W1) u
      h92full hp96 hCU hBarU with
    hcaseA | hcaseB
  · rcases hcaseA with ⟨a, hcaseA⟩
    let Uprime : Subgroup G := (_root_.commutator U).map U.subtype
    have hUprimeU : Uprime ≤ U := by
      intro x hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hUprimeN : Uprime ≤ N := le_trans hUprimeU hUN
    have hH0Uprime_N : H0 ⊔ Uprime ≤ N := sup_le hS_N.1 hUprimeN
    let SH0U : Finset (Section1.ClassFunction M) :=
      kernelInducedSubfamily_sec9 M N MF (H0 ⊔ Uprime) S
    have hSH0U_N : kernelInducedFamily M N MF (H0 ⊔ Uprime) SH0U :=
      kernelInducedFamily_subfamily_of_le_sec9 M N MF H0 (H0 ⊔ Uprime) S
        hH0Uprime_N le_sup_left hS_N
    have hSH0U :
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U := by
      simpa [N] using hSH0U_N
    have hchar :
        case_9_7_a_characterData M MF U H0 C Uprime p (Nat.card W1) a u
          S SH0C SH0U :=
      (theorem_9_8 M MF U W1 W2 H0 C Uprime p (Nat.card W1) a u
        S SH0C SH0U hcaseA hBarU rfl hS hSH0C hSH0U).2
    rcases hchar with ⟨_hdiv, _hUnderlyingDiv, _hbarU, _hR, hχ, _hI⟩
    rcases hχ with ⟨χ, hχSH0C, hχirr, hχdeg, hχlin⟩
    have hYle : H0 ⊔ Cprime ≤ H0 ⊔ C :=
      sup_le_sup_left hCprimeC H0
    have hSH0C_subset :
        SH0C ⊆ SH0Cprime :=
      kernelInducedFamily_subset_of_le_sec9 M N MF (H0 ⊔ Cprime) (H0 ⊔ C)
        SH0Cprime SH0C hYle (by simpa [N] using hSH0Cprime) hSH0C_N
    exact False.elim <| hno
      ⟨χ, hSH0C_subset hχSH0C, ⟨hχirr, hχdeg, hχlin⟩⟩
  · exact hcaseB

private theorem subgroupOf_eq_bot_of_eq_bot_sec9
    {G : Type u} [Group G] {C U : Subgroup G} (hC : C = ⊥) :
    C.subgroupOf U = ⊥ := by
  subst C
  ext x
  simp

private theorem theorem_9_10_C_eq_bot_from_no_forbidden_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
      (¬ ∃ χ : Section1.ClassFunction M,
        χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
        C = ⊥ ∧ u = (p ^ q - 1) / (p - 1) := by
  intro hchar hno
  rcases hchar with ⟨_hdivChar, hdeg, _hreducibles, hnoirr_to_bot⟩
  have hnoirr : ¬ ∃ χ : Section1.ClassFunction M,
      χ ∈ SH0Cprime ∧ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro h
    rcases h with ⟨χ, hχmem, hχirr⟩
    have hχdeg := hdeg χ hχmem
    exact hno ⟨χ, hχmem, ⟨hχirr, hχdeg.1, hχdeg.2⟩⟩
  exact hnoirr_to_bot hnoirr

public theorem theorem_9_10_cyclic_card_from_case_b_character_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          IsCyclic U ∧ Nat.card U = (p ^ q - 1) / (p - 1) := by
  intro hcaseB hchar hno
  rcases hcaseB with
    ⟨_h92, _hH0MF, _hCentIn, _hpprime, _hqprime, _hpdata, _hcard,
      _hcentBy, hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  rcases theorem_9_10_C_eq_bot_from_no_forbidden_sec9
      M MF H0 C p q u SH0 SH0C SH0Cprime hchar hno with
    ⟨hCbot, huEq⟩
  rcases hcyclicQuot with ⟨_hCU, _hnormal, hcyc, hcardUquot⟩
  have hCsub : C.subgroupOf U = ⊥ := subgroupOf_eq_bot_of_eq_bot_sec9 hCbot
  let e1 : U ⧸ C.subgroupOf U ≃* U ⧸ (⊥ : Subgroup U) :=
    QuotientGroup.quotientMulEquivOfEq hCsub
  let e : U ⧸ C.subgroupOf U ≃* U :=
    e1.trans (QuotientGroup.quotientBot (G := U))
  have hUcyc : IsCyclic U := e.isCyclic.mp hcyc
  have hcardUeqUquot : Nat.card U = Nat.card (U ⧸ C.subgroupOf U) :=
    (Nat.card_congr e.toEquiv).symm
  refine ⟨hUcyc, ?_⟩
  rw [hcardUeqUquot, hcardUquot, huEq]

private theorem theorem_9_10_H0_normal_in_MF_sup_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (H0.subgroupOf (MF ⊔ U)).Normal := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0MF, _hCentIn, _hpprime, _hqprime, hpdata, _hcard,
      _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  rcases hpdata with ⟨_hp, _hp_eq, hpdata, _h96⟩
  rcases hpdata with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  have hH0_le_M : H0 ≤ M := hH0_le_MF.trans hMF_le_M
  have hM_le_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0_normal_M
  have hU_le_M : U ≤ M :=
    (complement_le_right_sec9 hcomp).trans section12_ambientDerivedSubgroup_le
  have hMFU_le_M : MF ⊔ U ≤ M := sup_le hMF_le_M hU_le_M
  have hH0_le_MFU : H0 ≤ MF ⊔ U := hH0_le_MF.trans le_sup_left
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_MFU).2
    (hMFU_le_M.trans hM_le_norm_H0)

private theorem theorem_9_10_MF_normal_in_MF_sup_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (MF.subgroupOf (MF ⊔ U)).Normal := by
  intro h92
  have hMF := h92.mf
  have htypeP := h92.typeP
  rcases hMF.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases htypeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  have hUleD : U ≤ ambientDerivedSubgroup M := hcompD.2.1
  have hSleD : MF ⊔ U ≤ ambientDerivedSubgroup M := sup_le hMFleD hUleD
  have hMleNormMF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (H := MF) (K := MF ⊔ U) le_sup_left).2
      (hSleD.trans (hDleM.trans hMleNormMF))

private theorem theorem_9_10_MF_U_complement_in_join_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (MF.subgroupOf (MF ⊔ U)).IsComplement' (U.subgroupOf (MF ⊔ U)) := by
  intro h92
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhallD, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  rcases hcompD with ⟨hMFleD, hUleD, hD_eq, hMFUdisj⟩
  have hMFnormalS : (MF.subgroupOf (MF ⊔ U)).Normal :=
    theorem_9_10_MF_normal_in_MF_sup_U_sec9 M MF U W1 W2 q h92full
  have hMFUdisjSub :
      Disjoint (MF.subgroupOf (MF ⊔ U)) (U.subgroupOf (MF ⊔ U)) := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ U := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hMFUdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMFUsupTop :
      MF.subgroupOf (MF ⊔ U) ⊔ U.subgroupOf (MF ⊔ U) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := MF ⊔ U)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  letI : (MF.subgroupOf (MF ⊔ U)).Normal := hMFnormalS
  exact isComplement'_of_disjoint_sup_eq_top_of_normal
    (MF.subgroupOf (MF ⊔ U)) (U.subgroupOf (MF ⊔ U))
    hMFUdisjSub hMFUsupTop

private theorem theorem_9_10_quotient_frobenius_formal_facts_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (hnormal : (H0.subgroupOf (MF ⊔ U)).Normal) →
        letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
        let Kbar := (MF.subgroupOf (MF ⊔ U)).map
          (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
        let Rbar := (U.subgroupOf (MF ⊔ U)).map
          (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
        Kbar.Normal ∧ Kbar.IsComplement' Rbar ∧ Kbar ≠ ⊥ ∧ Rbar ≠ ⊥ := by
  intro hcase hnormal
  letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
  rcases hcase with
    ⟨h92, hH0MF, _hCentIn, _hpprime, _hqprime, hpdata, _hcard,
      _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  rcases hpdata with ⟨_hp, _hp_eq, hpdata, _h96⟩
  rcases hpdata with
    ⟨_hH0_le_MF, _hMF_le_M, _hH0_normal_M, _hH0_normal_MF, hH0lt,
      _helem, _htypeIIIIV⟩
  let Sg : Subgroup G := MF ⊔ U
  let N : Subgroup Sg := H0.subgroupOf Sg
  let K : Subgroup Sg := MF.subgroupOf Sg
  let R : Subgroup Sg := U.subgroupOf Sg
  let qmap : Sg →* Sg ⧸ N := QuotientGroup.mk' N
  have hKnormal : K.Normal := by
    simpa [Sg, K] using
      theorem_9_10_MF_normal_in_MF_sup_U_sec9 M MF U W1 W2 q h92
  have hKR : K.IsComplement' R := by
    simpa [Sg, K, R] using
      theorem_9_10_MF_U_complement_in_join_sec9 M MF U W1 W2 q h92
  have hNleK : N ≤ K := by
    intro x hx
    have hxH0 : ((x : Sg) : G) ∈ H0 := by
      simpa [N, Subgroup.mem_subgroupOf] using hx
    have hxMF : ((x : Sg) : G) ∈ MF := hH0MF hxH0
    simpa [K, Subgroup.mem_subgroupOf] using hxMF
  have hKbarNormal : (K.map qmap).Normal :=
    Subgroup.Normal.map (H := K) (f := qmap) hKnormal (QuotientGroup.mk'_surjective _)
  have hKbarRbar : (K.map qmap).IsComplement' (R.map qmap) :=
    isComplement'_map_mk'_of_le_isComplement' K R N hNleK hKR
  have hKbar_ne : K.map qmap ≠ ⊥ := by
    intro hKbar_bot
    have hK_le_ker : K ≤ qmap.ker :=
      (Subgroup.map_eq_bot_iff (H := K) (f := qmap)).1 hKbar_bot
    have hMFleH0 : MF ≤ H0 := by
      intro x hxMF
      let xs : Sg := ⟨x, (show MF ≤ MF ⊔ U from le_sup_left) hxMF⟩
      have hxK : xs ∈ K := by
        simpa [K, Subgroup.mem_subgroupOf] using hxMF
      have hxN : xs ∈ N := by
        have hxker : xs ∈ qmap.ker := hK_le_ker hxK
        simpa [qmap, N, QuotientGroup.ker_mk'] using hxker
      simpa [N, Subgroup.mem_subgroupOf] using hxN
    exact hH0lt.2 hMFleH0
  have hUne : U ≠ ⊥ := h92.typeIIToIVSourceCondition.1
  have hRbar_ne : R.map qmap ≠ ⊥ := by
    have hRcard : Nat.card R = Nat.card U := by
      simpa [Sg, R] using natCard_subgroupOf_eq U (MF ⊔ U) le_sup_right
    have hRbar_card : Nat.card (R.map qmap) = Nat.card R :=
      natCard_map_mk'_eq_of_le_isComplement' K R N hNleK hKR
    have hRbar_one_lt : 1 < Nat.card (R.map qmap) := by
      rw [hRbar_card, hRcard]
      exact (Subgroup.one_lt_card_iff_ne_bot (H := U)).2 hUne
    exact (Subgroup.one_lt_card_iff_ne_bot (H := R.map qmap)).1 hRbar_one_lt
  exact ⟨by simpa [Sg, N, K, qmap] using hKbarNormal,
    by simpa [Sg, N, K, R, qmap] using hKbarRbar,
    by simpa [Sg, N, K, qmap] using hKbar_ne,
    by simpa [Sg, N, R, qmap] using hRbar_ne⟩

private theorem theorem_9_10_field_unit_fixed_eq_one_sec9
    {F : Type u} [Field F] (a : Fˣ) (z : Multiplicative F) :
    a ≠ 1 →
      Multiplicative.ofAdd ((a : F) * Multiplicative.toAdd z) = z →
        z = 1 := by
  intro ha hfix
  apply Multiplicative.toAdd.injective
  simp
  have hz : (a : F) * Multiplicative.toAdd z = Multiplicative.toAdd z := by
    simpa using congrArg Multiplicative.toAdd hfix
  have hzero : Multiplicative.toAdd z = 0 := by
    have hmul : ((a : F) - 1) * Multiplicative.toAdd z = 0 := by
      calc
        ((a : F) - 1) * Multiplicative.toAdd z =
            (a : F) * Multiplicative.toAdd z - Multiplicative.toAdd z := by ring
        _ = 0 := by rw [hz]; ring
    have ha_sub : ((a : F) - 1) ≠ 0 := by
      intro hsub
      apply ha
      ext
      simpa using sub_eq_zero.mp hsub
    exact (mul_eq_zero.mp hmul).resolve_left ha_sub
  exact hzero

private theorem theorem_9_10_quotient_complement_centralizer_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (hCbot : C = ⊥) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (hnormal : (H0.subgroupOf (MF ⊔ U)).Normal) →
        letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
        let Kbar := (MF.subgroupOf (MF ⊔ U)).map
          (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
        let Rbar := (U.subgroupOf (MF ⊔ U)).map
          (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
        ∀ x : Rbar,
          x ≠ 1 → elementCentralizerIn Kbar (x :
            ↥(MF ⊔ U) ⧸ H0.subgroupOf (MF ⊔ U)) = ⊥ := by
  intro hcase hnormal
  letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
  dsimp only
  intro x hx
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hcase with
    ⟨h92, hH0MF, hCentIn, hpprime, hqprime, hpdata, hcard,
      hcentBy, hcyclicQuot, hirr, hfield, hcop, hdiv⟩
  rcases hfield with
    ⟨hnH0MF, hnC, _hW1normU, _hCinv, F, fieldInst, fintypeInst, Ustar,
      _hFcard, _hUstarCard, _hUstarCyc, _hspan, φH, φU, _φW, hUact,
      _hWact⟩
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : (H0.subgroupOf MF).Normal := hnH0MF
  letI : (C.subgroupOf U).Normal := hnC
  let Sg : Subgroup G := MF ⊔ U
  let N : Subgroup Sg := H0.subgroupOf Sg
  let K : Subgroup Sg := MF.subgroupOf Sg
  let R : Subgroup Sg := U.subgroupOf Sg
  let qS : Sg →* Sg ⧸ N := QuotientGroup.mk' N
  have hyK : y ∈ K.map qS := by
    simpa [Sg, N, K, qS] using hy.1
  rcases hyK with ⟨kS, hkK, hky⟩
  have hxR : (x : Sg ⧸ N) ∈ R.map qS := by
    exact x.property
  rcases hxR with ⟨rS, hrR, hrx⟩
  let kMF : MF := ⟨(kS : G), by
    simpa [Sg, K, Subgroup.mem_subgroupOf] using hkK⟩
  let rU : U := ⟨(rS : G), by
    simpa [Sg, R, Subgroup.mem_subgroupOf] using hrR⟩
  let xUbar : U ⧸ C.subgroupOf U := QuotientGroup.mk' (C.subgroupOf U) rU
  have hφU_ne : ((φU xUbar : Ustar) : Fˣ) ≠ 1 := by
    intro hφ
    have hxUbar_one : xUbar = 1 := by
      apply φU.injective
      ext
      simpa using hφ
    have hrU_C : rU ∈ C.subgroupOf U := by
      exact (QuotientGroup.eq_one_iff (N := C.subgroupOf U) (x := rU)).1
        (by simpa [xUbar] using hxUbar_one)
    have hrU_one : rU = 1 := by
      have hrU_bot : rU ∈ (⊥ : Subgroup U) := by
        simpa [hCbot] using hrU_C
      simpa using hrU_bot
    have hrS_one : rS = 1 := by
      ext
      simpa [rU] using congrArg Subtype.val hrU_one
    have hxval_one : (x : Sg ⧸ N) = 1 := by
      rw [← hrx, hrS_one]
      simp [qS]
    exact hx (Subtype.ext hxval_one)
  have hout :
      QuotientGroup.mk' (C.subgroupOf U) (Quotient.out xUbar) = xUbar := by
    exact Quotient.out_eq' xUbar
  have hquot_eq :
      QuotientGroup.mk' (C.subgroupOf U) (Quotient.out xUbar) =
        QuotientGroup.mk' (C.subgroupOf U) rU := by
    simp [xUbar]
  have hdiffC : ((Quotient.out xUbar)⁻¹ * rU) ∈ C.subgroupOf U :=
    QuotientGroup.eq.mp hquot_eq
  have hdiffBot :
      ((Quotient.out xUbar)⁻¹ * rU : U) ∈ (⊥ : Subgroup U) := by
    simpa [hCbot] using hdiffC
  have hxout_eq : (Quotient.out xUbar : U) = rU := by
    have hmul : ((Quotient.out xUbar)⁻¹ * rU : U) = 1 := by
      simpa using hdiffBot
    simpa using inv_mul_eq_one.mp hmul
  rcases hUact xUbar kMF with ⟨hconjMF, hact⟩
  have hycent :
      y ∈ Subgroup.centralizer ({(x : Sg ⧸ N)} : Set (Sg ⧸ N)) := by
    simpa [elementCentralizerIn, Sg, N, K, qS] using hy.2
  have hcomm_yx : y * (x : Sg ⧸ N) = (x : Sg ⧸ N) * y :=
    Subgroup.mem_centralizer_singleton_iff.mp hycent
  have hcomm_kr : qS kS * qS rS = qS rS * qS kS := by
    rw [hky, hrx]
    exact hcomm_yx
  have hfixS' : (qS rS)⁻¹ * qS kS * qS rS = qS kS := by
    calc
      (qS rS)⁻¹ * qS kS * qS rS =
          (qS rS)⁻¹ * (qS kS * qS rS) := by rw [mul_assoc]
      _ = (qS rS)⁻¹ * (qS rS * qS kS) := by rw [hcomm_kr]
      _ = qS kS := by simp
  have hfixS : qS (rS⁻¹ * kS * rS) = qS kS := by
    calc
      qS (rS⁻¹ * kS * rS) = (qS rS)⁻¹ * qS kS * qS rS := by
        simp [qS]
      _ = qS kS := hfixS'
  have hconjMF_r : (rU : G)⁻¹ * (kMF : G) * (rU : G) ∈ MF := by
    simpa [hxout_eq] using hconjMF kMF
  have hfixMF_r :
      QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(rU : G)⁻¹ * (kMF : G) * (rU : G), hconjMF_r⟩ =
        QuotientGroup.mk' (H0.subgroupOf MF) kMF := by
    apply QuotientGroup.eq.mpr
    have hNmem : ((rS⁻¹ * kS * rS)⁻¹ * kS) ∈ N :=
      QuotientGroup.eq.mp hfixS
    have hH0mem :
        (((rU : G)⁻¹ * (kMF : G) * (rU : G))⁻¹ * (kMF : G)) ∈ H0 := by
      simpa [Sg, N, kMF, rU, Subgroup.mem_subgroupOf] using hNmem
    simpa [Subgroup.mem_subgroupOf] using hH0mem
  have hfixMF :
      QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(Quotient.out xUbar : U)⁻¹ * (kMF : G) *
            (Quotient.out xUbar : U), hconjMF kMF⟩ =
        QuotientGroup.mk' (H0.subgroupOf MF) kMF := by
    simpa [hxout_eq] using hfixMF_r
  have hfixed :
      Multiplicative.ofAdd (((φU xUbar : Ustar) : Fˣ) *
          Multiplicative.toAdd (φH (QuotientGroup.mk' (H0.subgroupOf MF) kMF))) =
        φH (QuotientGroup.mk' (H0.subgroupOf MF) kMF) := by
    rw [← hact]
    exact congrArg φH hfixMF
  have hφH_one : φH (QuotientGroup.mk' (H0.subgroupOf MF) kMF) = 1 := by
    exact theorem_9_10_field_unit_fixed_eq_one_sec9
      (((φU xUbar : Ustar) : Fˣ))
      (φH (QuotientGroup.mk' (H0.subgroupOf MF) kMF)) hφU_ne hfixed
  have hkMFq_one : QuotientGroup.mk' (H0.subgroupOf MF) kMF = 1 := by
    apply φH.injective
    simpa using hφH_one
  have hkH0 : kMF ∈ H0.subgroupOf MF :=
    (QuotientGroup.eq_one_iff (N := H0.subgroupOf MF) (x := kMF)).1 hkMFq_one
  have hkN : kS ∈ N := by
    have hkH0G : (kS : G) ∈ H0 := by
      simpa [kMF, Subgroup.mem_subgroupOf] using hkH0
    simpa [N, Sg, Subgroup.mem_subgroupOf] using hkH0G
  have hky_one : qS kS = 1 :=
    (QuotientGroup.eq_one_iff (N := N) (x := kS)).2 hkN
  rw [← hky]
  exact hky_one

private theorem theorem_9_10_quotient_complement_centralizer_from_character_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          (hnormal : (H0.subgroupOf (MF ⊔ U)).Normal) →
            letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
            let Kbar := (MF.subgroupOf (MF ⊔ U)).map
              (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
            let Rbar := (U.subgroupOf (MF ⊔ U)).map
              (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
            ∀ x : Rbar,
              x ≠ 1 → elementCentralizerIn Kbar (x :
                ↥(MF ⊔ U) ⧸ H0.subgroupOf (MF ⊔ U)) = ⊥ := by
  intro hcase hchar hno hnormal
  have hCbot : C = ⊥ :=
    (theorem_9_10_C_eq_bot_from_no_forbidden_sec9
      M MF H0 C p q u SH0 SH0C SH0Cprime hchar hno).1
  exact theorem_9_10_quotient_complement_centralizer_source_core_sec9
    M MF U W1 W2 H0 C p q u hCbot hcase hnormal

public theorem theorem_9_10_quotient_frobenius_of_C_eq_bot_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    C = ⊥ →
      case_9_7_b_data M MF U W1 W2 H0 C p q u →
        quotientFrobeniusWithKernelData MF H0 U := by
  intro hCbot hcase
  let hnormal : (H0.subgroupOf (MF ⊔ U)).Normal :=
    theorem_9_10_H0_normal_in_MF_sup_U_sec9 M MF U W1 W2 H0 C p q u hcase
  refine ⟨case_9_7_b_H0_le_MF_sec9 hcase, hnormal, ?_⟩
  letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
  let Kbar := (MF.subgroupOf (MF ⊔ U)).map
    (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
  let Rbar := (U.subgroupOf (MF ⊔ U)).map
    (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
  rcases theorem_9_10_quotient_frobenius_formal_facts_sec9
      M MF U W1 W2 H0 C p q u hcase hnormal with
    ⟨hKnormal, hKR, hKne, hRne⟩
  have hcent :
      ∀ x : Rbar,
        x ≠ 1 → elementCentralizerIn Kbar (x :
          ↥(MF ⊔ U) ⧸ H0.subgroupOf (MF ⊔ U)) = ⊥ :=
    theorem_9_10_quotient_complement_centralizer_source_core_sec9
      M MF U W1 W2 H0 C p q u hCbot hcase hnormal
  exact (lemma_3_1
    (G := ↥(MF ⊔ U) ⧸ H0.subgroupOf (MF ⊔ U))
    (K := Kbar) (R := Rbar) hKne hRne hKnormal hKR).2 hcent

private theorem theorem_9_10_quotient_frobenius_disjoint_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          (hnormal : (H0.subgroupOf (MF ⊔ U)).Normal) →
            letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
            let Rbar := (U.subgroupOf (MF ⊔ U)).map
              (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
            ∀ g,
              g ∉ Rbar → Disjoint Rbar (Rbar.conjBy g) := by
  intro hcase hchar hno hnormal
  letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
  let Kbar := (MF.subgroupOf (MF ⊔ U)).map
    (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
  let Rbar := (U.subgroupOf (MF ⊔ U)).map
    (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
  rcases theorem_9_10_quotient_frobenius_formal_facts_sec9
      M MF U W1 W2 H0 C p q u hcase hnormal with
    ⟨hKnormal, hKR, hKne, hRne⟩
  have hcent :
      ∀ x : Rbar,
        x ≠ 1 → elementCentralizerIn Kbar (x :
          ↥(MF ⊔ U) ⧸ H0.subgroupOf (MF ⊔ U)) = ⊥ :=
    theorem_9_10_quotient_complement_centralizer_from_character_sec9
      M MF U W1 W2 H0 C p q u SH0 SH0C SH0Cprime
      hcase hchar hno hnormal
  exact (lemma_3_1
    (G := ↥(MF ⊔ U) ⧸ H0.subgroupOf (MF ⊔ U))
    (K := Kbar) (R := Rbar) hKne hRne hKnormal hKR).2 hcent |>.disjoint_conjBy

private theorem theorem_9_10_quotient_frobenius_group_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          (hnormal : (H0.subgroupOf (MF ⊔ U)).Normal) →
            letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
            IsFrobeniusGroupWithKernelComplement
              ((MF.subgroupOf (MF ⊔ U)).map
                (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U))))
              ((U.subgroupOf (MF ⊔ U)).map
                (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))) := by
  intro hcase hchar hno hnormal
  letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
  let Kbar := (MF.subgroupOf (MF ⊔ U)).map
    (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
  let Rbar := (U.subgroupOf (MF ⊔ U)).map
    (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))
  rcases theorem_9_10_quotient_frobenius_formal_facts_sec9
      M MF U W1 W2 H0 C p q u hcase hnormal with
    ⟨hKnormal, hKR, hKne, hRne⟩
  have hdisj :
      ∀ g,
        g ∉ Rbar → Disjoint Rbar (Rbar.conjBy g) :=
    theorem_9_10_quotient_frobenius_disjoint_source_core_sec9
      M MF U W1 W2 H0 C p q u SH0 SH0C SH0Cprime
      hcase hchar hno hnormal
  exact ⟨by simpa [Kbar] using hKnormal,
    by simpa [Kbar, Rbar] using hKR,
    by simpa [Rbar] using hdisj,
    by simpa [Kbar] using hKne,
    by simpa [Rbar] using hRne⟩

private theorem theorem_9_10_quotient_frobenius_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          ∃ hnormal : (H0.subgroupOf (MF ⊔ U)).Normal,
            letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
            IsFrobeniusGroupWithKernelComplement
              ((MF.subgroupOf (MF ⊔ U)).map
                (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U))))
              ((U.subgroupOf (MF ⊔ U)).map
                (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U)))) := by
  intro hcase hchar hno
  let hnormal : (H0.subgroupOf (MF ⊔ U)).Normal :=
    theorem_9_10_H0_normal_in_MF_sup_U_sec9 M MF U W1 W2 H0 C p q u hcase
  exact ⟨hnormal,
    theorem_9_10_quotient_frobenius_group_source_core_sec9
      M MF U W1 W2 H0 C p q u SH0 SH0C SH0Cprime hcase hchar hno hnormal⟩

private theorem theorem_9_10_typeII_typeF_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      section16TypeII M MF →
        ∃ U1 U0 : Subgroup G,
          Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0 := by
  intro hcase hII
  rcases hcase with
    ⟨h92, _hH0MF, _hCentIn, _hpprime, _hqprime, _hpdata, _hcard,
      _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  exact ((h92.typeIISource hII).2.2)

public theorem theorem_9_10_typeII_frobenius_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          section16TypeII M MF → section12FrobeniusJoinWithKernel MF U := by
  intro hcaseB hchar hno hII
  rcases theorem_9_10_typeII_typeF_source_core_sec9
      M MF U W1 W2 H0 C p q u hcaseB hII with
    ⟨U1, U0, hF⟩
  have hUcyc : IsCyclic U :=
    (theorem_9_10_cyclic_card_from_case_b_character_sec9 M MF U W1 W2 H0 C
      p q u SH0 SH0C SH0Cprime hcaseB hchar hno).1
  have hSylow : ∀ r : Nat.Primes, ∀ P : Sylow r.val U, IsCyclic (P : Subgroup U) := by
    intro _r P
    haveI : IsCyclic U := hUcyc
    exact Subgroup.isCyclic_of_le (H := (P : Subgroup U)) (H' := ⊤) le_top
  have h82 := Section8.theorem_8_2_b (ambientDerivedSubgroup M) MF U U1 U0
  exact (h82 hF).mpr hSylow

public theorem theorem_9_10_frobenius_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      case_9_7_b_characterData M MF H0 C p q u SH0 SH0C SH0Cprime →
        (¬ ∃ χ : Section1.ClassFunction M,
          χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
          quotientFrobeniusWithKernelData MF H0 U ∧
            (section16TypeII M MF → section12FrobeniusJoinWithKernel MF U) := by
  intro hcase hchar hno
  have hcaseFull := hcase
  rcases hcase with
    ⟨_h92, hH0MF, _hCentIn, _hpprime, _hqprime, _hpdata, _hcard,
      _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hH0MF,
      theorem_9_10_quotient_frobenius_source_core_sec9
        M MF U W1 W2 H0 C p q u SH0 SH0C SH0Cprime hcaseFull hchar hno⟩
  · exact theorem_9_10_typeII_frobenius_source_core_sec9
      M MF U W1 W2 H0 C p q u SH0 SH0C SH0Cprime hcaseFull hchar hno

public theorem theorem_9_10
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p q u : ℕ)
    (S SH0Cprime : Finset (Section1.ClassFunction M)) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      (∃ hp : Nat.Primes, hp.val = p ∧ hoReductionData M MF U W2 H0 hp) →
        q = Nat.card W1 →
          quotientBarUCardinality U C u →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF
                (H0 ⊔ Cprime) SH0Cprime →
              (¬ ∃ χ : Section1.ClassFunction M,
                χ ∈ SH0Cprime ∧ degreeQuIrreducibleFromLinearHC M MF C q u χ) →
                  case_9_7_b_data M MF U W1 W2 H0 C p q u ∧
                    quotientFrobeniusWithKernelData MF H0 U ∧
                    IsCyclic U ∧
                    Nat.card U = (p ^ q - 1) / (p - 1) ∧
                    (section16TypeII M MF → section12FrobeniusJoinWithKernel MF U) := by
  intro h95 hp hq hBarU hSH0Cprime hno
  have hcaseB : case_9_7_b_data M MF U W1 W2 H0 C p q u :=
    theorem_9_10_case_b_from_no_forbidden_sec9
      M MF U W1 W2 H0 C Cprime T p q u S SH0Cprime
      h95 hp hq hBarU hSH0Cprime hno
  rcases h95 with
    ⟨h92, _hp95, hCU, _hBarU95, _hCprimeC, hCprimeEq, _hDade, hS⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  let N := ambientDerivedSubgroup M
  have hS_N : kernelInducedFamily M N MF H0 S := by
    simpa [N] using hS
  have hUN : U ≤ N := by
    simpa [N] using complement_le_right_sec9 hcomp
  have hCN : C ≤ N := le_trans hCU.1 hUN
  have hH0C_N : H0 ⊔ C ≤ N := sup_le hS_N.1 hCN
  let SH0C : Finset (Section1.ClassFunction M) :=
    kernelInducedSubfamily_sec9 M N MF (H0 ⊔ C) S
  have hSH0C_N : kernelInducedFamily M N MF (H0 ⊔ C) SH0C :=
    kernelInducedFamily_subfamily_of_le_sec9 M N MF H0 (H0 ⊔ C) S
      hH0C_N le_sup_left hS_N
  have hSH0C :
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C := by
    simpa [N] using hSH0C_N
  have hchar :
      case_9_7_b_characterData M MF H0 C p q u S SH0C SH0Cprime :=
    (theorem_9_9 M MF U W1 W2 H0 C Cprime p q u
      S SH0C SH0Cprime hcaseB hCprimeEq hS hSH0C hSH0Cprime).2
  have hcycCard : IsCyclic U ∧ Nat.card U = (p ^ q - 1) / (p - 1) :=
    theorem_9_10_cyclic_card_from_case_b_character_sec9
      M MF U W1 W2 H0 C p q u S SH0C SH0Cprime hcaseB hchar hno
  have hfrob :
      quotientFrobeniusWithKernelData MF H0 U ∧
        (section16TypeII M MF → section12FrobeniusJoinWithKernel MF U) :=
    theorem_9_10_frobenius_source_bridge_sec9
      M MF U W1 W2 H0 C p q u S SH0C SH0Cprime hcaseB hchar hno
  exact ⟨hcaseB, hfrob.1, hcycCard.1, hcycCard.2, hfrob.2⟩

end CFSG.Section9
