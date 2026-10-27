module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: (14.2) source-data adapters
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14_coprime_card_of_isElementaryAbelian_of_ne
    {p q : ℕ} {Q : Type*} [Group Q] [Finite Q]
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    [IsElementaryAbelian q Q] :
    Nat.Coprime p (Nat.card Q) := by
  letI : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q Q := IsElementaryAbelian.isPGroup q Q
  rcases hQp.exists_card_eq with ⟨n, hcard⟩
  rw [hcard]
  exact hq.coprime_pow_of_not_dvd (m := n) (a := p) (by
    intro hq_dvd_p
    exact hpq ((hp.dvd_iff_eq hq.ne_one).1 hq_dvd_p))

public theorem section14_case_9_7_b_for_section13_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G} {p q u : ℕ} :
    Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u →
      Section13.case_9_7_b_for_section13 M C p q u := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0le, hcent, hp, hq, _hred, _hcard, _hcentby, _hcyclic,
      _hirr, _hfield, hcop, hdiv, _hprimeField⟩
  have hCU : C ≤ U := hcent.1
  have hUM : U ≤ M := by
    rcases h92 with ⟨_hMmax, _hMF, htypeP, _htype, _hW1card⟩
    rcases htypeP with ⟨_hMF, hcommon⟩
    exact hcommon.2.2.1.2.1.trans section12_ambientDerivedSubgroup_le
  exact ⟨hCU.trans hUM, hp, hq, hcop, hdiv⟩

public theorem section14_isCyclic_of_case_9_7_b_sourceData_card_eq_one
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    (hCcard : Nat.card C = 1) :
    IsCyclic U := by
  rcases hcase with
    ⟨_h92, _hH0le, _hcent, _hp, _hq, _hred, _hcardMF, _hcentby,
      hcyclicQuot, _hirr, _hfield, _hcop, _hdiv, _hprimeField⟩
  rcases hcyclicQuot with ⟨_hCU, hnormal, hcyc, _hcardQuot⟩
  letI : (C.subgroupOf U).Normal := hnormal
  have hCbot : C = ⊥ := (Subgroup.card_eq_one (H := C)).1 hCcard
  have hCsub : C.subgroupOf U = ⊥ := by
    subst C
    ext x
    simp
  let e1 : U ⧸ C.subgroupOf U ≃* U ⧸ (⊥ : Subgroup U) :=
    QuotientGroup.quotientMulEquivOfEq hCsub
  let e : U ⧸ C.subgroupOf U ≃* U :=
    e1.trans (QuotientGroup.quotientBot (G := U))
  exact e.isCyclic.mp hcyc

public theorem section14_section12InternalDirectProduct_swap
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


public theorem section14_theorem_3_2_map_statement_swap
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
    Section3.theorem_3_2_map_statement W2 W1 W σ := by
  rcases hσ with ⟨hiso, hvirt, hind, hclass, hprin, hagree, hvanish⟩
  refine ⟨hiso, hvirt, ?_, hclass, hprin, ?_, ?_⟩
  · intro α hα
    apply hind
    simpa [Section3.cyclicTISet_swap W1 W2 W] using hα
  · intro α hα x hx
    exact hagree α hα x (by simpa [Section3.cyclicTISet_swap W1 W2 W] using hx)
  · intro χ hχ hnot x hx
    exact hvanish χ hχ hnot x
      (by simpa [Section3.cyclicTISet_swap W1 W2 W] using hx)

public theorem section14_hypothesis_13_1_omegaNotationData_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G} {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    (hω : Section13.hypothesis_13_1_omegaNotationData W W1 W2 p q ω) :
    Section13.hypothesis_13_1_omegaNotationData W W2 W1 q p
      (fun i j => ω j i) := by
  rcases hω with ⟨h31, hqpos, hppos, ωFin, hnotation, hωeq⟩
  refine ⟨Section3.hypothesis_3_1_statement_swap h31, hppos, hqpos,
    (fun i j => ωFin j i), ?_, ?_⟩
  · exact Section3.notation_3_3_statement_swap hnotation
  · intro i j hi hj
    exact hωeq j i hj hi

public theorem section14_hypothesis_13_1_characterNotationDataFor_swap
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
    (h : Section13.hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ) :
    Section13.hypothesis_13_1_characterNotationDataFor
      Tmax Smax W W2 W1 q p
      (fun i j => ω j i) (fun i j => η j i)
      (fun i j => ν j i) (fun i j => μ j i)
      (fun i => νsum i) (fun i => μsum i) δ' δ σ := by
  rcases h with
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  refine
    ⟨section14_hypothesis_13_1_omegaNotationData_swap hω,
      section14_theorem_3_2_map_statement_swap hσ, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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


public theorem section14_hypothesis_13_1_sourceData_swap
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (h13 : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section13.hypothesis_13_1_sourceData Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c := by
  exact Section13.section13_hypothesis_13_1_sourceData_swap h13

public theorem section14_theorem_14_2_b_Q_elementary_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (h13 : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    IsElementaryAbelian q Q :=
  (Section13.theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c
    (section14_hypothesis_13_1_sourceData_swap h13)).2.2.2.2.2.1

public theorem section14_theorem_14_2_b_W2_le_normalizer_Q_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (h13 : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    W2 ≤ Subgroup.normalizer (Q : Set G) := by
  rcases h13 with
    ⟨hcase, _hSTypeP, hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      _hTType, _hCover⟩
  rcases hTTypeP with ⟨hQMF, _hW2cyc, _hW2ne', _hW2hall, _hW2comp,
    _hVle, _hVnil, _hW2normV, _hVcomp, _hQnoncyc, _hSecond, _hFittingEq,
    _hFittingLe, _hW1le, _hW1cyc, _hW1ne, _hCentralizer, _hHatNorm⟩
  rcases hQMF with ⟨⟨hQT, hQnormalT, _hQnilpotent, _hQhall⟩, _hQmax⟩
  have hTnormQ : Tmax ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).1 hQnormalT
  have hW2leT : W2 ≤ Tmax := by
    rw [hTeq]
    exact le_sup_right
  exact hW2leT.trans hTnormQ

public theorem section14_theorem_14_2_a_cardW2_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (h13 : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.card W2 = p := by
  rcases h13 with
    ⟨_hcase, _hSTypeP, _hTTypeP, hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  exact hp.symm

public theorem section14_theorem_14_2_a_W2_le_P_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (h13 : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    W2 ≤ P := by
  rcases h13 with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with ⟨_hPMF, _hW1cyc, _hW1ne, _hW1hall, _hW1comp,
    _hUle, _hUnil, _hW1normU, _hUcomp, _hPnoncyc, _hSecond, _hFittingEq,
    _hFittingLe, hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatNorm⟩
  exact hW2le.trans inf_le_left

public theorem section14_context_primes_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Prime p ∧ Nat.Prime q := by
  by_cases h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u
  · rcases (Section13.theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 h10).2 with ⟨hcase, _hv⟩
    rcases hcase with
      ⟨_h92, _hH0le, _hcent, hq, hp, _hred, _hcard, _hcentby,
        _hcyclic, _hirr, _hfield, _hcop, _hdiv, _hprimeField⟩
    exact ⟨hp, hq⟩
  · rcases ((Section13.theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1).2 h10) with
      ⟨_hCbot, hcase, _hu⟩
    rcases hcase with
      ⟨_h92, _hH0le, _hcent, hp, hq, _hred, _hcard, _hcentby,
        _hcyclic, _hirr, _hfield, _hcop, _hdiv, _hprimeField⟩
    exact ⟨hp, hq⟩

public theorem section14_theorem_14_2_U_card_coprime_of_not_theorem_13_10
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnot : ¬ Section13.theorem_13_10_hypothesis Smax P C Sfam p q u) :
    Nat.card U = (p ^ q - 1) / (p - 1) ∧
      Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  let hsrc' := hsrc
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, hc, _hd, hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases ((Section13.theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsrc').2 hnot) with
    ⟨hCbot, hcaseB, hu⟩
  rcases hcaseB with
    ⟨_h92, _hH0le, _hcent, _hp', _hq', _hred, _hcard, _hcentby,
      _hcyclic, _hirr, _hfield, hcop, _hdiv, _hprimeField⟩
  have hc_one : c = 1 := by
    rw [hc, hCbot]
    simp
  constructor
  · rw [hUcard, hu, hc_one, Nat.mul_one]
  · simpa [hu] using hcop

public theorem section14_U_card_of_sourceData_of_u_eq_and_c_eq_one
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hu : u = (p ^ q - 1) / (p - 1))
    (hc : c = 1) :
    Nat.card U = (p ^ q - 1) / (p - 1) := by
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rw [hUcard, hu, hc, Nat.mul_one]

public theorem section14_C_eq_bot_of_pf13_12_source
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    C = ⊥ := by
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hcardC : Nat.card C = 1 := by
    rw [← hc, hc_one]
  exact (Subgroup.card_eq_one (H := C)).1 hcardC
end CFSG.Section14
