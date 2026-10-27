module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aPair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xo
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s136a_even_of_isPowTwo {n : ℕ} (hn : IsPowTwo n) (hn2 : 2 ≤ n) : Even n := by
  obtain ⟨k, rfl⟩ := hn
  cases k with
  | zero => norm_num at hn2
  | succ j => exact Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem s136a_false_of_two_members_of_k_eq_one
    (hThin : ThinList13)
    {D : Data G} (hS : Setting13 D) {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h1 : S17.R17_1At D V₀ V hV) (hk : D.k = 1) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (sL : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n))
    (sK : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 K) n ∨ IsU3 (Bar2 K) n)) : False := by
  obtain ⟨nL, hLpow, hLshape⟩ := sL
  obtain ⟨nK, hKpow, hKshape⟩ := sK
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hLn : (L.subgroupOf D.M).Normal := hS.hyp131.normal L hL
  have hKn : (K.subgroupOf D.M).Normal := hS.hyp131.normal K hK
  have hE₁ : ∃ E₁ ≤ L, IsElemAbelian 3 E₁ ∧ 1 ≤ CFSG.Open.pRank 3 E₁ ∧ Permutes E₁ D.T := by
    rcases hLshape with hL2 | hLU
    · exact S17.exists_elemAbelian_permutes_of_isL2_even hLM hLn
        (s136a_even_of_isPowTwo hLpow (s13_two_le_of_isL2 hL2)) hL2
    · exact S17.exists_elemAbelian_permutes_of_isSU3_even hLM hLn
        (s136a_even_of_isPowTwo hLpow (s13_two_le_of_isU3 hLU))
        (uc22p22d_isSU3_of_isU3 hL.2.2 hLU)
  have hE₂ : ∃ E₂ ≤ K, IsElemAbelian 3 E₂ ∧ 1 ≤ CFSG.Open.pRank 3 E₂ ∧ Permutes E₂ D.T := by
    rcases hKshape with hK2 | hKU
    · exact S17.exists_elemAbelian_permutes_of_isL2_even hKM hKn
        (s136a_even_of_isPowTwo hKpow (s13_two_le_of_isL2 hK2)) hK2
    · exact S17.exists_elemAbelian_permutes_of_isSU3_even hKM hKn
        (s136a_even_of_isPowTwo hKpow (s13_two_le_of_isU3 hKU))
        (uc22p22d_isSU3_of_isU3 hK.2.2 hKU)
  obtain ⟨E₁, hE₁L, hE₁ab, hE₁r, hperm₁⟩ := hE₁
  obtain ⟨E₂, hE₂K, hE₂ab, hE₂r, hperm₂⟩ := hE₂
  have hELM : E₁ ≤ D.M := hE₁L.trans hLM
  have hEKM : E₂ ≤ D.M := hE₂K.trans hKM
  obtain ⟨hcomm, hdisj⟩ := s136a_indep_of_members hThin hS hL hK hne Nat.prime_three
    (by norm_num) hE₁L hE₂K (CFSG.Open.IsElemAbelian.isPGroup hE₁ab)
  obtain ⟨n, hnO, hXel, hXrank, hXperm⟩ := S17.exists_conj_sup_isElemAbelian_permutes
    hELM hEKM hE₁ab hE₂ab hperm₁ hperm₂ hcomm hdisj (by omega)
  have hO2M : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  refine S17.false_of_k_eq_one_of_permutes h1 hk
    ⟨E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom, ?_, ?_,
      CFSG.Open.IsElemAbelian.isPGroup hXel, hXel.2, ?_, hXperm⟩
  · refine sup_le hELM ?_
    rintro x ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact D.M.mul_mem (D.M.mul_mem (hO2M hnO) (hEKM hy)) (D.M.inv_mem (hO2M hnO))
  · intro hbot
    rw [hbot, s13_Rank13_pRank_bot Nat.prime_three] at hXrank
    omega
  · exact CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank Nat.prime_three hXrank

theorem s136a_false_of_three_members
    (hThin : ThinList13)
    {D : Data G} (hS : Setting13 D) (h82 : F08.R82 D) {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V} (h1 : S17.R17_1At D V₀ V hV) {L₁ L₂ L₃ : Subgroup G}
    (h₁ : L₁ ∈ calC D.M) (h₂ : L₂ ∈ calC D.M) (h₃ : L₃ ∈ calC D.M)
    (h12 : barImage D.M L₁ ≠ barImage D.M L₂) (h13 : barImage D.M L₁ ≠ barImage D.M L₃)
    (h23 : barImage D.M L₂ ≠ barImage D.M L₃)
    (s₁ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₁) n ∨ IsU3 (Bar2 L₁) n))
    (s₂ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₂) n ∨ IsU3 (Bar2 L₂) n))
    (s₃ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₃) n ∨ IsU3 (Bar2 L₃) n)) : False := by
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D (h82 _ (uc22s13xo_hyp81 h₁ h₂ h₃
    (by rintro rfl; exact h12 rfl) (by rintro rfl; exact h13 rfl) (by rintro rfl; exact h23 rfl)
    s₁ s₂ s₃))
  exact s136a_false_of_two_members_of_k_eq_one hThin hS h1 hk h₁ h₂ h12 s₁ s₂

theorem s136a_three_not_mem
    (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hx : DataExt D) (hSg : UC6S846.SigmaStd D) (hS : Setting13 D)
    (hshape : ∀ L ∈ calC D.M, ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n))
    {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V} (h1 : S17.R17_1At D V₀ V hV) : 3 ∉ D.sig := by
  intro h3
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hSg hS.sig_eq h3
  have hsum := uc22s2121e3_pRank_eq_sum hThin hCyc hS hSg h3
  have hS3 : CFSG.Open.pRank 3 (F13.Sp D.M 3) ≤ 1 := hS.hyp131.smallS 3 h3
  have hM3 : 3 ≤ CFSG.Open.pRank 3 D.M := hx.three_le 3 h3
  have hterm : ∀ J ∈ s13_compsP (Bar2 D.M) 3, CFSG.Open.pRank 3 J ≤ 1 := by
    intro J hJ
    obtain ⟨hJc, -⟩ := s13_mem_compsP.mp hJ
    obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJc
    rw [s13_pRank_barImage Nat.prime_three (by norm_num) (s13_le_of_mem_calC hL)]
    rcases uc22s2121e3_pRank_le_of_mem_calC hS.hyp131 Nat.prime_three (by norm_num) hL with
      h1 | ⟨⟨m, hm, hU, hpm⟩, -⟩
    · exact h1
    · exfalso
      have heven : Even m := s136a_even_of_isPowTwo hm (s13_two_le_of_isU3 hU)
      have h3dvd : 3 ∣ 2 ^ m - 1 := by
        simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp heven)
      have hsub : 3 ∣ (2 ^ m + 1) - (2 ^ m - 1) := Nat.dvd_sub hpm h3dvd
      have heq : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
      rw [heq] at hsub
      norm_num at hsub
  have hsumle : ∑ J ∈ s13_compsP (Bar2 D.M) 3, CFSG.Open.pRank 3 J ≤
      (s13_compsP (Bar2 D.M) 3).card := by
    calc ∑ J ∈ s13_compsP (Bar2 D.M) 3, CFSG.Open.pRank 3 J
        ≤ ∑ J ∈ s13_compsP (Bar2 D.M) 3, 1 := Finset.sum_le_sum hterm
      _ = (s13_compsP (Bar2 D.M) 3).card := by simp
  have hcard : 2 ≤ (s13_compsP (Bar2 D.M) 3).card := by
    rw [hsum] at hM3
    omega
  obtain ⟨J₁, hJ₁, J₂, hJ₂, hJne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (s13_compsP (Bar2 D.M) 3).card)
  obtain ⟨L₁, hL₁, hbar₁⟩ := s13_exists_calC_of_component D.M (s13_mem_compsP.mp hJ₁).1
  obtain ⟨L₂, hL₂, hbar₂⟩ := s13_exists_calC_of_component D.M (s13_mem_compsP.mp hJ₂).1
  refine s136a_false_of_two_members_of_k_eq_one hThin hS h1 hk hL₁ hL₂ ?_
    (hshape L₁ hL₁) (hshape L₂ hL₂)
  intro h
  exact hJne (by rw [← hbar₁, ← hbar₂, h])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
