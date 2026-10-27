module

public import CFSG.LocalAnalysis.WeakClosure81.SixNineIndexTwo
public import CFSG.LocalAnalysis.WeakClosure81.SixNineIndexFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAGaps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_26a_Alt_holds
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) {D : Data G} {V₀ V : Subgroup G}
    (h20 : R17_20At D V₀ V) (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h93 : ∀ L, Ctx17_17 D V₀ V L → Thm93 V₀ D.T) (hC117 : C117 D V₀ V)
    (hK2 : K_J2_centralizer_shape) (hK3 : Inputs1719.K_J2_threeCentral) :
    Gap17_26a_Alt D V₀ V := by
  intro hcat L c hm hJ2 hsig hN h242 hN2 h2grp A hA hAO
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁
  have hsh := gap17_25_H1_shape_of D V₀ V h20 hC117 hK2 L c hJ2
  obtain ⟨ψ, hker, hrange⟩ := CFSG.GroupTheory.AlternatingFive.exists_hom_perm_five hsh
  have hfus := seventeen_twentytwo_two_of_J2 h22 h23 c
  have hU : ∀ X : Subgroup G, X ≤ H₁ →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ Nat.card X = p) → UC6.InU D.M X :=
    fun X hX hp => gap17_26a_U_holds c h20 hC117 hK2 hK3 hm hJ2 hN h242 hfus X hX hp
  have h5 : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC c.mem_calC) h5
  have hNA := isPGroup_H17_25_one_inf_normalizer c hm hsp hU hA hAO
  have hinner := map_gammaZero_le_alternatingGroup hTim hcat c h66 h88 (h93 L c) hm
    (fun X hX h3 => hU X hX ⟨3, by norm_num, by norm_num, by norm_num, h3⟩) ψ hker hrange hA
  obtain ⟨hAel, hATI, hrk, hAT⟩ := config17_26a_II_gammaSet_facts c.hyp125 hA hm
  have h2rk : 2 < rk ↥A := by rw [hrk]; omega
  have hAH : A ≤ H₁ := hAT.trans (T_le_H17_25_one c.hyp125)
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  have hC : IsPGroup 2 ↥(H₁ ⊓ centralizer (E3.cClos A 2 D.T : Set G)) := by
    obtain ⟨-, g₀, hAg₀, hq⟩ := hA
    have hV0p : IsPGroup 2 V₀ :=
      CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian c.hyp125.pairFacts.elemAbelian₀
    have hAeq : A = conjSubgroup V₀ g₀ :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV0p g₀) hAg₀).mp hq
    rw [hAeq, E3.cClos_conjV]
    exact h2grp
  have hcard := CFSG.GroupTheory.AlternatingFive.card_map_subgroupOf_eq_two_pow ψ hker hAH hA2
  have hdvd : Nat.card ((A.subgroupOf H₁).map ψ) ∣ 4 := by
    have h60 : Nat.card ((A.subgroupOf H₁).map ψ) ∣ 60 := by
      rw [← CFSG.Quasithin.SteinbergCB.nat_card_alternating_five]
      exact Subgroup.card_dvd_of_le hinner
    rw [hcard] at h60 ⊢
    have h4 : 2 ^ E3.mQuot A (A ⊓ pCoreOf 2 H₁) ∣ 4 * 15 := by
      rw [show 4 * 15 = 60 by norm_num]
      exact h60
    exact (Nat.Coprime.pow_left (E3.mQuot A (A ⊓ pCoreOf 2 H₁))
      (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_right h4
  have hk2 : E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 2 := by
    rw [hcard, show (4 : ℕ) = 2 ^ 2 by norm_num] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hfb := conj_inf_pCoreOf_le_normalizer (T_le_H17_25_one c.hyp125)
    (pCoreOf_H17_25_one_le_T c) hAH hAel hATI h2rk hAO hk2 hNA hC
  have hk0 : E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≠ 0 := by
    intro h0
    exact hAO (((E3.mQuot_eq_zero_iff hA2 inf_le_left).mp h0).symm ▸ inf_le_right)
  rcases (by omega : E3.mQuot A (A ⊓ pCoreOf 2 H₁) = 1 ∨
      E3.mQuot A (A ⊓ pCoreOf 2 H₁) = 2) with hk | hk
  · obtain ⟨h, hh, h1, h2, h3⟩ :=
      exists_second_case_of_mQuot_eq_one hAel hATI h2rk hAH hAO hk hfb
        (fun x hx hodd =>
          CFSG.GroupTheory.AlternatingFive.eq_one_or_prime_of_hom_perm_five ψ hker hx hodd)
    exact ⟨h, hh, Or.inr ⟨h1, h2, h3⟩⟩
  · have hrange' : alternatingGroup (Fin 5) ≤ ψ.range := by
      rcases hrange with h | h
      · exact h.ge
      · rw [h]; exact le_top
    obtain ⟨h, hh, h1, h2⟩ :=
      exists_first_case_of_mQuot_eq_two ψ hker hrange' hAel hATI h2rk hAH hinner hk hfb
    exact ⟨h, hh, Or.inl ⟨h1, h2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
