module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenCaseThreeGap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem r18_15_of_dvd_cTilde (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hCV : p ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    R18_15At D V₀ V p L := by
  classical
  intro v hv hv1
  by_cases hv0 : v ∈ V₀
  · exact p_mem_piSet_of_mem_V₀ D h hv0 hv1
  · have hP := h.hyp125.pairFacts
    have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
      rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
      · exact Or.inl h0
      · exact Or.inr h0
    have h4 : Nat.card V₀ ≤ 4 := by
      have := (mSub_le_one_iff hP.elemAbelian₀).1 h.small
      omega
    obtain ⟨n, -, hn⟩ : ∃ n ≤ 2, (D.M ⊓ centralizer ({v} : Set G)).relIndex
        (F11.CElt D.M V₀ v) = 2 ^ n := by
      rcases hcase with rfl | hc
      · exact ⟨0, by norm_num, by simpa using ElevenThree.relIndex_cElt_bot D.M v⟩
      · exact ElevenThree.relIndex_cElt_eq_pow_two hc h4 hv hv0
    have hCT_le : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ v :=
      iInf_le_of_le v (iInf_le_of_le hv le_rfl)
    have hdC : p ∣ Nat.card (F11.CElt D.M V₀ v) :=
      hCV.trans (Subgroup.card_dvd_of_le hCT_le)
    have hmul := Subgroup.relIndex_mul_card (D.M ⊓ centralizer ({v} : Set G))
      (F11.CElt D.M V₀ v)
    rw [hn] at hmul
    have hcop : Nat.Coprime p (2 ^ n) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes h.p_prime Nat.prime_two).2 h.p_ne_two)
    have hd1 : p ∣ Nat.card ↥((D.M ⊓ centralizer ({v} : Set G)) ⊓ F11.CElt D.M V₀ v) := by
      rw [← hmul] at hdC
      exact hcop.dvd_of_dvd_mul_left hdC
    exact ⟨h.p_prime, hd1.trans (Subgroup.card_dvd_of_le inf_le_left)⟩

theorem r6_38_of_hyp18 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) : UC6.R6_38 D :=
  UC6.r6_38_of_sigma D fun q hq =>
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab
      (D.sig_prime q hq).1 (UC6S846.sp_of_mem_sig hSg h.not_solvable hq)

section Certified

theorem r18_15_of_case3 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) (hSg : UC6S846.SigmaStd D)
    (hKp : K_OmegaFourPlusNormalizer_pRank) (hs : P18_13_3 D V₀ V p L h) :
    R18_15At D V₀ V p L :=
  r18_15_of_dvd_cTilde D h
    (dvd_card_cTilde_of_case3 D h h1742 hs hSg hKp (r6_38_of_hyp18 D h hSg))

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
