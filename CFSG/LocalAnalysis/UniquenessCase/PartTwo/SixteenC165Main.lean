module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Case
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_5_holds (D : Data G) (h3 : R16_3_2 D) (hx : DataExt D) (h115 : F11.R115 D)
    (h127 : R127 D) (h129 : R129_1 D) (h61 : UC6.R6_1 D) (h638 : UC6.R6_38 D)
    (h640 : UC6.R6_40_2 D) : R16_5 D := by
  intro V₀ V L hV hSet hne hconc hΩ
  have hS : Sect16 D V₀ V L hV := ⟨hSet, hne, hconc⟩
  have hH : Hyp125 D V₀ V := hSet.hyp16.hyp125
  have hH11 : F11.Hyp11 D V₀ V := hH.hyp11 h127
  have hc4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D hSet.hyp16
  have hMn : D.M ≤ normalizer (V : Set G) := hH.pairFacts.le_normalizer
  have hMn₀ : D.M ≤ normalizer (V₀ : Set G) := hH.pairFacts.le_normalizer₀
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hMn hMn₀
  obtain ⟨S, hK, hΩc, hΩM, hMN⟩ := exists_omegaModel_bar h3 hS hΩ
  have hrange : (barHom V₀ V hV hMst).range = Mbar D.M V₀ V hV := range_barHom V₀ V hV hMst
  have hker : (barHom V₀ V hV hMst).ker = (F11.CTilde D.M V₀ V).subgroupOf D.M :=
    ker_barHom V₀ V hV hMn hMst
  have hΩr : S.omega ≤ (barHom V₀ V hV hMst).range := hrange ▸ hΩM
  have hrN : (barHom V₀ V hV hMst).range ≤ OmegaModel.omegaNorm S := hrange ▸ hMN
  have hrk : ∀ p ∈ D.sig, ∃ E : Subgroup ↥D.M, IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E ∧
      ∀ E' : Subgroup ↥D.M, IsElemAbelian p E' → E' ≤ (barHom V₀ V hV hMst).ker →
        Nat.card E' ≤ p := by
    intro p hp
    obtain ⟨E, hE, hEc, hEk⟩ := exists_rank_data h115 hH11 hc4 hp
    exact ⟨E, hE, hEc, fun E' hE' hle => hEk E' hE' (hker ▸ hle)⟩
  have hsig : ∀ p ∈ D.sig, p = 3 ∨ p = 7 := by
    intro p hp
    obtain ⟨E, hE, hEc, hEk⟩ := hrk p hp
    exact S.eq_three_or_seven_of_pRank hK (barHom V₀ V hV hMst) hrN (D.sig_prime p hp).1
      (D.sig_prime p hp).2 hE hEc hEk
  have h7 : 7 ∉ D.sig := by
    intro h7
    by_cases hdvd : 7 ^ 3 ∣ Nat.card (barHom V₀ V hV hMst).range
    · obtain ⟨Y, hYN, hYp, hYc⟩ :=
        S.exists_isPGroup_noncyclic_le_normalizer_of_seven_pow_three_dvd hK hΩc
          (barHom V₀ V hV hMst) hΩr hrN hdvd (isPGroup_two_subgroupOf_sylow D).1
          (isPGroup_two_subgroupOf_sylow D).2
      exact false_of_noncyclic_seven_normalizer D h61 h640 h7 hYN hYp hYc
    · obtain ⟨E, hE, hEc, hEk⟩ := hrk 7 h7
      exact false_of_seven_not_pow_three_dvd D h61 h129 hH hV hc4 h7 hMst S hK hΩr hE hEc hEk hdvd
  have hsig3 : D.sig = {3} := by
    ext p
    rw [Set.mem_singleton_iff]
    constructor
    · intro hp
      rcases hsig p hp with h | h
      · exact h
      · exact absurd (h ▸ hp) h7
    · rintro rfl
      obtain ⟨q, hq⟩ := hx.sig_nonempty
      rcases hsig q hq with h | h
      · exact h ▸ hq
      · exact absurd (h ▸ hq) h7
  refine ⟨hsig3, ?_⟩
  have h3sig : 3 ∈ D.sig := by rw [hsig3]; rfl
  obtain ⟨E, hE, hEc, -⟩ := hrk 3 h3sig
  have hOp : UC22.F10.OpRes 3 D.M = D.M := h638 3 Nat.prime_three (by norm_num) (Or.inl h3sig)
  have hop : ∀ (N : Subgroup ↥D.M) [N.Normal], IsPGroup 3 (↥D.M ⧸ N) → N = ⊤ :=
    fun N _ hq => UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 Nat.prime_three hOp N hq
  have h3ker : 3 ∣ Nat.card (barHom V₀ V hV hMst).ker :=
    S.three_dvd_card_ker hK hΩc (barHom V₀ V hV hMst) hrN hop hE hEc
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg 1) V.one_mem).1
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv] at h3ker
  exact h3ker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
