module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_false_of_rk_le_four (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V)
    (hV : IsElemAbelian 2 V) (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 4) : False := by
  obtain ⟨p, hp, hp2, h3⟩ := s16e_exists_pRank_mBar D hx h61 h127 h16 hV h4
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hlt := s16e_pRank_lt_three_of_rk_le_four hT hrk (s16e_card_eq_two_pow_rk_top hT) hp hp2
    (Mbar D.M V₀ V hV)
  omega

theorem s16e_mbar_index_ne_three_of_opRes (D : Data G)
    (hop : UC22.F10.OpRes 3 D.M = D.M)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (N : Subgroup ↥(Mbar D.M V₀ V hV)) [N.Normal] : N.index ≠ 3 := by
  intro hidx
  have hMn : D.M ≤ normalizer (V : Set G) := h16.hyp125.pairFacts.le_normalizer
  have hMn₀ : D.M ≤ normalizer (V₀ : Set G) := h16.hyp125.pairFacts.le_normalizer₀
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hMn hMn₀
  have hrange : (barHom V₀ V hV hMst).range = Mbar D.M V₀ V hV := range_barHom V₀ V hV hMst
  let ψ : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
    (barHom V₀ V hV hMst).codRestrict (Mbar D.M V₀ V hV) (fun m => by
      rw [← hrange]
      exact ⟨m, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : MulAut (Vtil V₀ V hV)) ∈ (barHom V₀ V hV hMst).range := by
      rw [hrange]
      exact x.2
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, Subtype.ext hm⟩
  haveI : (N.comap ψ).Normal := Subgroup.normal_comap ψ
  have hidx' : (N.comap ψ).index = 3 := by
    rw [Subgroup.index_comap_of_surjective N hψ]
    exact hidx
  have hpg : IsPGroup 3 (↥D.M ⧸ N.comap ψ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one]
    exact hidx'
  have htop := UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 Nat.prime_three
    hop (N.comap ψ) hpg
  rw [htop, Subgroup.index_top] at hidx'
  omega

theorem s16e_mbar_index_ne_three (D : Data G) (h638 : UC6.R6_38 D) (h3 : 3 ∈ D.sig)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (N : Subgroup ↥(Mbar D.M V₀ V hV)) [N.Normal] : N.index ≠ 3 :=
  s16e_mbar_index_ne_three_of_opRes D
    (h638 3 Nat.prime_three (by norm_num) (Or.inl h3)) h16 hV N

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
