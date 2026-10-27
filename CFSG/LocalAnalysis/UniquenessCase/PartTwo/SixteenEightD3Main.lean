module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Five
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10MBarFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem s16e_d3_exists_ctx (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hs : s15 D.M V₀ V hV L = 1) {r : ℕ} (hr2 : 2 ≤ r) (hr5 : r ≤ 5)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    (hS : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam 7)) :
    ∃ (Δ : Fin (r + 1) → Subgroup (Vtil V₀ V hV))
      (σ : ↥(Mbar D.M V₀ V hV) →* Equiv.Perm (Fin (r + 1))),
      s16e_d3_Ctx (Mbar D.M V₀ V hV) (lBar V₀ V hV L) r Δ σ := by
  obtain ⟨Δ, σ, hcfg⟩ := s16e_d3_cfg_of_symSumOfConj hS
  rw [s16c1610_dParam_seven] at hcfg
  exact ⟨Δ, σ, { cfg := hcfg
                 sq_eq_one := s15_Infra_vtil_sq_eq_one V₀ V hV
                 elem := hE
                 le := barSub_mono V₀ V hV hset.hyp151.le
                 normal := fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
                 two_le := hr2
                 le_five := hr5 }⟩

theorem s16e_d3_eq_of_mem_sig (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h16 : Hyp16 D V₀ V) {r : ℕ} {Δ : Fin (r + 1) → Subgroup (Vtil V₀ V hV)}
    {σ : ↥(Mbar D.M V₀ V hV) →* Equiv.Perm (Fin (r + 1))}
    (h : s16e_d3_Ctx (Mbar D.M V₀ V hV) (lBar V₀ V hV L) r Δ σ) {q : ℕ} (hq : q ∈ D.sig) :
    q = 7 ∨ (q = 3 ∧ r = 5) := by
  have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 h16 hV h4 hq
  obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
  exact s16e_d3_eq_of_three_le_pRank h hqp hq2 h3

theorem s16e_d3_two_lt_mBar (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hs : s15 D.M V₀ V hV L = 1) {r : ℕ} (hr3 : 3 ≤ r) (hr5 : r ≤ 5)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    (hS : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam 7)) :
    2 < mBar D.M V₀ V hV := by
  obtain ⟨Δ, σ, hctx⟩ := s16e_d3_exists_ctx D hV hset hs (by omega) hr5 hE hS
  exact s16c1610_two_lt_mParam_of_case4_seven (s15_Infra_vtil_sq_eq_one V₀ V hV) (by omega) hE
    (s16e_d3_le_pCoreOf hctx) hS (s16e_d3_three_le_pRank_seven hctx hr3)

theorem s16e_d3_mem_sig_seven_of_ne_five (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V hV L = 1) {r : ℕ} (hr2 : 2 ≤ r) (hr5 : r ≤ 5) (hne : r ≠ 5)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    (hS : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam 7)) :
    7 ∈ D.sig := by
  obtain ⟨Δ, σ, hctx⟩ := s16e_d3_exists_ctx D hV hset hs hr2 hr5 hE hS
  obtain ⟨q, hq⟩ := hSg.nonempty
  rcases s16e_d3_eq_of_mem_sig D hx h61 h127 h4 hset.hyp16 hctx hq with rfl | ⟨-, h5⟩
  · exact hq
  · exact absurd h5 hne

theorem s16e_d3_mem_sig_seven (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1110 : R1110Core D)
    (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {r : ℕ} (hr2 : 2 ≤ r) (hr5 : r ≤ 5)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    (hS : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam 7)) :
    7 ∈ D.sig := by
  by_cases hr : r = 5
  · subst hr
    obtain ⟨Δ, σ, hctx⟩ := s16e_d3_exists_ctx D hV hset hs hr2 hr5 hE hS
    exact s16e_d3_sig_five D hSg h127 h1110 h63 h126 h1211 h111 h6161ii h77 h1219 hV hset hconc hs
      hE (fun q hq => (s16e_d3_eq_of_mem_sig D hx h61 h127 h4 hset.hyp16 hctx hq).elim Or.inr
        fun h => Or.inl h.1)
      (s16e_d3_two_lt_mBar D hV hset hs (by norm_num) le_rfl hE hS)
  · exact s16e_d3_mem_sig_seven_of_ne_five D hx h4 hSg h61 h127 hV hset hs hr2 hr5 hr hE hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
