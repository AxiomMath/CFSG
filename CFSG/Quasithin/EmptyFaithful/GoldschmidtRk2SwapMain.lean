module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2SwapMin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2SwapBlk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclMain
public import CFSG.Quasithin.EmptyFaithful.S151S4E

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Main

theorem rankTwoNoSwap_of (h118 : TheoremC118) (h126 : TheoremC126) (h1416 : StageLemma1416)
    (h15 : StageLemma1515CE) : Input15120RankTwoNoSwap := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hB hSN P hP hBP
  obtain ⟨Y, _, _, ρ, n, hn, hY, hsurj, hq_le, hcent, hker⟩ := rkModel L hB
  set S := s1516 T Z₁ with hSdef
  have hq := hc.ctx.qtfe
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hSL : IsSylowTwoOf (S ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hU : IsSylowTwoOf (((S ⊓ L).subgroupOf L).map ρ) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSL) ρ hsurj
  have hY' : IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y ∨ IsPSp4 2 n Y ∨ IsG2 2 n Y :=
    hY.elim Or.inl fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h)))
      fun h => Or.inr (Or.inr (Or.inr h))
  obtain ⟨Pk, hPk⟩ := rank2Pkg_exists hn hY' hU
  have hdata : RkData L (S ⊓ L) ρ _ Pk := ⟨hsurj, hq_le, hcent, hSL, rfl, hPk, hker _ Pk hPk⟩
  have hperfQ := perfect_sup_pCore_of_quasi hc.hL.quasi
  have hQ : pCoreOf 2 L ≤ S ⊓ L := pCoreOf_two_le_of_sylowIn hSL.1 hSL.2.1 hSL.2.2
  have hSSL : ∀ t ∈ S, t ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := fun t ht =>
    zb_mem_normalizer_inf (Subgroup.le_normalizer ht) (hSN ht)
  have hfix : ∀ j, S ≤ Subgroup.normalizer (parUp L ρ (Pk j) : Set G) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨j₀, hj₀⟩ := hnot
    obtain ⟨t, ht, htn⟩ := IsConcreteLE.not_le_iff_exists.1 hj₀
    have hfin : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    have hsw : B6.conjSub t (parUp L ρ (Pk 0)) = parUp L ρ (Pk 1) := by
      rcases swap_or_fix hdata hperfQ hQ (hSN ht) (hSSL t ht) with ⟨h0, h1⟩ | ⟨h0, -⟩
      · exfalso
        rcases hfin j₀ with rfl | rfl
        · exact htn (mem_normalizer_of_conjSub_eq h0)
        · exact htn (mem_normalizer_of_conjSub_eq h1)
      · exact h0
    have hLloc : L ∈ cComp (L ⊔ S) := cComp_of_isLocal hc.hL.mem.2
    have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLloc
    have hL0 : L ≠ ⊥ := ne_bot_of_mem_cComp hLloc
    have hmin : IsMinParabolicOf (L ⊔ S) (L ⊔ S) :=
      isMinParabolic_of_swap hdata hperfQ hSN hS2 rfl ht hsw
    have hno3 : ¬ C126Third (L ⊔ S) S := not_c126Third_of_typeB hB hSN hS2 hperf hc.hL.quasi
    have hHG : L ⊔ S ≤ g1_1516 Z₁ := sup_le hc.hL.mem.1 (s1516_le_g1 T Z₁)
    have hOp : pCoreOf 2 L ≠ ⊥ := by
      intro h
      apply hL0
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ pCoreOf 2 L := hchar ⟨hx, by
        rw [h]
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Subgroup.mem_bot.mp hy]
          simp⟩
      rw [h] at h1
      exact h1
    have hpc : pCoreOf 2 (L ⊔ S) ≠ ⊥ := by
      have hHN : L ⊔ S ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
        sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
          (fun s hs => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hSN hs))
      have h2 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hHN
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      exact ne_bot_of_le_ne_bot hOp h2
    have hcharH : CharTwo (L ⊔ S) := zb_charTwo_sup hSN hS2 hchar
    have hRsyl : IsSylowTwoOf S (L ⊔ S) := S151S4.sylow_sup_of_normalizes hSN hS2 hSL
    have hLM : ¬ L ≤ M :=
      lemma_15_1_20_one (h1416 G T Mc hq).1 hc.ctx.mf (h15 G T Mc M hq hc.ctx.mf hc.ctx.ce) hc.hL
    rcases S151S4.star_general_sub h118 h126 hc.ctx hc.h17 hc.h18 (R := S) (H := L ⊔ S)
        (C1GN.baum_le S) le_rfl hHG hRsyl hpc hcharH hmin hno3 with h | h
    · exact hLM (le_sup_left.trans h)
    · exact hc.hL.not_le (le_sup_left.trans h)
  have hSLP : S ⊓ L ≤ P :=
    (le_inf (inf_le_right) (Subgroup.le_normalizer (H := S ⊓ L))).trans hBP
  obtain ⟨j, hj⟩ := exists_le_parUp hdata hperfQ hQ hP.1.1 hSLP hP.2.1
  have hPj : parUp L ρ (Pk j) = P :=
    hP.2.2 _ (isMaxParabolic2_parUp hdata j).1 (parUp_ne_top hdata j) hj
  rw [← hPj]
  exact hfix j

end Main

section Final

theorem input15120RankTwoExclF_of' (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hl2 : Input15120L2Block)
    (h118 : TheoremC118) (h126 : TheoremC126) (h1416 : StageLemma1416)
    (h15 : StageLemma1515CE) : Input15120RankTwoExclF :=
  input15120RankTwoExclF_of h37 h38 hl2 (rankTwoNoSwap_of h118 h126 h1416 h15)

end Final

end CFSG.Quasithin.Rk2
