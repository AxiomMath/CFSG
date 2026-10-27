module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Cond
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s16h_e3_CycTwoP5_orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

private lemma s16h_e3_CycTwoP5_cTable_five : s16h_cTable 5 4 5 ≤ 1 := by
  rw [s16h_cTable, s16h_e3_CycTwoP5_orderOf_two_zmod_five,
    show (5 : ℕ) - 1 = 4 by norm_num]
  norm_num [Nat.lcm]

theorem s16h_e3_cyclic_two_p5
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp5 : p = 5) (hm : rk ↥(wTil V₀ V hV L) = 4) :
    ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  subst p
  have h5 : 5 ∈ D.sig := by
    obtain ⟨q0, hq0⟩ := S.hx.sig_nonempty
    rcases hres q0 hq0 with hq | hq
    · exact hq ▸ hq0
    · exact absurd hq.1 (by norm_num)
  have h3 : 3 ≤ CFSG.Open.pRank 5 D.M := by
    have hp3 := s16h_pRank_eq_three D S hr3 h5
    omega
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hLp.2]
    exact ⟨2, by norm_num⟩
  have hBBhV : s16h_BlockBound (Mbar D.M V₀ V hV) (barSub V₀ V hV L) 5 1 := by
    have hfix : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) ⊓
        fixV (barSub V₀ V hV L) = ⊥ := by
      have hb := s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
      rwa [wTil, lBar] at hb
    have hbase := s16h_blockBound_of_cyclic (s15_Infra_vtil_sq_eq_one V₀ V hV)
      Nat.prime_five Nat.prime_five (by norm_num) (by norm_num)
      (A := Mbar D.M V₀ V hV) (L := barSub V₀ V hV L) hLp.1 hLp.2 hfix
    have hrk : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L)) = 4 := hm
    refine s16h_blockBound_mono (by norm_num : 0 < 5) le_rfl ?_ hbase
    rw [hrk]
    exact s16h_e3_CycTwoP5_cTable_five
  have hVeq : hV = h.hyp151.isElemAbelian := Subsingleton.elim hV _
  have hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) 5 1 := hVeq ▸ hBBhV
  have hgoal := s16h_uniqueMax_of_blockBound_one_two D S.h61 S.h127 h hs2.le h5 h3 hBB
  intro w hw hw1
  exact hgoal w (hVeq ▸ hw) hw1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
