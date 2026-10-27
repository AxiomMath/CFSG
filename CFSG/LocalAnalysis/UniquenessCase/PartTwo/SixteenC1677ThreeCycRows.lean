module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCyc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycChoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycDich
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_row_z3_four {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hE : IsElemAbelianOfRank 3 1 ↥(lBar V₀ V hV L)) (hrk : rk ↥(wTil V₀ V hV L) = 4) :
    Choice168F D V₀ V hV := by
  obtain ⟨t₀, -, -, -, -, hW₀⟩ := c.conc
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := hW₀.le
  have hwtop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hWL : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by simpa only [wTil, lBar] using hwtop
  have hT : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrk4 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 4 := by
    rw [← hwtop]
    exact hrk
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 4 := by
    rw [s16e_card_eq_two_pow_rk_top hT, hrk4]
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  have hind : IsIndivisible (Mbar D.M V₀ V hV) :=
    TwelveSeventeen.isIndivisible D c.std.hx c.std.h61 c.std.h127 c.std.h1214
      c.setting.hyp16.hyp125
  have hO2 : ∀ P : Subgroup (MulAut (Vtil V₀ V hV)), P ≤ Mbar D.M V₀ V hV →
      (P.subgroupOf (Mbar D.M V₀ V hV)).Normal → IsPGroup 2 ↥P → P = ⊥ :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.setting.hyp16.hyp125 hP hN h2
  have hsig : D.sig = {3} :=
    c.sig_eq_singleton_of_pRank_lt_two 3 fun q hq hq2 hq3 =>
      s168e3_pRank_lt_two_of_z3_four hT hcard hLA hLn hE hWL hq hq2 hq3
  have h3σ : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  refine s168e3_choice_of_cyclic c (Or.inl ⟨rfl, rfl⟩) hsig ?_
  intro t ht ht2 ht1 htr hWt
  rcases s168e3_z3_four_dichotomy hT hcard hLA hLn hE hWL hind hO2 ht ht2 ht1 htr hWt
      Nat.prime_three (by norm_num) (c.two_le_pRank_mbar h3σ) with
    hTool | ⟨K, hK, hKc, hKrk, hKn, -⟩
  · exact (s168e3_false_of_tool c Nat.prime_three h3σ hTool).elim
  · exact ⟨K, hK, hKc, hKrk, hKn⟩

theorem s168e3_row_z7_six {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hE : IsElemAbelianOfRank 7 1 ↥(lBar V₀ V hV L)) (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    Choice168F D V₀ V hV := by
  obtain ⟨t₀, ht₀, ht₀2, ht₀1, ht₀tr, hW₀⟩ := c.conc
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := hW₀.le
  have hwtop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hWL : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by simpa only [wTil, lBar] using hwtop
  have hT : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrk6 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← hwtop]
    exact hrk
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top hT, hrk6]
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  have hind : IsIndivisible (Mbar D.M V₀ V hV) :=
    TwelveSeventeen.isIndivisible D c.std.hx c.std.h61 c.std.h127 c.std.h1214
      c.setting.hyp16.hyp125
  have hO2 : ∀ P : Subgroup (MulAut (Vtil V₀ V hV)), P ≤ Mbar D.M V₀ V hV →
      (P.subgroupOf (Mbar D.M V₀ V hV)).Normal → IsPGroup 2 ↥P → P = ⊥ :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.setting.hyp16.hyp125 hP hN h2
  obtain ⟨p₀, hp₀⟩ := c.std.hx.sig_nonempty
  have h3lt : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) < 2 := by
    rcases s168e3_z7_six_dichotomy hT hcard hLA hLn hE hWL hind hO2 ht₀ ht₀2 ht₀1 ht₀tr hW₀
        (D.sig_prime p₀ hp₀).1 (D.sig_prime p₀ hp₀).2 (c.two_le_pRank_mbar hp₀) with
      hTool | ⟨-, -, -, -, -, h7⟩
    · exact (s168e3_false_of_tool c (D.sig_prime p₀ hp₀).1 hp₀ hTool).elim
    · exact h7 3 Nat.prime_three (by norm_num) (by norm_num)
  have hsig : D.sig = {7} :=
    c.sig_eq_singleton_of_pRank_lt_two 7 fun q hq hq2 hq7 => by
      by_cases hq3 : q = 3
      · subst hq3
        exact h3lt
      · exact s168e3_pRank_lt_two_of_z7_six hT hcard hLA hLn hE hWL hq hq2 hq3 hq7
  have h7σ : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  refine s168e3_choice_of_cyclic c (Or.inr ⟨rfl, rfl⟩) hsig ?_
  intro t ht ht2 ht1 htr hWt
  rcases s168e3_z7_six_dichotomy hT hcard hLA hLn hE hWL hind hO2 ht ht2 ht1 htr hWt
      Nat.prime_seven (by norm_num) (c.two_le_pRank_mbar h7σ) with
    hTool | ⟨K, hK, hKc, hKrk, hKn, -⟩
  · exact (s168e3_false_of_tool c Nat.prime_seven h7σ hTool).elim
  · exact ⟨K, hK, hKc, hKrk, hKn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
