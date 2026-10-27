module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicFiveRankFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34ThreeMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem concl163F_or_cyclic_three_rank_six_s1_of_conc4_133
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {t : MulAut (Vtil V₀ V hV)}
    (c : S168e3Ctx D V₀ V L hV)
    (h133 : Conc4_133 (Mbar D.M V₀ V hV) t (lBar V₀ V hV L)) :
    Concl163F D V₀ V hV L ∨
      (IsCyclicOrd ↥(lBar V₀ V hV L) 3 ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 6 ∧
        s15 D.M V₀ V hV L = 1) := by
  have hpos : 0 < s15 D.M V₀ V hV L := s15_Eleven_pos_s D c.setting.hyp151 hV
  have hs1 : 1 ≤ s15 D.M V₀ V hV L := hpos
  have hcycToElem : ∀ {X : Type} [Group X] {q : ℕ}, IsCyclicOrd X q → IsElemAbelianOfRank q 1 X := by
    intro X _ q h
    obtain ⟨hcyc, hcard⟩ := h
    refine ⟨?_⟩
    rw [← hcard]
    exact (zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.funUnique (Fin 1) (ZMod (Nat.card X))).symm.toMultiplicative
  have to163F_of_162 : Concl162 D V₀ V hV L → Concl163F D V₀ V hV L := fun h => Or.inl h
  have to162_of_153_3 : Case153_3 D V₀ V hV L → Concl162 D V₀ V hV L :=
    fun h => Or.inl (Or.inr (Or.inr h))
  have to162_of_162_3 : Case162_3 D V₀ V hV L → Concl162 D V₀ V hV L :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))
  have to162_of_162_4 : Case162_4 D V₀ V hV L → Concl162 D V₀ V hV L :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have to162_of_162_5 : Case162_5 D V₀ V hV L → Concl162 D V₀ V hV L :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have to163F_of_163_9 : Case163_9 D V₀ V hV L → Concl163F D V₀ V hV L := by
    intro h
    unfold Concl163F
    iterate 9 right
    exact Or.inl h
  have to163F_of_163_10 : Case163_10 V₀ V hV L → Concl163F D V₀ V hV L := by
    intro h
    unfold Concl163F
    iterate 10 right
    exact Or.inl h
  have to163F_of_163_11 : Case163_11 V₀ V hV L → Concl163F D V₀ V hV L := by
    intro h
    unfold Concl163F
    iterate 11 right
    exact Or.inl h
  have to163F_of_163_12 : Case163_12 D V₀ V hV L → Concl163F D V₀ V hV L := by
    intro h
    unfold Concl163F
    iterate 12 right
    exact h
  obtain ⟨p, -, -, -, -, hcases⟩ := h133
  rcases hcases with
      ⟨hC3, h2 | h4 | h6⟩ | ⟨hC5, h5⟩ | ⟨hP3, h6⟩ | ⟨hE9, h8, -, -⟩ |
      ⟨hC7, h3 | h6⟩ | ⟨r, m, hpm, hr2, hEr, hrk, -⟩ | ⟨hE9, h6, -⟩
  ·
    have h153 : Case153_3 D V₀ V hV L := by
      refine ⟨⟨L, le_rfl, hC3, ?_, ?_⟩, Or.inl c.setting.hyp16.small⟩
      · exact s16c34_isDirectProdOfConj_self _ _ inf_le_right
      · exact s16c34_alternatingNatural_of_cyclic_three (s15_Infra_vtil_sq_eq_one V₀ V hV) hC3 h2
    exact Or.inl (to163F_of_162 (to162_of_153_3 h153))
  ·
    have h162_5 : Case162_5 D V₀ V hV L := by
      refine ⟨⟨1, hcycToElem hC3, ?_⟩, hs1⟩
      rw [show 2 * (1 + 1) = 4 by norm_num]
      change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 4
      exact h4
    exact Or.inl (to163F_of_162 (to162_of_162_5 h162_5))
  ·
    by_cases hs : s15 D.M V₀ V hV L = 1
    · exact Or.inr ⟨hC3, h6, hs⟩
    · have hs2 : 2 ≤ s15 D.M V₀ V hV L := by omega
      have h163_9 : Case163_9 D V₀ V hV L := by
        refine ⟨hC3, ?_, hs2⟩
        change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 6
        exact h6
      exact Or.inl (to163F_of_163_9 h163_9)
  ·
    exact Or.inl (to163F_of_162 (to162_of_162_3 (case162_3_of_cyclic_five_rank_four c hC5 h5)))
  ·
    have h162_4 : Case162_4 D V₀ V hV L := by
      refine ⟨hP3, ?_, hs1⟩
      change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 6
      exact h6
    exact Or.inl (to163F_of_162 (to162_of_162_4 h162_4))
  ·
    have h163_10 : Case163_10 V₀ V hV L := by
      refine ⟨hE9, ?_⟩
      change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 8
      exact h8
    exact Or.inl (to163F_of_163_10 h163_10)
  ·
    have hs : 1 < s15 D.M V₀ V hV L :=
      s16c34_one_lt_s15_of_rk_wTil_le_three D c.std.hx c.std.h61 c.std.h127 c.std.h1217
        c.setting c.ne (le_of_eq h3)
    have h163_12 : Case163_12 D V₀ V hV L := by
      refine ⟨hC7, ?_, hs⟩
      change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 3
      exact h3
    exact Or.inl (to163F_of_163_12 h163_12)
  ·
    have h163_11 : Case163_11 V₀ V hV L := by
      refine ⟨1, hcycToElem hC7, ?_⟩
      rw [show 3 * (1 + 1) = 6 by norm_num]
      change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 6
      exact h6
    exact Or.inl (to163F_of_163_11 h163_11)
  ·
    rcases hpm with ⟨hp3, hm2⟩ | ⟨hp7, hm3⟩
    · have hEr' : IsElemAbelianOfRank 3 r ↥(lBar V₀ V hV L) := by rwa [hp3] at hEr
      have hrk' : rk ↥(wTil V₀ V hV L) = 2 * (r + 1) := by
        rw [hm2] at hrk
        change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) =
          2 * (r + 1)
        rw [hrk]
        ring
      have h162_5 : Case162_5 D V₀ V hV L := ⟨⟨r, hEr', hrk'⟩, hs1⟩
      exact Or.inl (to163F_of_162 (to162_of_162_5 h162_5))
    · have hEr' : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L) := by rwa [hp7] at hEr
      have hrk' : rk ↥(wTil V₀ V hV L) = 3 * (r + 1) := by
        rw [hm3] at hrk
        change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) =
          3 * (r + 1)
        rw [hrk]
        ring
      have h163_11 : Case163_11 V₀ V hV L := ⟨r, hEr', hrk'⟩
      exact Or.inl (to163F_of_163_11 h163_11)
  ·
    have h162_5 : Case162_5 D V₀ V hV L := by
      refine ⟨⟨2, hE9, ?_⟩, hs1⟩
      rw [show 2 * (2 + 1) = 6 by norm_num]
      change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 6
      exact h6
    exact Or.inl (to163F_of_162 (to162_of_162_5 h162_5))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
