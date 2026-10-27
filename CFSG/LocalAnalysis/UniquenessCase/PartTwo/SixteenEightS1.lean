module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Fam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Z7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Omega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5False

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Concl168Four (D : Data G) (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) (L : Subgroup G) : Prop :=
  Case168_1 D V₀ V hV L ∨ Case168_2Star D V₀ V hV L ∨ Case168_3 D V₀ V hV L ∨
    Case168_4 D V₀ V hV L ∨ Case168_5Star D V₀ V hV L ∨ Case168_7 D V₀ V hV L

theorem concl168_of_four {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Concl168Four D V₀ V hV L) : Concl168 D V₀ V hV L := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem s16e_s1_survivors (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1110 : R1110Core D) (h164 : R16_4 D) (h165 : R16_5 D)
    (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h167 : ¬ Concl167 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 1)
    (h163 : Concl163 D V₀ V hV L) : Concl168Four D V₀ V hV L := by
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hrkT : ∀ n : ℕ, rk ↥(wTil V₀ V hV L) = n → rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = n := by
    intro n hn
    rw [← hwT]
    exact hn
  have hsig3 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 8 → D.sig = {3} := fun hrk =>
    s16e_sig_eq_three_of_rk_le_eight D hx h4 h61 h127 hset.hyp16 hV hrk
  have hfalse4 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 4 → False := fun hrk =>
    s16e_false_of_rk_le_four D hx h4 h61 h127 hset.hyp16 hV hrk
  rcases h163 with h162 | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h162 with h153 | h | h | h | h | h | h | h | h | h
    · rcases h153 with h | h | h
      · exact (s16e_false_of_sig_pRank_three hx h4 h.2.2.1 h.2.2.2.1).elim
      · exact (s16e_not_case153_2 hx h4 h).elim
      · obtain ⟨-, hrk⟩ := r1613g_case153_3_summary D hconc h
        have hrk' : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 2 := by
          rw [← hwT]
          exact hrk
        exact (hfalse4 (by omega)).elim
    · exact absurd h.2 (by omega)
    · rcases s16e_s1_case2_of_162_2 D hx h4 h61 h127 h1214 h638 hV hset hL hconc h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact absurd h.2.2 (by omega)
    · obtain ⟨hP, hrk, -⟩ := h
      have hrk6 := hrkT _ hrk
      exact Or.inr (Or.inr (Or.inl ⟨hP, hrk6, hsig3 (by omega)⟩))
    · obtain ⟨⟨r, hE, hrk⟩, -⟩ := h
      have hr := s16e_one_le_of_elemAbelianOfRank hL hE
      by_cases hr1 : r = 1
      · subst hr1
        have hrk' := hrkT _ hrk
        exact (hfalse4 (by omega)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (s16e_s1_case4_of_elem D hx h4 hSg h61 h127 h1214 h638 h1110 h63 h126 h1211 h111
            h6161ii h77 h1219 hV hset hconc hs (Or.inl rfl) (by omega) hE
            (by rw [s16c1610_dParam_three]; omega)))))
    · exact (s16e_false_of_sig_pRank_three hx h4 h.2.2.2.1 h.2.2.2.2).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (s16e_s1_case5_of_omegaPlus D hx h4 h61 h127 h1217 hV hset hL hconc h)))))
    · exact absurd h.2 (by omega)
    · exact (s16e_false_of_sig_pRank_three hx h4 h.2.2.2.1 h.2.2.2.2).elim
  · exact absurd h.2.2 (by omega)
  · exfalso
    apply h167
    have hsig := (h165 V₀ V L hV hset hL hconc h.1).1
    have hnat : NatOmegaPlus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 4 3 := by
      have := h.2.1
      rw [hwT] at this
      exact this
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, hnat, hsig⟩)))))
  · exact absurd h.2.2.1 (by omega)
  · exact absurd h.2.2 (by omega)
  · exact absurd h.2 (by omega)
  · exact (s16e_false_of_sig_pRank_three hx h4 h.2.2.2.1 h.2.2.2.2).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exfalso
    apply h167
    have hten : NatTensor (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 3 1 := by
      have := h.2.1
      rw [hwT] at this
      exact this
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, hten, h.2.2.2⟩))))))
  · exact absurd h.2.2 (by omega)
  · exact (s16e_d5_false D h164 hx h4 h61 h127 h1214 hV hset hconc hs h).elim
  · obtain ⟨r, hE, hrk⟩ := h
    have hr := s16e_one_le_of_elemAbelianOfRank hL hE
    by_cases hr1 : r = 1
    · subst hr1
      have hrk' := hrk
      exact (s16e_s1_false_of_z7 D hx h4 h61 h127 hV hset hconc hs hE (by omega)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (s16e_s1_case4_of_elem D hx h4 hSg h61 h127 h1214 h638 h1110 h63 h126 h1211 h111
          h6161ii h77 h1219 hV hset hconc hs (Or.inr rfl) (by omega) hE
          (by rw [s16c1610_dParam_seven]; omega)))))
  · exact absurd h.2.2 (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
