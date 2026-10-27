module

public import CFSG.Quasithin.MS93.SkItems
public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] {M T L : Subgroup G}

section Cases

theorem MS93ConclAS.of_case2 (h : MS93Case2 M L) : MS93ConclAS M T L := Or.inl h

theorem MS93ConclAS.of_case3 (h : MS93Case3 M T L) : MS93ConclAS M T L := Or.inr (Or.inl h)

theorem MS93ConclAS.of_case4 (h : MS93Case4 M L) : MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inl h))

theorem MS93ConclAS.of_case5 (hX : Xq M ≤ Zq M L ⊔ Uq M T L) (h : MS93Case5 (Vq M L) L) :
    MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨hX, h⟩)))

theorem MS93ConclAS.of_case6 (h : MS93Case6 M L) : MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem MS93ConclAS.of_case8 (h : MS93Case8 M T L) : MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem MS93ConclAS.of_case10 (h : MS93Case10 M L) : MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem MS93ConclAS.of_case11 (hX : Xq M ≤ Zq M L ⊔ Uq M T L) (h : MS93Case11 (Vq M L) T L) :
    MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hX, h⟩)))))))

theorem MS93ConclAS.of_case13 (hX : Xq M ≤ Zq M L ⊔ Uq M T L) (h : MS93Case13 (Vq M L) T L) :
    MS93ConclAS M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hX, h⟩)))))))

theorem QjInfo.mono {T₁ W : Subgroup G} {q : ℕ} (h : QjInfo T₁ L W q) (hT : T₁ ≤ T) :
    QjInfo T L W q := by
  intro SL hSL hTN
  obtain ⟨X, hX, hidx, hXT⟩ := h SL hSL (hT.trans hTN)
  exact ⟨X, hX, hidx, hXT.trans hT⟩

theorem MS93Case11.mono {V T₁ : Subgroup G} (h : MS93Case11 V T₁ L) (hT : T₁ ≤ T) :
    MS93Case11 V T L := by
  obtain ⟨n, F, hF, hFt, α, h1, h2, h3, h4, h5⟩ := h
  exact ⟨n, F, hF, hFt, α, h1, h2, h3, h4, h5.mono hT⟩

theorem MS93Case13.mono {V T₁ : Subgroup G} (h : MS93Case13 V T₁ L) (hT : T₁ ≤ T) :
    MS93Case13 V T L := by
  obtain ⟨n, F, hF, hFt, α, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨n, F, hF, hFt, α, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11.mono hT⟩

end Cases

variable [Finite G]

section Aux

theorem PUHyp.critDist_even (h : PUHyp M T L) : Even (critDist (puAmalgam h.le)) :=
  ms21_v (puAmalgam h.le) h.hyp20

theorem PUHyp.Uq_inf_Dq_eq_of_card (h : PUHyp M T L) (h2 : Nat.card ↥(Uq M T L ⊓ Dq M L) = 2) :
    Uq M T L ⊓ Dq M L = Uq M T L ⊓ Subgroup.centralizer (M : Set G) := by
  refine le_antisymm (le_inf inf_le_left (le_centralizer_of_card_eq_two
    (le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_Dq h.le_normalizer)) h2))
    ?_
  rw [h.Uq_inf_Dq]
  exact inf_le_inf_left _ (Subgroup.centralizer_le h.L_le)

theorem case2_or_case3_of_sp4 (h37 : S37) (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    (hVU : Vq M L = Uq M T L) {k : ℕ}
    (hk : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) k) :
    MS93Case2 M L ∨ MS93Case3 M T L := by
  have hVX : Vq M L ≤ Xq M := hVU ▸ h.Uq_le_Xq
  rcases hk with ⟨-, N, hN⟩ | ⟨hk2, F, hF, hFt, α, hcard, hsurj, hnat⟩
  · refine Or.inl ⟨hVX, N, ?_⟩
    rw [hVU]
    exact hN
  · refine Or.inr ⟨hVX, k, F, hF, hFt, α, hk2, hcard, hsurj, by rw [hVU]; exact hnat, ?_⟩
    intro hodd
    have hnat' : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1 := by
      rw [h.Uq_inf_Zq]
      exact hnat
    exact h37 G M T L h hb k F hF hFt α hk2 hcard hsurj hnat' hodd

end Aux

theorem ms93ConclAS_of_critDist_eq_two (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18)
    (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2) : MS93ConclAS M T L := by
  obtain ⟨h36a, h36b⟩ := h36 G M T L h hb
  by_cases hVU : Vq M L = Uq M T L
  swap
  · have hD := h36a.resolve_left hVU
    exact MS93ConclAS.of_case5 hD.2.1.le (h18 G M T L h hb hVU hD)
  have hVX : Vq M L ≤ Xq M := hVU ▸ h.Uq_le_Xq
  rcases h36b with hUD | ⟨k, hk⟩ | hii
  ·
    have hUZ : Uq M T L ⊓ Zq M L = ⊥ := by rw [h.Uq_inf_Zq, ← h.Uq_inf_Dq, hUD]
    obtain ⟨-, -, h32c⟩ := h32 G M T L h
    rcases h32c with ⟨-, -, n, F, hF, hFt, α, hcard, hsurj, hnat⟩ | ⟨-, -, hU, hA6⟩ |
        ⟨hX, -, n, F, hF, hFt, α, hcard, hsurj, hnat⟩ | ⟨-, hcard2, -, -⟩ |
        ⟨-, -, -, α, hsurj, hnat⟩ | ⟨k, hvi⟩ | ⟨-, -, ⟨hU, hG2⟩, -⟩
    · refine MS93ConclAS.of_case4 ⟨hVX, n, F, hF, hFt, α, hcard, hsurj, ?_⟩
      rw [hVU]
      exact hnat
    · refine MS93ConclAS.of_case6 ⟨hVX, ?_⟩
      rw [hVU]
      exact ⟨hU, hA6⟩
    · refine MS93ConclAS.of_case5 hX.le ⟨n, F, hF, hFt, α, hcard, hsurj, ?_⟩
      rw [hVU]
      exact hnat
    · rw [inf_comm, hUZ, Subgroup.card_bot] at hcard2
      exact absurd hcard2 (by norm_num)
    · refine MS93ConclAS.of_case4 ⟨hVX, 1, ZMod 2, inferInstance, inferInstance, α,
        by rw [ZMod.card, pow_one], hsurj, ?_⟩
      rw [hVU]
      exact hnat
    · rw [h.Uq_inf_Zq] at hvi
      rcases case2_or_case3_of_sp4 h37 h hb hVU hvi with h2 | h3
      · exact MS93ConclAS.of_case2 h2
      · exact MS93ConclAS.of_case3 h3
    · refine MS93ConclAS.of_case10 ⟨hVX, ?_⟩
      rw [hUZ, intSub_bot] at hG2
      rw [hVU]
      exact ⟨hU, hG2⟩
  ·
    rw [h.Uq_inf_Dq] at hk
    rcases case2_or_case3_of_sp4 h37 h hb hVU hk with h2 | h3
    · exact MS93ConclAS.of_case2 h2
    · exact MS93ConclAS.of_case3 h3
  ·
    obtain ⟨⟨α, hsurj, hnat⟩, hcard, hTQ, hcomm, hX, hSyl⟩ := hii
    have hUDM := h.Uq_inf_Dq_eq_of_card hcard
    refine MS93ConclAS.of_case8 ?_
    unfold MS93Case8
    rw [hVU, ← hUDM]
    refine ⟨⟨α, hsurj, hnat⟩, hcard, hTQ, hcomm, h.Uq_inf_Dq, rfl, hX, fun S hS => ?_⟩
    rw [hSyl S hS, hUDM]

theorem exists_minimal_reduction (hred : PUReduce) (h : PUHyp M T L) :
    ∃ M₁ T₁ : Subgroup G, PUHyp M₁ T₁ L ∧ T₁ ≤ T ∧ PUMin M₁ T₁ L ∧ Vq M₁ L = Vq M L := by
  have key : ∀ (n : ℕ) (M T : Subgroup G), Nat.card T = n → PUHyp M T L →
      ∃ M₁ T₁ : Subgroup G, PUHyp M₁ T₁ L ∧ T₁ ≤ T ∧ PUMin M₁ T₁ L ∧ Vq M₁ L = Vq M L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro M T hn h
      by_cases hmin : PUMin M T L
      · exact ⟨M, T, h, le_rfl, hmin, rfl⟩
      · unfold PUMin at hmin
        push Not at hmin
        obtain ⟨T₁, hT₁T, hchar, hcond, hne⟩ := hmin
        obtain ⟨h₁, hV⟩ := hred G M T L T₁ h hT₁T hchar hcond (h.ne_bot_of_inf_le hcond)
        have hlt : Nat.card T₁ < n := hn ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hT₁T hne)
        obtain ⟨M₂, T₂, h₂, hT₂, hmin₂, hV₂⟩ := ih _ hlt (L ⊔ T₁) T₁ rfl h₁
        exact ⟨M₂, T₂, h₂, hT₂.trans hT₁T, hmin₂, hV₂.trans hV⟩
  exact key _ M T rfl h

end CFSG.Quasithin.MS93
