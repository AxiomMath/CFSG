module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UFF2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem false_of_concl701FF_of_leaves (h325 : H13.Stmt3_2_5) (h328 : H13.Stmt3_2_8)
    {T Kp Ip : Subgroup G} (hfsu : H13.FSU G T Kp Ip)
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hVN : Kp ⊔ T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G))
    [IsMulCommutative ↥(H13.fsuV T Ip)]
    (hcard : ∀ {X : Type} [Group X] [Finite X] (f : ↥Kp →* X), Function.Surjective f →
      1 < Nat.card X → Nat.card X ≤ 20160 → False)
    (hSL : ∀ {K : Type} [Field K] [Finite K] {m n : ℕ}, 2 ≤ m → 1 ≤ n → (3 ≤ m ∨ 2 ≤ n) →
      Nat.card K = 2 ^ n → ∀ f : ↥Kp →* Matrix.SpecialLinearGroup (Fin m) K,
        Function.Surjective f → False)
    (hSp : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n →
      ∀ f : ↥Kp →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K), Function.Surjective f → False)
    (hG2 : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n →
      ∀ f : ↥Kp →* ↥⁅quasithinG2 K, quasithinG2 K⁆, Function.Surjective f → False)
    (hFF : H13.Concl701FF T Kp Ip) : False := by
  have hKpN : Kp ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G) := le_sup_left.trans hVN
  have hTN : T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G) := le_sup_right.trans hVN
  obtain ⟨f₀, hf₀⟩ := exists_autOn_surjective hKpN
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have hpos : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK Finite.one_lt_card.ne'
    · exact h0
  have hZ2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hAltLeaf : ∀ {X : Type} [Group X] [Finite X] (g : ↥Kp →* X), Function.Surjective g →
      ∀ {m : ℕ}, 5 ≤ m → m ≤ 8 → (X ≃* alternatingGroup (Fin m)) → False := by
    intro X _ _ g hg m hm5 hm8 e
    have hc : Nat.card X = m.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, card_alt (by omega)]
    refine hcard g hg ?_ ?_ <;> rw [hc]
    · interval_cases m <;> decide
    · interval_cases m <;> decide
  have hSL' : ∀ {K : Type} [Field K] [Finite K] {m n : ℕ}, 2 ≤ m → (3 ≤ m ∨ 2 ≤ n) →
      Nat.card K = 2 ^ n →
      Nonempty (↥(autOn Kp (H13.fsuV T Ip)) ≃* Matrix.SpecialLinearGroup (Fin m) K) → False :=
    fun hm hmn hK ⟨e⟩ => hSL hm (hpos hK) hmn hK (e.toMonoidHom.comp f₀) (e.surjective.comp hf₀)
  have hAlt : ∀ {m : ℕ}, 5 ≤ m → m ≤ 8 →
      Nonempty (↥(autOn Kp (H13.fsuV T Ip)) ≃* alternatingGroup (Fin m)) → False :=
    fun hm5 hm8 ⟨e⟩ => hAltLeaf f₀ hf₀ hm5 hm8 e
  have hSp' : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n →
      Nonempty (↥(autOn Kp (H13.fsuV T Ip)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K)) →
        False :=
    fun hK ⟨e⟩ => hSp hK (e.toMonoidHom.comp f₀) (e.surjective.comp hf₀)
  rcases SecS.concl701FF_list h325 h328 hfsu hTK hFF with hl | ⟨-, ht⟩
  · rcases hl with ⟨n, K, _, _, hK, he⟩ | ⟨n, K, _, _, hK, he⟩ | he | he | he | he
    · exact hSL' (by norm_num) (Or.inl le_rfl) hK he
    · exact hSp' hK he
    · exact hAlt (by norm_num) (by norm_num) he
    · exact hSL' (by norm_num) (Or.inl (by norm_num)) hZ2 he
    · exact hSL' (by norm_num) (Or.inl (by norm_num)) hZ2 he
    · exact hAlt (by norm_num) (by norm_num) he
  · rcases ht with ⟨n, hL⟩ | ⟨n, K, _, _, hK, he⟩ | he | ⟨n, K, _, _, hK, he⟩ |
        ⟨n, K, _, _, hK, he⟩ | he | he | he | he | ⟨-, -, he⟩ | ⟨n, hn, he⟩ | he
    ·
      rcases hL with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · have hcard' := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl
        obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
        have : CharP K 2 := KGNat.charP_two_of_card (by have := hpos hK; omega) hK
        have ε : ↥(autOn Kp (H13.fsuV T Ip)) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
          (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
            K).symm).trans ((QuotientGroup.quotientMulEquivOfEq KGNat.center_SL2_eq_bot).trans
              QuotientGroup.quotientBot)
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · obtain rfl : n = 1 := by have := hpos hK; omega
          refine hcard (ε.toMonoidHom.comp f₀) (ε.surjective.comp hf₀) ?_ ?_ <;>
            rw [← Nat.card_congr ε.toEquiv, hcard'] <;> decide
        · exact hSL' le_rfl (Or.inr hn2) hK ⟨ε⟩
      all_goals exact absurd h (by norm_num)
    · exact hSL' (by norm_num) (Or.inl le_rfl) hK he
    · exact hSL' (by norm_num) (Or.inl le_rfl) hZ2 he
    · exact hSp' hK he
    · obtain ⟨e⟩ := he
      exact hG2 hK (e.toMonoidHom.comp f₀) (e.surjective.comp hf₀)
    · exact hAlt (by norm_num) (by norm_num) he
    · exact hAlt (by norm_num) (by norm_num) he
    · exact hAlt (by norm_num) (by norm_num) he
    ·
      obtain ⟨e⟩ := he
      have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      exact false_of_autOn_sup_simple hKpN hTN hTK hT2
        (not_isPGroup_two_of_three_dvd (by rw [card_alt (n := 7) (by norm_num)]; decide)) e
        fun g hg => hAltLeaf g hg (by norm_num) (by norm_num) (MulEquiv.refl _)
    ·
      obtain ⟨e⟩ := he
      exact hAltLeaf ((e.toMonoidHom.comp (QuotientGroup.mk' _)).comp f₀)
        ((e.surjective.comp (QuotientGroup.mk'_surjective _)).comp hf₀) (m := 6) (by norm_num)
        (by norm_num) (MulEquiv.refl _)
    ·
      obtain ⟨e⟩ := he
      have hn3 : 3 ≤ n := by omega
      have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
        SecA.isSimpleGroup_SL_zmod_two hn3
      exact false_of_autOn_sup_simple hKpN hTN hTK hT2
        (not_isPGroup_two_of_three_dvd (three_dvd_card_SL_zmod_two hn)) e
        fun g hg => hSL (by omega) le_rfl (Or.inl hn3) hZ2 g hg
    · exact hSL' (by norm_num) (Or.inl (by norm_num)) hZ2 he

end CFSG.Quasithin.Vol2.Ch11.SecB
