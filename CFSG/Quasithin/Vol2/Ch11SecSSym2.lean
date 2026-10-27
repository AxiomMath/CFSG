module

public import CFSG.Quasithin.Vol2.Ch11SecSInsp
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

variable {G : Type} [Group G] [Finite G]

theorem a128FourList_of_shape (hG2a : FactG2AdjointOrder) {Y : Type} [Group Y] [Finite Y]
    (hs : Shape4 Y) (hn : ¬ IsPSL 3 2 2 Y) : A128FourList Y := by
  have hn1 : ∀ c m k, Odd c → Odd m → k ≠ 3 → c * Nat.card Y = 2 ^ k * m →
      ¬ IsPSL 3 2 1 Y := by
    intro c m k hc hm hk heq h
    rw [card_L32 h] at heq
    exact hk (eq_of_two_pow_mul_odd (a := k) (b := 3) hm (hc.mul (by decide : Odd 21))
      (by rw [← heq]; ring))
  have hn2 : ∀ c m k, Odd c → Odd m → k ≠ 6 → c * Nat.card Y = 2 ^ k * m →
      ¬ IsPSL 3 2 2 Y := by
    intro c m k hc hm hk heq h
    rw [card_L34 h] at heq
    exact hk (eq_of_two_pow_mul_odd (a := k) (b := 6) hm (hc.mul (by decide : Odd 315))
      (by rw [← heq]; ring))
  unfold A128FourList
  iterate 14 right
  rcases hs with hSL | hL | hSp | hG
  · obtain ⟨c, m, hc, hm, heq⟩ := card_of_shape_SL (Or.inl hSL)
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hSL
    exact ⟨Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, K, inferInstance, inferInstance, hK,
      ⟨e.trans (specialLinearGroupEquivStatedSL 3 K)⟩⟩)⟩, hn1 c m 6 hc hm (by norm_num) heq, hn⟩
  · exfalso
    rcases hL with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hn hc
    all_goals exact absurd h (by norm_num)
  · obtain ⟨c, m, hc, hm, heq⟩ := card_of_shape_Sp hSp
    have hSp' : IsPSp4 2 2 Y := by
      rcases hSp with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hc
      all_goals exact absurd h (by norm_num)
    exact ⟨Or.inl ⟨2, Or.inr (Or.inr (Or.inl ⟨le_rfl, hSp'⟩))⟩,
      hn1 c m 8 hc hm (by norm_num) heq, hn2 c m 8 hc hm (by norm_num) heq⟩
  · obtain ⟨m, hm, heq⟩ := card_of_shape_G2 hG2a hG
    have heq' : 1 * Nat.card Y = 2 ^ 12 * m := by rw [one_mul, heq]
    have hG' : IsG2 2 2 Y := by
      rcases hG with ⟨h, -⟩ | ⟨-, -, hc⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact hc
      all_goals exact absurd h (by decide)
    exact ⟨Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, hG'⟩)))⟩,
      hn1 1 m 12 odd_one hm (by norm_num) heq', hn2 1 m 12 odd_one hm (by norm_num) heq'⟩

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem inspData_k0Of (hLevi : FactL34Levi) (hT : FactPGL34Torus) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) {I₀ : Subgroup G}
    (hTI₀ : T ≤ Subgroup.normalizer (I₀ : Set G)) (hK₀I₀ : k0Of K P₂ ≤ I₀)
    (hL₂I₀ : LOf L V₂ ≤ I₀) (hXI₀ : X ≤ I₀) :
    InspData (modO2Image I₀ (T ⊓ I₀)) (modO2Image I₀ (k0Of K P₂)) (modO2Image I₀ (LOf L V₂))
      (modO2Image I₀ X) := by
  have hK₀SL : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(k0Of K P₂) ⧸ CFSG.pCore 2 ↥(k0Of K P₂) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF4, ⟨e⟩⟩ :=
      hLevi _ h.psl _ h.isSylowTwoOf_bar P₂ hP.c₂.1 hP.ne_top₂ hP.c₂.2.1 hP.n₂
    obtain ⟨e₂⟩ := modO2Image_quotEquiv (k0Of_le K P₂)
    rw [modO2Image_k0Of K hP.c₂.2.1] at e₂
    exact ⟨F, inferInstance, inferInstance, hF4, ⟨e₂.trans e⟩⟩
  have hXK₀b : X ⊓ k0Of K P₂ ≠ ⊥ := by
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_three cL.card₁
    intro hb
    have : x ∈ X ⊓ k0Of K P₂ := ⟨hx.1, h.cartan_inf_L₁_le_k0Of hP hx⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hx1 this
  exact h.inspData hN h1102 cL (k0Of_perfect K P₂) hP.k0Of_ne_bot (h.T_le_normalizer_k0Of hP)
    (h.cartan_le_normalizer_k0Of hN h1102 hP) (h.k0Of_not_le hP) hK₀SL hXK₀b
    (h.xOne_k0Of_ne_bot hT hN h1102 cL hP) hTI₀ hK₀I₀ hL₂I₀ hXI₀

theorem not_isPSL_of_le (hNo : FactL34NoE9) (hLevi : FactL34Levi) (hT : FactPGL34Torus)
    (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) {I₀ : Subgroup G}
    (hTI₀ : T ≤ Subgroup.normalizer (I₀ : Set G)) (hK₀I₀ : k0Of K P₂ ≤ I₀)
    (hL₂I₀ : LOf L V₂ ≤ I₀) (hXI₀ : X ≤ I₀) : ¬ IsPSL 3 2 2 (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) :=
  (h.inspData_k0Of hLevi hT hN h1102 cL hP hTI₀ hK₀I₀ hL₂I₀ hXI₀).false_of_isPSL hNo

theorem isMaximalLocal_of_shape (h128 : Lemma128Four) (hG2a : FactG2AdjointOrder)
    (h : StarHyp G T L I V₁ V₂ X K) {J : Subgroup G} (hJ : quasithinIsLocal T J)
    (hs : Shape11 J 2) (hn : ¬ IsPSL 3 2 2 (↥J ⧸ CFSG.pCore 2 ↥J)) :
    quasithinIsMaximalLocal T J :=
  h128 G h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian T J hJ
    (a128FourList_of_shape hG2a hs hn)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
