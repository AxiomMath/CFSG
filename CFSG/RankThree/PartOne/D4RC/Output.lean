module

public import CFSG.RankThree.PartOne.D4RC.OrdFinal
public import CFSG.Timmesfeld.ARS.Induction
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Final CFSG.Open CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

theorem rcs_field_eq {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R) {f f' : ℕ}
    (hE : ∀ E ∈ R, Nat.card E = 2 ^ f) (hE' : ∀ E ∈ R, Nat.card E = 2 ^ f') : f' = f := by
  obtain ⟨A, hA, -⟩ := h.nondeg
  exact Nat.pow_right_injective (le_refl 2) ((hE' A hA).symm.trans (hE A hA))

theorem rcs_output_card {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    (ho : Output G R) {c f p : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpΦ : p ∣ phiOrd c (2 ^ f)) (hE : ∀ E ∈ R, Nat.card E = 2 ^ f)
    (hmM : Nat.card G ∣ ordTrialityD4 (2 ^ f)) (hRm : rOrd c f ∣ Nat.card G)
    (hpm : p ^ padicValNat p (ordTrialityD4 (2 ^ f)) ∣ Nat.card G) :
    Nat.card G = ordTrialityD4 (2 ^ f) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hpK : p ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 := rcs_prime_dvd_triality hc hq1 hpΦ
  have hSL : SimplyLacedOrder f (Nat.card G) → False :=
    fun hfam => rcs_simply_laced hc hf hp hpK hmM hRm hpm hfam
  have hNSL : NSLOrder (Nat.card G) → Nat.card G = ordTrialityD4 (2 ^ f) :=
    fun hfam => rcs_nsl hc hf hp hp5 hpΦ hmM hRm hpm hfam
  rcases ho with ⟨m, hm, A, B, hX, hgen⟩ | ⟨m, hm, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ |
    ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨hns, -⟩
  ·
    refine (hSL ?_).elim
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨f', hf', hcard, hL⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := rcs_field_eq h hE hcard
      have hc' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      exact Or.inl ⟨2, le_rfl, (card_statedClassicalModel_two hc').1 rfl⟩
    · obtain ⟨f', hf', hcard, hL⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := rcs_field_eq h hE hcard
      have hc' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      exact Or.inl ⟨m, by omega, (card_statedClassicalModel_two hc').1 rfl⟩
  ·
    refine (hSL ?_).elim
    obtain ⟨f', hf', hcard, hL⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := rcs_field_eq h hE hcard
    have hc' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
    exact Or.inr (Or.inl ⟨m, hm, (card_statedClassicalModel_two hc').2.2.2.1 rfl⟩)
  ·
    refine (hSL ?_).elim
    obtain ⟨f', hf', hcard, hL⟩ := hX.lieModel_E6 hR hiso hZ hgen
    obtain rfl := rcs_field_eq h hE hcard
    have hc' := chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact Or.inr (Or.inr (Or.inl (ExceptionalOrders.card_of_untwistedChevalleyModel_E6 hc'.2)))
  ·
    refine (hSL ?_).elim
    obtain ⟨f', hf', hcard, hL⟩ := hX.lieModel_E7 hR hiso hZ hgen
    obtain rfl := rcs_field_eq h hE hcard
    have hc' := chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (ExceptionalOrders.card_of_untwistedChevalleyModel_E7 hc'.2))))
  ·
    refine (hSL ?_).elim
    obtain ⟨f', hf', hcard, hL⟩ := hX.lieModel_E8 hR hiso hZ hgen
    obtain rfl := rcs_field_eq h hE hcard
    have hc' := chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (ExceptionalOrders.card_of_untwistedChevalleyModel_E8 hc'.2))))
  ·
    refine hNSL ?_
    rcases hns with ⟨n, g, hn, hg, hL⟩ | ⟨n, g, hn, hg, hL⟩ | ⟨g, hg, hL⟩ |
      ⟨g, hg, t, ht, hL⟩ | hL
    · have hc' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      exact Or.inl ⟨n, g, hn, hg, (card_statedClassicalModel_two hc').2.2.1 rfl⟩
    · have hc' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      exact Or.inr (Or.inl ⟨n, g, hn, hg, (card_statedClassicalModel_two hc').2.2.2.2 rfl⟩)
    · have hc' := chevalleyExceptionalModel_of_lieModel (by decide) hL
      exact Or.inr (Or.inr (Or.inl
        ⟨g, hg, ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hc'.2⟩))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      have hct : t ∈ chevalleyExceptionalTags := by
        rcases ht with rfl | rfl | rfl <;> decide
      have hc' := chevalleyExceptionalModel_of_lieModel hct hL
      rcases ht with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨g, hg, Or.inl (card_chevalleyExceptionalModel_two hc')⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨g, hg, Or.inr (Or.inl (ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hc'.2))⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨g, hg, Or.inr (Or.inr (card_chevalleyExceptionalModel_two hc'))⟩)))
    · have hc' := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
      have hcard := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two
        (by norm_num) hc').2.1 rfl
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [hcard]
      decide

end CFSG.RankThree.PartOne.D4RC
