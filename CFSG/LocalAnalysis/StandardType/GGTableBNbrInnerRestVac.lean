module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestCore
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly StdSubRestThree

@[expose] def GGTableBNbrInnerA2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ 3

theorem recipeLinear_card_lt_three {N p : ℕ} (hp : p.Prime) (hp3 : p ∣ 3) (hpN : p ∣ N - 1)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear 3 N Q) :
    LargeEvenRecipeLinear 3 N fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpN
  have hpe : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  exact card_lt_of_congr (TypeA.recipeEquiv 3 K) (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TypeA.card_lt_of_torality hp hpK (by norm_num) le_rfl
      (ggPGLToralityInput_holds p 3 K hp (by omega) hpK hp3) hX' hX'I) hXI hX

theorem largeEvenLabelAll_card_lt_A2 {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGTableBNbrInnerA2Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hp3⟩ := h
  dsimp only at ht hl hpn
  subst ht hl
  intro Q hQ
  exact recipeLinear_card_lt_three (N := 2 ^ n) hp hp3 hpn hQ

@[expose] def GGTableBNbrInnerVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLinearTwoLabel lab ∨ GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab ∨
    (GGCorFourTwoSmallLabel p lab ∧ LargeEvenSplit p lab) ∨
    (lab.tag = .twA ∧ lab.rank = 2 ∧ LargeEvenSplit p lab)

section Vac


theorem ggTableBNbrInnerInputOn_vac : GGTableBNbrInnerInputOn GGTableBNbrInnerVacLabel := by
  refine ((ggTableBNbrInnerInputOn_of_labelAll_card_lt (S := fun p lab =>
      GGLinearTwoLabel lab ∨ GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab ∨
        (GGCorFourTwoSmallLabel p lab ∧ LargeEvenSplit p lab)) ?_).or
    (ggTableBNbrInnerInputOn_of_labelsSC (S := fun p lab =>
      lab.tag = .twA ∧ lab.rank = 2 ∧ LargeEvenSplit p lab) ?_)).mono ?_
  · intro p lab hp hp2 hlab h
    rcases h with h | h | h | h
    · exact (largeEvenLabelAll_autRankLeTwo_linearTwo hp hp2 h).mono
        fun _ _ _ _ hR hs hna X _ hX =>
          (hR hs hna X hX).trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
    · exact (largeEvenLabelAll_card_lt_twoThreeSmall h).mono fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_A2 hp h).mono fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_corFourTwoSmall hp hlab h.1 h.2).mono
        fun _ _ _ _ hX _ _ => hX
  · intro p lab hp hlab h
    exact (largeEvenLabelAll_lift_card_lt_unitaryThree hp hlab h.1 h.2.1 h.2.2).mono
      fun _ _ _ _ hX => ggTorusNbrSC_of_card_lt hX
  · intro p lab h
    rcases h with h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr h

end Vac

end CFSG.StandardType

end
