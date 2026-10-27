module

public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoRank
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_irredTableB_D4_two
    {lab : LargeEvenLabel} (h : GGD4Three 3 lab) (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredTableB 3 R I := by
  have horth : GGOrthNsLabel 3 lab := by
    refine ⟨Or.inl h.1, ?_, ?_⟩
    · rw [h.2.1]
    · rw [hn]
      norm_num
  have hirr : LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB 3 R I :=
    (largeEvenLabelAll_torusIrredSC_orthNs Nat.prime_three horth).mono
      fun R _ I _ hI => ggIrredModTableB_of_torusIrredSC Nat.prime_three hI
  have hcard : LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M)
        (θ : L' ⧸ Subgroup.center L' ≃* R)
        (hE : E ≤ Subgroup.normalizer (L' : Set M)),
        GGTableBPosition 3 L' E I θ hE →
        Nat.card E = 3 ^ 4 *
          Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨htag, hrk, _⟩ := h
    dsimp only at htag hrk
    subst htag
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · subst hrk
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      haveI : CharP K 2 := charP_two_of_card hK
      have hn1 : n = 1 := by simpa using hn
      have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
      refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
      intro M _ _ L' E θ hE hP
      exact card_eq_pow_four_of_omegaPlus_two hK2 hP
  refine (largeEvenLabelAll_and hcard hirr).mono ?_
  intro R _ I F hpair M _ _ L' E θ hE hP
  exact ⟨hpair.1 M L' E θ hE hP, hpair.2 M L' E θ hE hP⟩

end CFSG.StandardType
