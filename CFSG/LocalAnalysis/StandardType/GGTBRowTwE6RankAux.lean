module

public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTwE6Row_card_le_of_recipe
    {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp3 : p ≠ 3) (hpn : p ∣ 2 ^ n + 1) :
    ∀ X : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n →
        IsElemAbelian p X → Nat.card X ≤ p ^ 6 := by
  intro X hXI hX
  haveI := TwE6Delta.finite_recipeR (K := K) hK
  have hXInn : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
      Set.range (MulAut.conj :
        TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) := by
    intro φ hφ
    exact TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ (hXI hφ) (hX.2 φ hφ)
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn
    (R := TwE6Delta.RecipeR K n) (TwE6Delta.center_recipeR_eq_bot hn hK) hXInn hX
  have h6 := TwE6Rank.card_le_of_isElemAbelian hn hK hp
    (TableBU.ne_two_of_dvd_two_pow_add_one hn hpn) hp3 hpn hA
  rw [← hAc]
  exact h6

theorem ggTwE6Row_labelAll_card
    {lab : LargeEvenLabel} (htag : lab.tag = .twE6) (hlab : LargeEvenInLambda2 lab)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n + 1) (hp3 : p ≠ 3) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X ≤ p ^ 6) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  refine TwE6Delta.labelAll (lab := ⟨.twE6, l, n⟩) rfl ?_
  intro K _ _ hK
  intro _ _ X hXI hX
  exact ggTwE6Row_card_le_of_recipe hlab.1 hK hp hp3 hpn X hXI hX

end CFSG.StandardType

end
