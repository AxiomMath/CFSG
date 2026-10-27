module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGResE6DepSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_card_lt_uniMinusSmall {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hS : ggTBJUniMinusSmallLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ⟨⟨ht, hl⟩ | ⟨ht, hl⟩, hpq⟩
  · dsimp only at ht hl hpq
    subst ht
    rintro Q ⟨K, hField, hFinite, hK, hq⟩
    let : Field K := hField
    let : Finite K := hFinite
    refine ⟨K, hField, hFinite, hK, hq, fun E hEI hE => ?_⟩
    have hd3 : 3 ≤ l + 1 := by omega
    have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
      intro h
      exact absurd (congrArg Prod.fst h) (by omega)
    have hd : (l + 1) / 2 < 3 := by omega
    exact (TwDThree.card_le_of_subset_unitaryConj (d := l + 1)
      ⟨Nat.prime_two, hlab.1, by rw [hK, ← pow_mul, mul_comm]⟩ hd3 hdq hp hpq hE hEI).trans_lt
      (Nat.pow_lt_pow_right hp.one_lt hd)
  · exact largeEvenLabelAll_card_lt_twDThree hp hlab ⟨ht, hl, hpq⟩

theorem ggTBJLeftOn_uniMinusSmall : GGTBJLeftOn ggTBJUniMinusSmallLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _
  exact (hH.not_innerDiagOnLabel_of_card_lt (X := L) (Or.inl rfl)
    (fun lab hΛ hS => largeEvenLabelAll_card_lt_uniMinusSmall hp.out hΛ hS) hL).elim

theorem ggTBJNbrOn_uniMinusSmall : GGTBJNbrOn ggTBJUniMinusSmallLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK _
  exact (hH.not_innerDiagOnLabel_of_card_lt (X := K) (Or.inr rfl)
    (fun lab hΛ hS => largeEvenLabelAll_card_lt_uniMinusSmall hp.out hΛ hS) hK).elim

end CFSG.StandardType

end
