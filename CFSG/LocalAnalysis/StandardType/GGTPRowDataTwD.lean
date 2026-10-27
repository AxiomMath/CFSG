module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGTPRowDataDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPRowData_twD {n : ℕ} {Y : Type} [Group Y] (hY : GGHasLabel ⟨.twD, 7, n⟩ Y) :
    GGTPRowDatum Y := by
  simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeOmegaMinus] at hY
  obtain ⟨K, hField, hFinite, hK, b, c, _, ⟨e⟩⟩ := hY
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : Fintype K := Fintype.ofFinite K
  letI : CharP K 2 := by
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rwa [Nat.card_eq_fintype_card] at hK
  refine ⟨LargeEvenMinusIdx 6, inferInstance, inferInstance, K, hField, hFinite,
    LargeEvenOmega (LargeEvenQMinus 6 b c), ⟨e⟩, ?_, ?_, ?_⟩
  · decide
  · exact ‹CharP K 2›
  · rw [TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := 6) b c]
    rw [Nat.card_of_subsingleton (1 : (⊥ : Subgroup (LargeEvenOmega (LargeEvenQMinus 6 b c))))]
    norm_num

end CFSG.StandardType

end
