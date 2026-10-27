module

public import CFSG.LocalAnalysis.StandardType.GGTPRowDataDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPRowData_C {n : ℕ} {Y : Type} [Group Y] (hY : GGHasLabel ⟨.C, 6, n⟩ Y) :
    GGTPRowDatum Y := by
  simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hY
  obtain ⟨K, hField, hFinite, hKcard, hYiso⟩ := hY
  letI := hField
  letI := hFinite
  have hchar : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hZ : (LargeEvenScalars (Fin 6 ⊕ Fin 6) K).subgroupOf (LargeEvenSpGroup K 6) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := 6) (K := K)
  refine ⟨Fin 6 ⊕ Fin 6, inferInstance, inferInstance, K, hField, hFinite,
    LargeEvenSpGroup K 6, ?_, ?_, hchar, ?_⟩
  · simpa using hYiso
  · simp [Fintype.card_sum]
  · rw [hZ, Subgroup.card_bot]
    norm_num

end CFSG.StandardType

end
