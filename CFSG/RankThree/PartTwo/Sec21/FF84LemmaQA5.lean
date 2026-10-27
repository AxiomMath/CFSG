module

public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

private theorem alt5_real_of_order_three :
    ∀ x : alternatingGroup (Fin 5), x ^ 3 = 1 → x ≠ 1 →
      ∃ u : alternatingGroup (Fin 5), u * x * u⁻¹ = x⁻¹ := by
  decide +kernel

theorem exists_conj_inv_of_card_sixty {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : Nat.card K = 60) {a : K} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ∃ t : K, t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hK
  obtain ⟨u, hu⟩ := alt5_real_of_order_three (e a) (by rw [← map_pow, ha3, map_one])
    (fun h => ha1 (e.injective (by rw [h, map_one])))
  refine ⟨e.symm u, ?_⟩
  apply e.injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hu

end CFSG.RankThree.PartTwo.Sec21.FF84
