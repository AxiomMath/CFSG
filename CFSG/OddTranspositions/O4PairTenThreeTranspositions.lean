module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.OddTranspositions.O4PairTenAbstract

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

theorem orderOf_y (i : Fin 10) : orderOf (y i) = 2 := by
  have hconj := (mem_class65_iff (y i)).mp (y_mem_class65 i)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hsem : c * SemidirectProduct.inr (φ := psl2FieldAut K25) frob25 = y i * c := by
    rw [← hc]; group
  have hord : orderOf (y i) = orderOf (SemidirectProduct.inr (φ := psl2FieldAut K25) frob25) :=
    (SemiconjBy.orderOf_eq (G := PSigmaL225) c hsem).symm
  have hord2 : orderOf (SemidirectProduct.inr (φ := psl2FieldAut K25) frob25) = 2 := by
    rw [orderOf_injective (SemidirectProduct.inr (φ := psl2FieldAut K25)) SemidirectProduct.inr_injective frob25]
    exact orderOf_eq_prime (by rw [pow_two, frob25_mul_self]) frob25_ne_one
  rw [hord, hord2]

theorem y_mul_self (i : Fin 10) : y i * y i = 1 := by
  have h := pow_orderOf_eq_one (y i)
  rw [orderOf_y i] at h
  simpa [pow_two] using h

theorem y_mul_eq (i j : Fin 10) :
    y i * y j = SemidirectProduct.inl (φ := psl2FieldAut K25) (pslEquiv (x i * x j)) := by
  have hmul : SemidirectProduct.mk (x i) frob25t * SemidirectProduct.mk (x j) frob25t =
      SemidirectProduct.inl (φ := psl2FieldAut F25t) (x i * x j) := by
    rw [SemidirectProduct.mul_def]
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.left_inl]
      exact congrArg (fun z => x i * z) (x_fixed j)
    · simp [frob25t_mul_self]
  rw [y, y, ← map_mul, hmul, psigmaL2Equiv_inl]

theorem y_products_order (i j : Fin 10) :
    orderOf (y i * y j) ∈ ({1, 2, 3} : Set ℕ) := by
  rw [y_mul_eq]
  rw [orderOf_injective (SemidirectProduct.inl (φ := psl2FieldAut K25)) SemidirectProduct.inl_injective,
    (pslEquiv).orderOf_eq]
  exact ten_products_order i j

end CFSG.OddTranspositions.QZ
