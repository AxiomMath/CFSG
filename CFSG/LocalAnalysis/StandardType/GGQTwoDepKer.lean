module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGIntCartanLeafKer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lr7dk_E6_cartan_pair {a b : Fin 6} (hab : a ≠ b) :
    (CartanMatrix.E 6 a b = 0 ∧ CartanMatrix.E 6 b a = 0 ∧ CoxeterMatrix.E₆ a b = 2) ∨
      (CartanMatrix.E 6 a b = -1 ∧ CartanMatrix.E 6 b a = -1 ∧ CoxeterMatrix.E₆ a b = 3) := by
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | decide

private theorem lr7dk_E6_symm (i j : Fin 6) :
    CartanMatrix.E 6 i j = CartanMatrix.E 6 j i :=
  congrFun (congrFun (CartanMatrix.E_transpose 6) j) i

private theorem lr7dk_coxeter_of_cartan {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hC : GGIntCartan M C)
    (e : Fin 6 ≃ ι) (hCE : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) :
    M = CoxeterMatrix.E₆.reindex e := by
  apply CoxeterMatrix.ext
  funext x y
  obtain ⟨i, rfl⟩ := e.surjective x
  obtain ⟨j, rfl⟩ := e.surjective y
  rw [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal (e i)]
    fin_cases i <;> decide
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rcases lr7dk_E6_cartan_pair hij with ⟨h0, h0', hE6⟩ | ⟨h1, h1', hE6⟩
    · rcases hC.2 (e i) (e j) hne with
        ⟨hm, h2, -⟩ | ⟨hm, h2, -⟩ | ⟨hm, h2, h3, h4⟩ | ⟨hm, h2, h3, h4⟩
      · exact hm.trans hE6.symm
      · rw [hCE i j, h0] at h2; norm_num at h2
      · rw [hCE i j, h0, zero_mul] at h2; norm_num at h2
      · rw [hCE i j, h0, zero_mul] at h2; norm_num at h2
    · rcases hC.2 (e i) (e j) hne with
        ⟨hm, h2, -⟩ | ⟨hm, h2, -⟩ | ⟨hm, h2, h3, h4⟩ | ⟨hm, h2, h3, h4⟩
      · rw [hCE i j, h1] at h2; norm_num at h2
      · exact hm.trans hE6.symm
      · rw [hCE i j, h1, hCE j i, h1'] at h2; norm_num at h2
      · rw [hCE i j, h1, hCE j i, h1'] at h2; norm_num at h2

private theorem lr7dk_intCartan_transpose {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) :
    GGIntCartan M C.transpose := by
  refine ⟨fun i => by simpa using hC.1 i, fun i j hij => ?_⟩
  simp only [Matrix.transpose_apply]
  rcases hC.2 i j hij with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, h3, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))

private theorem lr7dk_leaf_transpose {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) {a : ι}
    (ha : ∃! c, c ≠ a ∧ C a c ≠ 0) :
    ∃! c, c ≠ a ∧ C.transpose a c ≠ 0 := by
  obtain ⟨c, hc, huniq⟩ := ha
  refine ⟨c, ⟨hc.1, ?_⟩, fun d hd => huniq d ⟨hd.1, ?_⟩⟩
  · rw [Matrix.transpose_apply]
    exact fun h0 => hc.2 (hC.eq_zero_symm hc.1.symm h0)
  · exact fun h0 => hd.2 (by rw [Matrix.transpose_apply]; exact hC.eq_zero_symm hd.1 h0)

theorem ggQ2_dep_ker_right (D : GGQ2Lin 3) (κ : D.ι → ZMod 3)
    (hκ : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * κ j = 0) (hκa : κ D.a = 0) (hκ0 : κ ≠ 0) :
    ∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e ∧
      (∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) ∧ e 1 = D.a := by
  obtain ⟨-, e, he, hea⟩ := ggIntCartan_leaf_ker D.isWeyl D.isCartan D.a_leaf (p := 3)
    (by norm_num) hκ hκa hκ0
  exact ⟨e, lr7dk_coxeter_of_cartan D.isCartan e he, he, hea⟩

theorem ggQ2_dep_ker_left (D : GGQ2Lin 3) (κ : D.ι → ZMod 3)
    (hκ : ∀ j, ∑ i, κ i * (D.cartan i j : ZMod 3) = 0) (hκa : κ D.a = 0) (hκ0 : κ ≠ 0) :
    ∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e ∧
      (∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) ∧ e 1 = D.a := by
  have hκT : ∀ i, ∑ j, (D.cartan.transpose i j : ZMod 3) * κ j = 0 := by
    intro i
    rw [← hκ i]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.transpose_apply, mul_comm]
  obtain ⟨-, e, heT, hea⟩ := ggIntCartan_leaf_ker D.isWeyl
    (lr7dk_intCartan_transpose D.isCartan) (lr7dk_leaf_transpose D.isCartan D.a_leaf)
    (p := 3) (by norm_num) hκT hκa hκ0
  have he : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j := by
    intro i j
    have h := heT j i
    rw [Matrix.transpose_apply] at h
    exact h.trans (lr7dk_E6_symm j i)
  exact ⟨e, lr7dk_coxeter_of_cartan D.isCartan e he, he, hea⟩

theorem GGQ2Lin.coxeter_eq_E6_of_cartan {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : Fin 6 ≃ D.ι)
    (he : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) :
    D.coxeter = CoxeterMatrix.E₆.reindex e :=
  lr7dk_coxeter_of_cartan D.isCartan e he

end CFSG.StandardType

end
