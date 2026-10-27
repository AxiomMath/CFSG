module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open Matrix

theorem transvection_mem_statedSL {K : Type} [Field K] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (c : K) : ∃ g : GL (Fin m) K, g ∈ StatedSL m K ∧
      (g : Matrix (Fin m) (Fin m) K) = Matrix.transvection i j c := by
  have hdet : (Matrix.transvection i j c).det = 1 := Matrix.det_transvection_of_ne i j hij c
  have hu : IsUnit (Matrix.transvection i j c).det := by rw [hdet]; exact isUnit_one
  refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j c) hu, ?_, rfl⟩
  exact Subgroup.subset_closure hdet

theorem biadd_eq_zero_of_SL {K : Type} [Field K] {A : Type*} [AddCommGroup A] {m : ℕ}
    (hm : 3 ≤ m) (β : (Fin m → K) →+ (Fin m → K) →+ A)
    (hinv : ∀ g : GL (Fin m) K, g ∈ StatedSL m K → ∀ x y : Fin m → K,
      β ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) ((g : Matrix (Fin m) (Fin m) K) *ᵥ y) = β x y)
    (x y : Fin m → K) : β x y = 0 := by
  classical
  have hact : ∀ (i j : Fin m) (c : K), i ≠ j → ∃ g : GL (Fin m) K, g ∈ StatedSL m K ∧
      ∀ x : Fin m → K,
        (g : Matrix (Fin m) (Fin m) K) *ᵥ x = x + (c * x j) • Pi.single i (1 : K) := by
    intro i j c hij
    obtain ⟨g, hg, hgA⟩ := transvection_mem_statedSL (K := K) hij c
    refine ⟨g, hg, fun x => ?_⟩
    rw [hgA, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  have hA : ∀ (i j : Fin m) (a : K), i ≠ j → ∀ y : Fin m → K, y j = 0 →
      β (a • Pi.single i (1 : K)) y = 0 := by
    intro i j a hij y hy
    obtain ⟨g, hg, hgx⟩ := hact i j a hij
    have h := hinv g hg (Pi.single j (1 : K)) y
    rw [hgx, hgx, hy] at h
    simp only [Pi.single_eq_same, mul_one, mul_zero, zero_smul, add_zero, map_add,
      AddMonoidHom.add_apply] at h
    have h2 : β (Pi.single j (1 : K)) y + β (a • Pi.single i (1 : K)) y =
        β (Pi.single j (1 : K)) y + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h2
  have hB : ∀ (i k : Fin m) (a b : K),
      β (a • Pi.single i (1 : K)) (b • Pi.single k (1 : K)) = 0 := by
    intro i k a b
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin m, j ≠ i ∧ j ≠ k := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, k} := by
        intro j _
        by_cases hji : j = i
        · simp [hji]
        · simp [hcon j hji]
      have := Finset.card_le_card hsub
      have h2 : ({i, k} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine hA i j a (Ne.symm hji) _ ?_
    simp [Pi.single_apply, hjk]
  have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ k, y k • Pi.single k (1 : K) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx, hy]
  simp [map_sum, AddMonoidHom.finset_sum_apply, hB]

end CFSG.RankThree.GF2n.Stroth80
