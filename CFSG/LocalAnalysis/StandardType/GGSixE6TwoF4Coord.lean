module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.StandardType.GGHalf Matrix

section Coord

private noncomputable def f4E0 : Fin 2 → F2 := Pi.single 0 1

private noncomputable def f4CoordHom : F4 →+ (Fin 2 → F2) where
  toFun y := f4Eps y *ᵥ f4E0
  map_zero' := by simp
  map_add' a b := by rw [map_add, Matrix.add_mulVec]

private theorem f4CoordHom_eq_zero {y : F4} (h : f4CoordHom y = 0) : y = 0 := by
  by_contra hy
  have h1 : f4Eps y⁻¹ *ᵥ f4CoordHom y = 0 := by rw [h, Matrix.mulVec_zero]
  have he : f4E0 = 0 := by
    calc f4E0 = (1 : Matrix (Fin 2) (Fin 2) F2) *ᵥ f4E0 := by rw [Matrix.one_mulVec]
      _ = (f4Eps y⁻¹ * f4Eps y) *ᵥ f4E0 := by
        rw [← map_mul, inv_mul_cancel₀ hy, map_one]
      _ = f4Eps y⁻¹ *ᵥ (f4Eps y *ᵥ f4E0) :=
        (Matrix.mulVec_mulVec f4E0 (f4Eps y⁻¹) (f4Eps y)).symm
      _ = f4Eps y⁻¹ *ᵥ f4CoordHom y := rfl
      _ = 0 := h1
  have h0 : f4E0 0 = 0 := by rw [he]; rfl
  have h1' : f4E0 0 = 1 := by simp [f4E0]
  rw [h1'] at h0
  exact one_ne_zero h0

private theorem f4CoordHom_injective : Function.Injective f4CoordHom := by
  intro y z h
  have hsub : f4CoordHom (y - z) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (f4CoordHom_eq_zero hsub)

private theorem f4CoordHom_bijective : Function.Bijective f4CoordHom := by
  have hF4 : Nat.card F4 = 4 := by
    have h := GaloisField.card 2 2 (by norm_num)
    simpa using h
  have hF2 : Nat.card F2 = 2 := by
    have h := GaloisField.card 2 1 (by norm_num)
    simpa using h
  have hfun : Nat.card (Fin 2 → F2) = 4 := by
    rw [Nat.card_fun, hF2, Nat.card_fin]
    norm_num
  exact (Nat.bijective_iff_injective_and_card f4CoordHom).mpr
    ⟨f4CoordHom_injective, by rw [hF4, hfun]⟩

private noncomputable abbrev f4CoordEquiv : F4 ≃+ (Fin 2 → F2) :=
  AddEquiv.ofBijective f4CoordHom f4CoordHom_bijective

private theorem f4CoordEquiv_apply (y : F4) : f4CoordEquiv y = f4CoordHom y := rfl

theorem exists_f4_coord :
    ∃ κ : F4 ≃+ (Fin 2 → F2), ∀ (a y : F4), f4Eps a *ᵥ κ y = κ (a * y) := by
  refine ⟨f4CoordEquiv, ?_⟩
  intro a y
  rw [f4CoordEquiv_apply, f4CoordEquiv_apply]
  change f4Eps a *ᵥ (f4Eps y *ᵥ f4E0) = f4Eps (a * y) *ᵥ f4E0
  rw [Matrix.mulVec_mulVec, ← map_mul]

private noncomputable def blockCoordHom (κ : F4 ≃+ (Fin 2 → F2)) :
    (Fin 3 → F4) →+ (Fin 6 → F2) where
  toFun x r := κ (x ((finProdFinEquiv (m := 3) (n := 2)).symm r).1)
                  ((finProdFinEquiv (m := 3) (n := 2)).symm r).2
  map_zero' := by
    ext r
    simp only [Pi.zero_apply, map_zero]
  map_add' x y := by
    ext r
    simp only [Pi.add_apply, map_add]

private theorem blockCoordHom_apply (κ : F4 ≃+ (Fin 2 → F2)) (x : Fin 3 → F4) (i : Fin 3)
    (j : Fin 2) : blockCoordHom κ x (finProdFinEquiv (i, j)) = κ (x i) j := by
  simp [blockCoordHom]

private theorem blockCoordHom_injective (κ : F4 ≃+ (Fin 2 → F2)) :
    Function.Injective (blockCoordHom κ) := by
  intro x y h
  funext i
  apply κ.injective
  funext j
  have h' := congrFun h (finProdFinEquiv (i, j))
  rw [blockCoordHom_apply, blockCoordHom_apply] at h'
  exact h'

private theorem blockCoordHom_bijective (κ : F4 ≃+ (Fin 2 → F2)) :
    Function.Bijective (blockCoordHom κ) := by
  have hF4 : Nat.card F4 = 4 := by
    have h := GaloisField.card 2 2 (by norm_num)
    simpa using h
  have hF2 : Nat.card F2 = 2 := by
    have h := GaloisField.card 2 1 (by norm_num)
    simpa using h
  have h3 : Nat.card (Fin 3 → F4) = 64 := by
    rw [Nat.card_fun, hF4, Nat.card_fin]
    norm_num
  have h6 : Nat.card (Fin 6 → F2) = 64 := by
    rw [Nat.card_fun, hF2, Nat.card_fin]
    norm_num
  exact (Nat.bijective_iff_injective_and_card (blockCoordHom κ)).mpr
    ⟨blockCoordHom_injective κ, by rw [h3, h6]⟩

private noncomputable abbrev blockCoordEquiv (κ : F4 ≃+ (Fin 2 → F2)) :
    (Fin 3 → F4) ≃+ (Fin 6 → F2) :=
  AddEquiv.ofBijective (blockCoordHom κ) (blockCoordHom_bijective κ)

private theorem blockCoordEquiv_apply (κ : F4 ≃+ (Fin 2 → F2)) (x : Fin 3 → F4) :
    blockCoordEquiv κ x = blockCoordHom κ x := rfl

private theorem resMat_mulVec_entry (A : Matrix (Fin 3) (Fin 3) F4) (v : Fin 6 → F2)
    (i : Fin 3) (j : Fin 2) :
    (resMat 3 A *ᵥ v) (finProdFinEquiv (i, j)) =
      ∑ i', ∑ j', f4Eps (A i i') j j' * v (finProdFinEquiv (i', j')) := by
  rw [Matrix.mulVec_apply_eq_sum]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := 3) (n := 2))
    (fun r => resMat 3 A (finProdFinEquiv (i, j)) r * v r)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
  rw [resMat_apply]

private theorem blockCoordHom_apply_mulVec (κ : F4 ≃+ (Fin 2 → F2))
    (hκ : ∀ a y : F4, f4Eps a *ᵥ κ y = κ (a * y))
    (A : Matrix (Fin 3) (Fin 3) F4) (x : Fin 3 → F4) (i : Fin 3) (j : Fin 2) :
    blockCoordHom κ (A *ᵥ x) (finProdFinEquiv (i, j)) =
      ∑ i', ∑ j', f4Eps (A i i') j j' * κ (x i') j' := by
  rw [blockCoordHom_apply, Matrix.mulVec_apply_eq_sum, map_sum, Fintype.sum_apply]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [← hκ (A i i') (x i'), Matrix.mulVec_apply_eq_sum]

theorem exists_block_coord :
    ∃ E' : (Fin 3 → F4) ≃+ (Fin 6 → F2), ∀ (A : Matrix (Fin 3) (Fin 3) F4) (x : Fin 3 → F4),
      resMat 3 A *ᵥ E' x = E' (A *ᵥ x) := by
  obtain ⟨κ, hκ⟩ := exists_f4_coord
  refine ⟨blockCoordEquiv κ, ?_⟩
  intro A x
  ext r
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  rw [blockCoordEquiv_apply κ x, blockCoordEquiv_apply κ (A *ᵥ x)]
  rw [resMat_mulVec_entry A (blockCoordHom κ x) i j,
    blockCoordHom_apply_mulVec κ hκ A x i j]
  simp only [blockCoordHom_apply]

end Coord

end CFSG.StandardType.GGSixE6Two
