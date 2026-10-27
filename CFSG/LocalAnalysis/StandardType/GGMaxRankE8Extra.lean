module

public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


private def l6m3_m : Fin 8 → ℤ := ![2, 4, 6, 5, 4, 3, 2, 1]

private def l6m3_mZ : Fin 8 → ZMod 3 := fun j => ((l6m3_m j : ℤ) : ZMod 3)

private def l6m3_G : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  (Tag.E8.symmetrizedCartan).map (fun z : ℤ => (z : ZMod 3))

private def l6m3_Gi : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  !![1, 2, 1, 1, 2, 0, 1, 2;
     2, 2, 1, 0, 0, 0, 0, 0;
     1, 1, 2, 2, 1, 0, 2, 1;
     1, 0, 2, 0, 0, 0, 0, 0;
     2, 0, 1, 0, 2, 0, 1, 2;
     0, 0, 0, 0, 0, 0, 2, 1;
     1, 0, 2, 0, 1, 2, 0, 0;
     2, 0, 1, 0, 2, 1, 0, 2]

private def l6m3_A : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  (CartanMatrix.A 8).map (fun z : ℤ => (z : ZMod 3))

private def l6m3_M (c : Fin 8 → Fin Tag.E8.rank → ℤ) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  fun t j => ((c j t : ℤ) : ZMod 3)

private lemma l6m3_G_isUnit : IsUnit l6m3_G :=
  ⟨⟨l6m3_G, l6m3_Gi, by decide +kernel, by decide +kernel⟩, rfl⟩

private lemma l6m3_G_entry (t s : Fin 8) :
    l6m3_G t s = ((Tag.E8.symmetrizedCartan t s : ℤ) : ZMod 3) := rfl

private lemma l6m3_iform_add_left
    (x x' y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) (x + x') y = iform (τ := .E8) x y + iform (τ := .E8) x' y :=
  iform_add_left (τ := .E8) x x' y

private lemma l6m3_iform_add_right
    (x y y' : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x (y + y') = iform (τ := .E8) x y + iform (τ := .E8) x y' :=
  iform_add_right (τ := .E8) x y y'

private lemma l6m3_iform_smul_left
    (c : ℤ) (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) (c • x) y = c * iform (τ := .E8) x y :=
  iform_smul_left (τ := .E8) c x y

private lemma l6m3_iform_smul_right
    (c : ℤ) (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x (c • y) = c * iform (τ := .E8) x y :=
  iform_smul_right (τ := .E8) c x y

private lemma l6m3_iform_comm
    (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x y = iform (τ := .E8) y x :=
  iform_comm (τ := .E8) x y

private lemma l6m3_iform_sum_left
    (a : Fin 8 → ℤ) (x : Fin 8 → Fin Tag.E8.rank → ℤ)
    (y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) (∑ p, a p • x p) y = ∑ p, a p * iform (τ := .E8) (x p) y := by
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp only [l6m3_iform_add_left, l6m3_iform_smul_left]

private lemma l6m3_iform_sum_right
    (x : Fin Tag.E8.rank → ℤ) (a : Fin 8 → ℤ)
    (y : Fin 8 → Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x (∑ i, a i • y i) = ∑ i, a i * iform (τ := .E8) x (y i) := by
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp only [l6m3_iform_add_right, l6m3_iform_smul_right]

private lemma l6m3_iform_neg_left
    (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) (-x) y = -iform (τ := .E8) x y := by
  rw [← neg_one_smul ℤ x, l6m3_iform_smul_left]
  ring

private lemma l6m3_iform_neg_right
    (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x (-y) = -iform (τ := .E8) x y := by
  rw [l6m3_iform_comm, l6m3_iform_neg_left, l6m3_iform_comm]

private lemma l6m3_iform_u
    (c : Fin 8 → Fin Tag.E8.rank → ℤ)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j) (j : Fin 8) :
    iform (τ := .E8) (∑ k, l6m3_m k • c k) (c j) = 3 * (if j = 2 then 1 else 0) := by
  rw [l6m3_iform_sum_left]
  simp only [hg]
  fin_cases j <;> decide +kernel

private lemma l6m3_iform_u_u
    (c : Fin 8 → Fin Tag.E8.rank → ℤ)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j) :
    iform (τ := .E8) (∑ k, l6m3_m k • c k) (∑ k, l6m3_m k • c k) = 18 := by
  have h : iform (τ := .E8) (∑ k, l6m3_m k • c k) (∑ k, l6m3_m k • c k)
      = ∑ p, l6m3_m p * iform (τ := .E8) (∑ k, l6m3_m k • c k) (c p) :=
    l6m3_iform_sum_right (∑ k, l6m3_m k • c k) l6m3_m c
  rw [h]
  simp only [l6m3_iform_u c hg]
  decide +kernel

private lemma l6m3_MGM_apply (c : Fin 8 → Fin Tag.E8.rank → ℤ) (i j : Fin 8) :
    (Matrix.transpose (l6m3_M c) * l6m3_G * l6m3_M c) i j
      = ((iform (τ := .E8) (c i) (c j) : ℤ) : ZMod 3) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, l6m3_M, Finset.sum_mul]
  rw [iform]
  push_cast
  simp only [l6m3_G_entry]
  conv_lhs => rw [Finset.sum_comm]
  rfl

private lemma l6m3_MGM (c : Fin 8 → Fin Tag.E8.rank → ℤ)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j) :
    Matrix.transpose (l6m3_M c) * l6m3_G * l6m3_M c = l6m3_A := by
  ext i j
  rw [l6m3_MGM_apply]
  simp only [l6m3_A, Matrix.map_apply, hg i j]

private lemma l6m3_kerA_aux :
    ∀ k0 k1 k2 k3 k4 k5 k6 k7 : ZMod 3,
      Matrix.mulVec l6m3_A (![k0, k1, k2, k3, k4, k5, k6, k7] : Fin 8 → ZMod 3) = 0 →
        (![k0, k1, k2, k3, k4, k5, k6, k7] : Fin 8 → ZMod 3) =
          (2 * k0) • l6m3_mZ := by
  decide +kernel

private lemma l6m3_kerA_all :
    ∀ k : Fin 8 → ZMod 3, Matrix.mulVec l6m3_A k = 0 → ∃ a : ZMod 3, k = a • l6m3_mZ := by
  intro k hk
  have hk' : Matrix.mulVec l6m3_A
      (fun j => ![k 0, k 1, k 2, k 3, k 4, k 5, k 6, k 7] j) = 0 := by
    rw [show (fun j => ![k 0, k 1, k 2, k 3, k 4, k 5, k 6, k 7] j) = k from by
      funext j; fin_cases j <;> rfl]
    exact hk
  have h := l6m3_kerA_aux (k 0) (k 1) (k 2) (k 3) (k 4) (k 5) (k 6) (k 7) hk'
  refine ⟨2 * k 0, ?_⟩
  rw [show k = (fun j => ![k 0, k 1, k 2, k 3, k 4, k 5, k 6, k 7] j) from by
    funext j; fin_cases j <;> rfl]
  exact h

private lemma l6m3_kernel_clause (c : Fin 8 → Fin Tag.E8.rank → ℤ)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j)
    (k : Fin 8 → ZMod 3)
    (hk : ∀ t : Fin Tag.E8.rank, ∑ j, k j * ((c j t : ℤ) : ZMod 3) = 0) :
    ∃ a : ZMod 3, k = a • l6m3_mZ := by
  have hMGM := l6m3_MGM c hg
  have hMk : Matrix.mulVec (l6m3_M c) k = 0 := by
    funext t
    change Matrix.mulVec (l6m3_M c) k t = 0
    rw [← hk t]
    simp only [l6m3_M, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAk : Matrix.mulVec l6m3_A k = 0 := by
    rw [← hMGM]
    conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hMk, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact l6m3_kerA_all k hAk

private lemma l6m3_M_ker_nontrivial (c : Fin 8 → Fin Tag.E8.rank → ℤ)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j) :
    ∃ v : Fin 8 → ZMod 3, v ≠ 0 ∧ Matrix.mulVec (l6m3_M c) v = 0 := by
  by_contra h
  have h' : ∀ v : Fin 8 → ZMod 3, Matrix.mulVec (l6m3_M c) v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  have hinj : Function.Injective (l6m3_M c).mulVec := by
    intro x y hxy
    have hsub : Matrix.mulVec (l6m3_M c) (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (h' (x - y) hsub)
  have hMunit : IsUnit (l6m3_M c) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hMt : IsUnit (Matrix.transpose (l6m3_M c)) :=
    (Matrix.isUnit_transpose (l6m3_M c)).mpr hMunit
  have hAunit : IsUnit l6m3_A := by
    rw [← l6m3_MGM c hg]
    exact (hMt.mul l6m3_G_isUnit).mul hMunit
  have hAinj : Function.Injective (l6m3_A).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hAunit
  have hAm : Matrix.mulVec l6m3_A l6m3_mZ = 0 := by decide +kernel
  have hm0 : l6m3_mZ ≠ 0 := by decide +kernel
  exact hm0 (hAinj (by rw [hAm, Matrix.mulVec_zero]))

theorem e8_chain_extraVec
    (c : Fin 8 → (Fin Tag.E8.rank → ℤ))
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j) :
    ∃ b : Fin Tag.E8.rank → ℤ, (∀ j, iform (τ := .E8) b (c j) = if j = 2 then -1 else 0) ∧
      iform (τ := .E8) b b = 2 ∧
      (2 : ℤ) • c 0 + (4 : ℤ) • c 1 + (6 : ℤ) • c 2 + (5 : ℤ) • c 3 + (4 : ℤ) • c 4 +
        (3 : ℤ) • c 5 + (2 : ℤ) • c 6 + c 7 + (3 : ℤ) • b = 0 ∧
      (∀ k : Fin 8 → ZMod 3,
        (∀ t : Fin Tag.E8.rank, ∑ j, k j * (((c j t : ℤ)) : ZMod 3) = 0) →
          ∃ a : ZMod 3, ∀ j, k j = a * ((![2, 4, 6, 5, 4, 3, 2, 1] j : ℤ) : ZMod 3)) := by
  obtain ⟨v, hv0, hvk⟩ := l6m3_M_ker_nontrivial c hg
  have hrel : ∀ t, ∑ j, v j * ((c j t : ℤ) : ZMod 3) = 0 := by
    intro t
    have h := congrFun hvk t
    simp only [l6m3_M, Matrix.mulVec, dotProduct] at h
    calc ∑ j, v j * ((c j t : ℤ) : ZMod 3)
        = ∑ j, ((c j t : ℤ) : ZMod 3) * v j := Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := h
  obtain ⟨a, ha⟩ := l6m3_kernel_clause c hg v hrel
  have ha0 : a ≠ 0 := by
    intro h0
    exact hv0 (by simp [ha, h0])
  have hMmZ : Matrix.mulVec (l6m3_M c) l6m3_mZ = 0 := by
    have h1 : a • Matrix.mulVec (l6m3_M c) l6m3_mZ = 0 := by
      rw [← Matrix.mulVec_smul, ← ha, hvk]
    funext t
    have h2 : a * Matrix.mulVec (l6m3_M c) l6m3_mZ t = 0 := by
      have := congrFun h1 t
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ha0
    · exact h3
  let U : Fin Tag.E8.rank → ℤ := ∑ j : Fin 8, l6m3_m j • c j
  have hU : ∀ t : Fin Tag.E8.rank, U t = ∑ j : Fin 8, l6m3_m j * c j t := by
    intro t
    dsimp only [U]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hdiv : ∀ t : Fin Tag.E8.rank, (3 : ℤ) ∣ U t := by
    intro t
    have h := congrFun hMmZ t
    simp only [l6m3_M, l6m3_mZ, Matrix.mulVec, dotProduct] at h
    have hcast : ((U t : ℤ) : ZMod 3) = 0 := by
      rw [hU t]
      push_cast
      calc ∑ j, ((l6m3_m j : ℤ) : ZMod 3) * ((c j t : ℤ) : ZMod 3)
          = ∑ j, ((c j t : ℤ) : ZMod 3) * ((l6m3_m j : ℤ) : ZMod 3) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hcast
  let b : Fin Tag.E8.rank → ℤ := fun t => -(U t / 3)
  have hb3 : ∀ t : Fin Tag.E8.rank, (3 : ℤ) * b t = -U t := by
    intro t
    have hc := Int.ediv_mul_cancel (hdiv t)
    dsimp only [b]
    calc (3 : ℤ) * -(U t / 3) = -(U t / 3 * 3) := by ring
      _ = -U t := by rw [hc]
  have h3b : (3 : ℤ) • b = -U := by
    funext t
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact hb3 t
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro j
    have h1 : (3 : ℤ) * iform (τ := .E8) b (c j) = -iform (τ := .E8) U (c j) := by
      calc (3 : ℤ) * iform (τ := .E8) b (c j)
          = iform (τ := .E8) ((3 : ℤ) • b) (c j) := by rw [l6m3_iform_smul_left]
        _ = iform (τ := .E8) (-U) (c j) := by rw [h3b]
        _ = -iform (τ := .E8) U (c j) := l6m3_iform_neg_left U (c j)
    dsimp only [U] at h1
    rw [l6m3_iform_u c hg j] at h1
    have h2 : (3 : ℤ) * iform (τ := .E8) b (c j) = 3 * (if j = 2 then -1 else 0) := by
      rw [h1]
      by_cases hj : j = 2 <;> simp [hj]
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) h2
  · have h1 : (9 : ℤ) * iform (τ := .E8) b b = iform (τ := .E8) U U := by
      calc (9 : ℤ) * iform (τ := .E8) b b
          = 3 * (3 * iform (τ := .E8) b b) := by ring
        _ = 3 * iform (τ := .E8) b ((3 : ℤ) • b) := by rw [l6m3_iform_smul_right]
        _ = iform (τ := .E8) ((3 : ℤ) • b) ((3 : ℤ) • b) := by rw [l6m3_iform_smul_left]
        _ = iform (τ := .E8) (-U) (-U) := by rw [h3b]
        _ = iform (τ := .E8) U U := by
              rw [l6m3_iform_neg_left, l6m3_iform_neg_right]
              ring
    dsimp only [U] at h1
    rw [l6m3_iform_u_u c hg] at h1
    exact mul_left_cancel₀ (by norm_num : (9 : ℤ) ≠ 0) (by rw [h1]; norm_num)
  · have hu : (∑ j : Fin 8, l6m3_m j • c j) = (2 : ℤ) • c 0 + (4 : ℤ) • c 1 +
        (6 : ℤ) • c 2 + (5 : ℤ) • c 3 + (4 : ℤ) • c 4 + (3 : ℤ) • c 5 + (2 : ℤ) • c 6 + c 7 := by
      rw [Fin.sum_univ_eight]
      simp [l6m3_m]
    rw [← hu, h3b]
    dsimp only [U]
    rw [add_neg_cancel]
  · intro k hk
    obtain ⟨a, ha⟩ := l6m3_kernel_clause c hg k hk
    exact ⟨a, fun j => by
      rw [ha]
      simp only [l6m3_mZ, l6m3_m, Pi.smul_apply, smul_eq_mul]⟩

end CFSG.StandardType

end
