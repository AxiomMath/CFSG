module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n m : ℕ} {d : List ℕ}

@[expose] noncomputable def glLin (g : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv

theorem glLin_apply (g : GL (Fin n) K) (v : Fin n → K) :
    glLin g v = (g : Matrix (Fin n) (Fin n) K).mulVec v := by
  simp [glLin, Matrix.GeneralLinearGroup.toLin_apply]

private theorem q2cFAc_glLin_mul (g h : GL (Fin n) K) :
    glLin (g * h) = (glLin h).trans (glLin g) := by
  ext v
  rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply,
    Matrix.GeneralLinearGroup.coe_mul]
  rw [Matrix.mulVec_mulVec]

private theorem q2cFAc_glLin_one :
    glLin (1 : GL (Fin n) K) = LinearEquiv.refl K (Fin n → K) := by
  ext v
  rw [glLin_apply]
  simp

theorem exists_flagMap (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : FlagK K n) :
    ∃ y : FlagK K n, ∀ j, y.E j = (x.E j).map e.toLinearMap := by
  refine ⟨⟨fun j => (x.E j).map e.toLinearMap, ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro i j hij
    exact Submodule.map_mono (x.mono hij)
  · intro j hj
    rw [LinearEquiv.finrank_map_eq, x.dim j hj]
  · intro j hj
    rw [x.top j hj, Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective

@[expose] noncomputable def flagMap (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : FlagK K n) :
    FlagK K n :=
  Classical.choose (exists_flagMap e x)

theorem flagMap_E (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : FlagK K n) (j : ℕ) :
    (flagMap e x).E j = (x.E j).map e.toLinearMap :=
  Classical.choose_spec (exists_flagMap e x) j

theorem flagMap_refl (x : FlagK K n) : flagMap (LinearEquiv.refl K (Fin n → K)) x = x := by
  apply FlagK.ext
  intro j
  rw [flagMap_E]
  simp

theorem flagMap_trans (e e' : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : FlagK K n) :
    flagMap e' (flagMap e x) = flagMap (e.trans e') x := by
  apply FlagK.ext
  intro j
  rw [flagMap_E, flagMap_E, flagMap_E]
  rw [← Submodule.map_comp]
  rfl

theorem flagMap_symm_flagMap (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (x : FlagK K n) :
    flagMap e.symm (flagMap e x) = x := by
  apply FlagK.ext
  intro j
  rw [flagMap_E, flagMap_E, ← Submodule.map_comp]
  have h : (e.symm.toLinearMap.comp e.toLinearMap : (Fin n → K) →ₗ[K] (Fin n → K)) =
      LinearMap.id := by
    ext v
    simp
  rw [h, Submodule.map_id]

theorem flagMap_injective (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) : Function.Injective (flagMap e) := by
  intro x y h
  have h' := congrArg (flagMap e.symm) h
  rwa [flagMap_symm_flagMap e x, flagMap_symm_flagMap e y] at h'

@[expose] noncomputable def flagAct (g : GL (Fin n) K) (x : FlagK K n) : FlagK K n :=
  flagMap (glLin g) x

theorem flagAct_one (x : FlagK K n) : flagAct (1 : GL (Fin n) K) x = x := by
  show flagMap (glLin (1 : GL (Fin n) K)) x = x
  rw [q2cFAc_glLin_one, flagMap_refl]

theorem flagAct_mul (g h : GL (Fin n) K) (x : FlagK K n) :
    flagAct (g * h) x = flagAct g (flagAct h x) := by
  show flagMap (glLin (g * h)) x = flagMap (glLin g) (flagMap (glLin h) x)
  rw [q2cFAc_glLin_mul]
  exact (flagMap_trans (glLin h) (glLin g) x).symm

theorem flagAct_inv_flagAct (g : GL (Fin n) K) (x : FlagK K n) :
    flagAct g⁻¹ (flagAct g x) = x := by
  rw [← flagAct_mul (g := g⁻¹) (h := g) (x := x), inv_mul_cancel, flagAct_one]

theorem flagMap_adj (e : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K)) {i : Fin m}
    {x y : FlagK K (m + 1)} :
    (flagSys K m).adj i (flagMap e x) (flagMap e y) ↔ (flagSys K m).adj i x y := by
  show (∀ j, j ≠ i.val + 1 → (flagMap e x).E j = (flagMap e y).E j) ↔
    (∀ j, j ≠ i.val + 1 → x.E j = y.E j)
  constructor
  · intro h j hj
    refine (Submodule.map_injective_of_injective e.injective) ?_
    simpa only [flagMap_E] using h j hj
  · intro h j hj
    rw [flagMap_E, flagMap_E, h j hj]

@[expose] noncomputable def flagMapIso (e : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K)) :
    ChamberIso (flagSys K m) (flagSys K m) where
  e := Equiv.refl _
  Φ := Equiv.ofBijective (flagMap e)
    ⟨flagMap_injective e, fun y => ⟨flagMap e.symm y, by
      have h := flagMap_symm_flagMap e.symm y
      rwa [LinearEquiv.symm_symm] at h⟩⟩
  adj_iff i x y := (flagMap_adj e).symm

theorem flagAct_stdFlag (g : GL (Fin n) K)
    (hg : (g : Matrix (Fin n) (Fin n) K).BlockTriangular id) :
    flagAct g (stdFlag K n) = stdFlag K n := by
  apply FlagK.ext
  intro j
  show (flagMap (glLin g) (stdFlag K n)).E j = (stdFlag K n).E j
  rw [flagMap_E]
  change (Vsub n j).map (glLin g).toLinearMap = Vsub n j
  refine Submodule.eq_of_le_of_finrank_eq ?_
    (LinearEquiv.finrank_map_eq (glLin g) (Vsub n j))
  rintro v ⟨w, hw, rfl⟩ i hi
  change (glLin g w) i = 0
  rw [glLin_apply, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val < i.val
  · rw [hg (i := i) (j := k) (show k < i from hk), zero_mul]
  · rw [hw k (le_trans hi (le_of_not_gt hk)), mul_zero]

theorem flagMap_mem_refSet (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ i, i < d.length →
      (Vsub n (d.getD i 0)).map e.toLinearMap = Vsub n (d.getD i 0))
    {x : FlagK K n} (hx : x ∈ refSet K n d) : flagMap e x ∈ refSet K n d := by
  intro i hi
  rw [flagMap_E, hx i hi]
  exact he i hi

theorem flagMap_image_refSet (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ i, i < d.length →
      (Vsub n (d.getD i 0)).map e.toLinearMap = Vsub n (d.getD i 0)) :
    flagMap e '' refSet K n d = refSet K n d := by
  have he' : ∀ i, i < d.length →
      (Vsub n (d.getD i 0)).map e.symm.toLinearMap = Vsub n (d.getD i 0) := by
    intro i hi
    have h : (e.symm.toLinearMap.comp e.toLinearMap : (Fin n → K) →ₗ[K] (Fin n → K)) =
        LinearMap.id := by
      ext v
      simp
    calc (Vsub n (d.getD i 0)).map e.symm.toLinearMap
        = ((Vsub n (d.getD i 0)).map e.toLinearMap).map e.symm.toLinearMap := by
          rw [he i hi]
      _ = (Vsub n (d.getD i 0)).map (e.symm.toLinearMap.comp e.toLinearMap) := by
          rw [Submodule.map_comp]
      _ = Vsub n (d.getD i 0) := by rw [h, Submodule.map_id]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact flagMap_mem_refSet e he hx
  · intro hy
    refine ⟨flagMap e.symm y, flagMap_mem_refSet e.symm he' hy, ?_⟩
    have h := flagMap_symm_flagMap e.symm y
    rwa [LinearEquiv.symm_symm] at h

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
