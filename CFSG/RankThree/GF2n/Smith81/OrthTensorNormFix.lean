module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Fix

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def cubeZero (n : ℕ) (K : Type*) [Field K] : Cube n K :=
  Pi.single (fun _ => (0 : Fin 2)) 1

theorem cubeZero_apply (x : Fin n → Fin 2) :
    cubeZero n K x = if x = fun _ => 0 then 1 else 0 := by
  simp [cubeZero, Pi.single_apply]

theorem kronMap_cubeZero_apply (k : Fin n → Matrix (Fin 2) (Fin 2) K) (x : Fin n → Fin 2) :
    kronMap k (cubeZero n K) x = ∏ i, k i (x i) 0 :=
  kronMap_basis k (fun _ => 0) x

theorem uniMat_apply_zero (β : K) (a : Fin 2) : uniMat β a 0 = if a = 0 then 1 else 0 := by
  fin_cases a <;> simp [uniMat]

theorem kronMap_uni_cubeZero (β : Fin n → K) :
    kronMap (fun i => uniMat (β i)) (cubeZero n K) = cubeZero n K := by
  funext x
  rw [kronMap_cubeZero_apply, cubeZero_apply]
  simp only [uniMat_apply_zero]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem permMap_cubeZero (π : Equiv.Perm (Fin n)) : permMap π (cubeZero n K) = cubeZero n K := by
  funext x
  rw [permMap_apply, cubeZero_apply, cubeZero_apply]
  have h : (x ∘ π = fun _ => 0) ↔ x = fun _ => 0 := by
    constructor
    · intro hx
      funext i
      have := congrFun hx (π.symm i)
      simpa using this
    · rintro rfl
      rfl
  simp only [h]

theorem exists_cubeU_apply (β : Fin n → K) :
    ∃ g ∈ cubeU n K, ∀ v, g v = kronMap (fun i => uniMat (β i)) v :=
  ⟨uniKron n K fun i => Multiplicative.ofAdd (β i), ⟨_, rfl⟩, fun _ => rfl⟩

theorem kronMap_uni_single (i : Fin n) :
    kronMap (fun j => uniMat ((Pi.single i 1 : Fin n → K) j)) = actMap i (uniMat 1) := by
  unfold actMap
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h, uniMat_zero]

theorem fixed_of_cubeU (v : Cube n K) (hv : ∀ g ∈ cubeU n K, g v = v) :
    ∃ c : K, v = c • cubeZero n K := by
  classical
  have key : ∀ (i : Fin n) (y : Fin n → Fin 2), y i = 1 → v y = 0 := by
    intro i y hy
    obtain ⟨g, hgU, hg⟩ := exists_cubeU_apply (Pi.single i 1 : Fin n → K)
    have h1 : actMap i (uniMat 1) v = v := by
      rw [← kronMap_uni_single, ← hg v]
      exact hv g hgU
    have h2 := congrFun h1 (Function.update y i 0)
    rw [actMap_apply, Fin.sum_univ_two] at h2
    have h3 : Function.update (Function.update y i 0) i 1 = y := by
      rw [Function.update_idem, Function.update_eq_self_iff.mpr hy.symm]
    rw [h3] at h2
    simpa [uniMat] using h2
  refine ⟨v (fun _ => 0), funext fun y => ?_⟩
  rw [Pi.smul_apply, cubeZero_apply, smul_eq_mul]
  by_cases hy : y = fun _ => 0
  · subst hy
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have hi1 : y i = 1 := by
      revert hi
      generalize y i = a
      fin_cases a <;> simp
    simp [hy, key i y hi1]

theorem upper_of_kron_cubeZero (h : Fin n → Matrix (Fin 2) (Fin 2) K)
    (hu : ∀ i, IsUnit (h i).det) (c : K)
    (hc : kronMap h (cubeZero n K) = c • cubeZero n K) : ∀ i, h i 1 0 = 0 := by
  classical
  have hcol : ∀ i, h i 1 0 = 0 → h i 0 0 ≠ 0 := by
    intro i h10 h00
    apply (hu i).ne_zero
    rw [Matrix.det_fin_two, h10, h00]
    ring
  let x : Fin n → Fin 2 := fun i => if h i 1 0 = 0 then 0 else 1
  have hprod : ∏ i, h i (x i) 0 ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    by_cases hi : h i 1 0 = 0
    · simpa [x, hi] using hcol i hi
    · simpa [x, hi]
  have hx : x = fun _ => 0 := by
    by_contra hne
    have := congrFun hc x
    rw [kronMap_cubeZero_apply, Pi.smul_apply, cubeZero_apply, if_neg hne, smul_zero] at this
    exact hprod this
  intro i
  by_contra hi
  have := congrFun hx i
  simp [x, hi] at this

end Fix

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
