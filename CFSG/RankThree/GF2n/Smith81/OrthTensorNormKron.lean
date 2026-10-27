module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Cube

variable {K : Type*} [Field K] {n : ℕ}

abbrev Cube (n : ℕ) (K : Type*) := (Fin n → Fin 2) → K

@[expose] def kronMap (k : Fin n → Matrix (Fin 2) (Fin 2) K) : Cube n K →ₗ[K] Cube n K where
  toFun T x := ∑ y : Fin n → Fin 2, (∏ i, k i (x i) (y i)) * T y
  map_add' T T' := by
    funext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    funext x
    simp [Finset.mul_sum, mul_left_comm]

theorem kronMap_apply (k : Fin n → Matrix (Fin 2) (Fin 2) K) (T : Cube n K) (x : Fin n → Fin 2) :
    kronMap k T x = ∑ y : Fin n → Fin 2, (∏ i, k i (x i) (y i)) * T y := rfl

theorem prod_mul_apply (k l : Fin n → Matrix (Fin 2) (Fin 2) K) (x z : Fin n → Fin 2) :
    ∏ i, (k i * l i) (x i) (z i) =
      ∑ y : Fin n → Fin 2, (∏ i, k i (x i) (y i)) * ∏ i, l i (y i) (z i) := by
  simp_rw [Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

theorem kronMap_mul (k l : Fin n → Matrix (Fin 2) (Fin 2) K) :
    kronMap (k * l) = kronMap k ∘ₗ kronMap l := by
  refine LinearMap.ext fun T => funext fun x => ?_
  simp only [LinearMap.comp_apply, kronMap_apply, Finset.mul_sum, Pi.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [prod_mul_apply, Finset.sum_mul]
  simp [mul_assoc]

theorem kronMap_one : kronMap (1 : Fin n → Matrix (Fin 2) (Fin 2) K) = LinearMap.id := by
  refine LinearMap.ext fun T => funext fun x => ?_
  have h : ∀ y : Fin n → Fin 2, (∀ i, x i = y i) ↔ x = y := fun y => funext_iff.symm
  simp [kronMap_apply, Matrix.one_apply, Finset.prod_boole, h]

theorem kronMap_basis (k : Fin n → Matrix (Fin 2) (Fin 2) K) (y x : Fin n → Fin 2) :
    kronMap k (Pi.single y 1) x = ∏ i, k i (x i) (y i) := by
  simp [kronMap_apply, Pi.single_apply]

theorem kronMap_smul_apply (k : Fin n → Matrix (Fin 2) (Fin 2) K) (i : Fin n) (c : K)
    (T : Cube n K) :
    kronMap (Function.update k i (c • k i)) T = c • kronMap k T := by
  refine funext fun x => ?_
  simp only [kronMap_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => k j (x j) (y j)) (Finset.mem_univ i)]
  have : ∏ j ∈ Finset.univ.erase i, Function.update k i (c • k i) j (x j) (y j) =
      ∏ j ∈ Finset.univ.erase i, k j (x j) (y j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]
  simp only [Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

end Cube

section Perm

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def permMap (π : Equiv.Perm (Fin n)) : Cube n K ≃ₗ[K] Cube n K where
  toFun T x := T (x ∘ π)
  invFun T x := T (x ∘ π.symm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv T := by
    funext x
    simp [Function.comp_assoc]
  right_inv T := by
    funext x
    simp [Function.comp_assoc]

theorem permMap_apply (π : Equiv.Perm (Fin n)) (T : Cube n K) (x : Fin n → Fin 2) :
    permMap π T x = T (x ∘ π) := rfl

theorem permMap_mul (π ρ : Equiv.Perm (Fin n)) :
    (permMap (π * ρ) : Cube n K ≃ₗ[K] Cube n K) = permMap π * permMap ρ := by
  refine LinearEquiv.ext fun T => funext fun x => ?_
  simp [permMap_apply, Function.comp_assoc]

theorem permMap_one : (permMap (1 : Equiv.Perm (Fin n)) : Cube n K ≃ₗ[K] Cube n K) = 1 := by
  refine LinearEquiv.ext fun T => funext fun x => ?_
  simp [permMap_apply]

theorem kronMap_comp_permMap (k : Fin n → Matrix (Fin 2) (Fin 2) K) (π : Equiv.Perm (Fin n)) :
    kronMap k ∘ₗ (permMap π : Cube n K ≃ₗ[K] Cube n K).toLinearMap =
      (permMap π : Cube n K ≃ₗ[K] Cube n K).toLinearMap ∘ₗ kronMap (fun i => k (π i)) := by
  refine LinearMap.ext fun T => funext fun x => ?_
  simp only [LinearMap.comp_apply, kronMap_apply, LinearEquiv.coe_coe, permMap_apply]
  let e : (Fin n → Fin 2) ≃ (Fin n → Fin 2) := Equiv.arrowCongr π.symm (Equiv.refl _)
  refine Fintype.sum_equiv e _ _ (fun y => ?_)
  have h1 : (e y) = y ∘ π := by
    funext i; simp [e, Equiv.arrowCongr]
  rw [h1]
  congr 1
  exact (Equiv.prod_comp π (fun j => k j (x j) (y j))).symm

end Perm

section Act

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def actMap (i : Fin n) (A : Matrix (Fin 2) (Fin 2) K) : Cube n K →ₗ[K] Cube n K :=
  kronMap (Pi.mulSingle i A)

theorem actMap_apply (i : Fin n) (A : Matrix (Fin 2) (Fin 2) K) (T : Cube n K)
    (x : Fin n → Fin 2) :
    actMap i A T x = ∑ b : Fin 2, A (x i) b * T (Function.update x i b) := by
  classical
  unfold actMap
  rw [kronMap_apply]
  have key : ∀ y : Fin n → Fin 2, (∏ j, (Pi.mulSingle i A : Fin n → Matrix (Fin 2) (Fin 2) K) j
      (x j) (y j)) = if (∀ j, j ≠ i → y j = x j) then A (x i) (y i) else 0 := by
    intro y
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Pi.mulSingle_eq_same]
    have h2 : ∏ j ∈ Finset.univ.erase i, (Pi.mulSingle i A : Fin n → Matrix (Fin 2) (Fin 2) K) j
        (x j) (y j) = ∏ j ∈ Finset.univ.erase i, (if x j = y j then (1 : K) else 0) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj), Matrix.one_apply]
    rw [h2, Finset.prod_boole]
    by_cases hc : ∀ j, j ≠ i → y j = x j
    · rw [if_pos ?_, if_pos hc, mul_one]
      intro j hj
      exact (hc j (Finset.ne_of_mem_erase hj)).symm
    · rw [if_neg, if_neg hc, mul_zero]
      intro h
      apply hc
      intro j hj
      exact (h j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)).symm
  simp_rw [key, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfil : Finset.univ.filter (fun y : Fin n → Fin 2 => ∀ j, j ≠ i → y j = x j) =
      Finset.univ.image (fun b : Fin 2 => Function.update x i b) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      refine ⟨y i, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, hy j hj]
    · rintro ⟨b, rfl⟩ j hj
      rw [Function.update_of_ne hj]
  rw [hfil, Finset.sum_image (fun b _ b' _ h => by
    simpa using congrFun h i)]
  simp

theorem actMap_mul (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) K) :
    actMap i (A * B) = actMap i A ∘ₗ actMap i B := by
  unfold actMap
  rw [← kronMap_mul, Pi.mulSingle_mul]

theorem actMap_one (i : Fin n) : actMap i (1 : Matrix (Fin 2) (Fin 2) K) = LinearMap.id := by
  unfold actMap
  rw [← kronMap_one]
  congr 1
  exact Pi.mulSingle_one i

theorem actMap_comm {i j : Fin n} (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) K) :
    actMap i A ∘ₗ actMap j B = actMap j B ∘ₗ actMap i A := by
  unfold actMap
  rw [← kronMap_mul, ← kronMap_mul]
  congr 1
  exact (Pi.mulSingle_commute (f := fun _ : Fin n => Matrix (Fin 2) (Fin 2) K) hij A B).eq

theorem actMap_comp_permMap (π : Equiv.Perm (Fin n)) (i : Fin n)
    (A : Matrix (Fin 2) (Fin 2) K) :
    actMap i A ∘ₗ (permMap π : Cube n K ≃ₗ[K] Cube n K).toLinearMap =
      (permMap π : Cube n K ≃ₗ[K] Cube n K).toLinearMap ∘ₗ actMap (π.symm i) A := by
  unfold actMap
  rw [kronMap_comp_permMap]
  congr 2
  funext j
  by_cases h : π j = i
  · have : j = π.symm i := by rw [← h]; simp
    subst this
    simp [h]
  · have h' : j ≠ π.symm i := fun hj => h (by rw [hj]; simp)
    rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h']

end Act

section Groups

variable {K : Type*} [Field K] {n : ℕ}

abbrev SL2 (K : Type*) [Field K] := Matrix.SpecialLinearGroup (Fin 2) K

@[expose] def kronSL (k : Fin n → SL2 K) : Cube n K ≃ₗ[K] Cube n K :=
  LinearEquiv.ofLinear (kronMap fun i => ((k i : SL2 K) : Matrix (Fin 2) (Fin 2) K))
    (kronMap fun i => (((k i)⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K))
    (by
      rw [← kronMap_mul, ← kronMap_one]
      congr 1
      funext i
      show ((k i : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        (((k i)⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])
    (by
      rw [← kronMap_mul, ← kronMap_one]
      congr 1
      funext i
      show (((k i)⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        ((k i : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one])

theorem kronSL_apply (k : Fin n → SL2 K) (v : Cube n K) :
    kronSL k v = kronMap (fun i => ((k i : SL2 K) : Matrix (Fin 2) (Fin 2) K)) v := rfl

@[expose] def kronSLHom (n : ℕ) (K : Type*) [Field K] :
    (Fin n → SL2 K) →* (Cube n K ≃ₗ[K] Cube n K) where
  toFun := kronSL
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    rw [kronSL_apply]
    simp only [Pi.one_apply, Matrix.SpecialLinearGroup.coe_one]
    exact LinearMap.congr_fun (kronMap_one (K := K) (n := n)) v
  map_mul' k l := by
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, kronSL_apply, kronSL_apply, kronSL_apply]
    have : (fun i => (((k * l) i : SL2 K) : Matrix (Fin 2) (Fin 2) K)) =
        (fun i => ((k i : SL2 K) : Matrix (Fin 2) (Fin 2) K)) *
          (fun i => ((l i : SL2 K) : Matrix (Fin 2) (Fin 2) K)) := by
      funext i
      simp
    rw [this, kronMap_mul]
    rfl

@[expose] def cubeE (n : ℕ) (K : Type*) [Field K] : Subgroup (Cube n K ≃ₗ[K] Cube n K) :=
  (kronSLHom n K).range

theorem mem_cubeE {g : Cube n K ≃ₗ[K] Cube n K} :
    g ∈ cubeE n K ↔ ∃ k : Fin n → Matrix (Fin 2) (Fin 2) K, (∀ i, (k i).det = 1) ∧
      ∀ v, g v = kronMap k v := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨fun i => (k i : Matrix (Fin 2) (Fin 2) K), fun i => (k i).2, fun v => rfl⟩
  · rintro ⟨k, hk, hg⟩
    exact ⟨fun i => ⟨k i, hk i⟩, LinearEquiv.ext fun v => (hg v).symm⟩

@[expose] def cubeF (n : ℕ) (K : Type*) [Field K] (i : Fin n) :
    Subgroup (Cube n K ≃ₗ[K] Cube n K) :=
  ((kronSLHom n K).comp (MonoidHom.mulSingle (fun _ : Fin n => SL2 K) i)).range

theorem coe_mulSingle_SL2 (i : Fin n) (A : SL2 K) :
    (fun j => ((Pi.mulSingle i A : Fin n → SL2 K) j : Matrix (Fin 2) (Fin 2) K)) =
      (Pi.mulSingle i (A : Matrix (Fin 2) (Fin 2) K) : Fin n → Matrix (Fin 2) (Fin 2) K) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp

theorem mem_cubeF {g : Cube n K ≃ₗ[K] Cube n K} {i : Fin n} :
    g ∈ cubeF n K i ↔ ∃ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 ∧ ∀ v, g v = actMap i A v := by
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨(A : Matrix (Fin 2) (Fin 2) K), A.2, fun v => ?_⟩
    show kronSL (Pi.mulSingle i A) v = _
    rw [kronSL_apply, coe_mulSingle_SL2]
    rfl
  · rintro ⟨A, hA, hg⟩
    let A' : SL2 K := ⟨A, hA⟩
    refine ⟨A', LinearEquiv.ext fun v => ?_⟩
    show kronSL (Pi.mulSingle i A' : Fin n → SL2 K) v = g v
    rw [kronSL_apply, coe_mulSingle_SL2, hg v]
    rfl

@[expose] def uniMat (β : K) : Matrix (Fin 2) (Fin 2) K := !![1, β; 0, 1]

theorem uniMat_det (β : K) : (uniMat β).det = 1 := by
  simp [uniMat, Matrix.det_fin_two]

theorem uniMat_mul (β γ : K) : uniMat β * uniMat γ = uniMat (β + γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem uniMat_zero : uniMat (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat]

@[expose] def uniSL (β : K) : SL2 K := ⟨uniMat β, uniMat_det β⟩

@[expose] def uniSLHom (K : Type*) [Field K] : Multiplicative K →* SL2 K where
  toFun β := uniSL (Multiplicative.toAdd β)
  map_one' := Subtype.ext (by simp [uniSL, uniMat_zero])
  map_mul' β γ := by
    apply Subtype.ext
    show uniMat (Multiplicative.toAdd β + Multiplicative.toAdd γ) =
      uniMat (Multiplicative.toAdd β) * uniMat (Multiplicative.toAdd γ)
    rw [uniMat_mul]

@[expose] def uniKron (n : ℕ) (K : Type*) [Field K] :
    (Fin n → Multiplicative K) →* (Cube n K ≃ₗ[K] Cube n K) :=
  (kronSLHom n K).comp (Pi.monoidHom fun i => (uniSLHom K).comp (Pi.evalMonoidHom _ i))

@[expose] def cubeU (n : ℕ) (K : Type*) [Field K] : Subgroup (Cube n K ≃ₗ[K] Cube n K) :=
  (uniKron n K).range

theorem mem_cubeU {g : Cube n K ≃ₗ[K] Cube n K} :
    g ∈ cubeU n K ↔ ∃ β : Fin n → K, ∀ v, g v = kronMap (fun i => uniMat (β i)) v := by
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨fun i => Multiplicative.toAdd (β i), fun v => rfl⟩
  · rintro ⟨β, hg⟩
    exact ⟨fun i => Multiplicative.ofAdd (β i), LinearEquiv.ext fun v => (hg v).symm⟩

theorem cubeF_le_cubeE (i : Fin n) : cubeF n K i ≤ cubeE n K := by
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_cubeF.mp hg
  refine mem_cubeE.mpr ⟨Pi.mulSingle i A, fun j => ?_, hgA⟩
  by_cases h : j = i
  · subst h; simpa using hA
  · rw [Pi.mulSingle_eq_of_ne h]; simp

theorem cubeU_le_cubeE : cubeU n K ≤ cubeE n K := by
  intro g hg
  obtain ⟨β, hβ⟩ := mem_cubeU.mp hg
  exact mem_cubeE.mpr ⟨fun i => uniMat (β i), fun i => uniMat_det _, hβ⟩

end Groups


end CFSG.RankThree.GF2n.Smith81.OrthTN

end
