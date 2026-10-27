module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLFixed

public section

namespace CFSG.StandardType.KGPSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix AutPSL

variable {K : Type*} [Field K]

private abbrev levi {m : ℕ} (hm : 3 ≤ m) : Subgroup (projectiveSL (m + 1) K) :=
  Subgroup.centralizer {proj (m + 1) K (AutPSL.rootInv (K := K) (m := m) (by omega))} ⊓
    Subgroup.centralizer {proj (m + 1) K (SpecialLinearGroup.transvection
      (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K))}

private noncomputable abbrev t0 {m : ℕ} (hm : 3 ≤ m) :
    SpecialLinearGroup (Fin (m + 1)) K :=
  AutPSL.rootInv (K := K) (m := m) (by omega)

private noncomputable abbrev ty {m : ℕ} (hm : 3 ≤ m) :
    SpecialLinearGroup (Fin (m + 1)) K :=
  SpecialLinearGroup.transvection (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K)

private lemma t0_mul_self [CharP K 2] {m : ℕ} (hm : 3 ≤ m) :
    t0 (K := K) hm * t0 (K := K) hm = 1 := by
  simpa [t0] using HypSixTypeA.transvection_mul_self
    (AutPSL.last_ne_zero (m := m) (by omega)) (1 : K)

private lemma ty_mul_self [CharP K 2] {m : ℕ} (hm : 3 ≤ m) :
    ty (K := K) hm * ty (K := K) hm = 1 := by
  simpa [ty] using HypSixTypeA.transvection_mul_self
    (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K)

private lemma mem_levi_of_commute {m : ℕ} (hm : 3 ≤ m)
    {g : SpecialLinearGroup (Fin (m + 1)) K}
    (h0 : g * t0 (K := K) hm = t0 (K := K) hm * g)
    (hy : g * ty (K := K) hm = ty (K := K) hm * g) :
    proj (m + 1) K g ∈ levi (K := K) hm := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h0]
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]

variable {n : ℕ} [NeZero n] [CharP K 2]

private lemma col_zero_of_commute_single (M : Matrix (Fin n) (Fin n) K) {l : Fin n}
    (h : M * (1 + Matrix.single (0 : Fin n) l 1) =
      (1 + Matrix.single (0 : Fin n) l 1) * M) :
    M *ᵥ Pi.single (0 : Fin n) 1 = (M l l) • Pi.single (0 : Fin n) 1 := by
  have h' : M * Matrix.single (0 : Fin n) l 1 = Matrix.single (0 : Fin n) l 1 * M := by
    have h2 : M + M * Matrix.single (0 : Fin n) l 1 =
        M + Matrix.single (0 : Fin n) l 1 * M := by
      simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] using h
    exact add_left_cancel h2
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have h1 := congrFun (congrFun h' i) l
  rw [Matrix.mul_single_apply_same, mul_one] at h1
  by_cases hi : i = 0
  · subst hi
    rw [Matrix.single_mul_apply_same, one_mul] at h1
    simpa using h1
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi] at h1
    simp [hi, h1]

private lemma entry_conj_single_one (D : Matrix (Fin n) (Fin n) K) {r s i j : Fin n} :
    (D * Matrix.single r s (1 : K) * D⁻¹) i j = D i r * D⁻¹ s j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne (1 : K) r s i b hb, zero_mul]
  · intro hs
    simp at hs

private lemma entry_conj_single (D : Matrix (Fin n) (Fin n) K) {r s i j : Fin n} (a : K)
    (hD : D * D⁻¹ = 1) (hij : i ≠ j) :
    (D * (1 + Matrix.single r s a) * D⁻¹) i j =
      a * ((D * Matrix.single r s (1 : K) * D⁻¹) i j) := by
  have h1 : D * (1 + Matrix.single r s a) * D⁻¹ =
      D * D⁻¹ + D * Matrix.single r s a * D⁻¹ := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
  rw [h1, Matrix.add_apply, hD, Matrix.one_apply, if_neg hij, zero_add]
  rw [show Matrix.single r s a = a • Matrix.single r s (1 : K) by
    ext x y; simp [Matrix.single_apply, Matrix.smul_apply]]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]


private lemma field_eq_one_of_conj_single (D : GL (Fin n) K) {σ : K ≃+* K}
    {r s i j : Fin n} (hij : i ≠ j)
    (h : ∀ t : K, (D : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single r s (σ t)) *
        ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j t) :
    σ = 1 := by
  have hDval : ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((D : Matrix (Fin n) (Fin n) K))⁻¹ := Matrix.GeneralLinearGroup.coe_inv D
  have hD : (D : Matrix (Fin n) (Fin n) K) * ((D : Matrix (Fin n) (Fin n) K))⁻¹ = 1 := by
    have h := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K))
      (mul_inv_cancel D)
    simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv] using h
  rw [hDval] at h
  have hc : ((D : Matrix (Fin n) (Fin n) K) * Matrix.single r s (1 : K) *
      ((D : Matrix (Fin n) (Fin n) K))⁻¹) i j = 1 := by
    have h1 := congrFun (congrFun (h 1) i) j
    rw [show σ 1 = 1 from map_one σ] at h1
    rw [entry_conj_single (D : Matrix (Fin n) (Fin n) K) (1 : K) hD hij, one_mul] at h1
    simpa [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hij] using h1
  ext t
  have h2 := congrFun (congrFun (h t) i) j
  rw [entry_conj_single (D : Matrix (Fin n) (Fin n) K) (σ t) hD hij] at h2
  rw [hc, mul_one] at h2
  simpa [Matrix.one_apply, Matrix.single_apply, hij] using h2

private lemma conj_eq_of_proj_eq_transvection (g t : SpecialLinearGroup (Fin n) K)
    (ht : t * t = 1) (h : proj n K (g * t * g⁻¹) = proj n K t) :
    g * t * g⁻¹ = t := by
  set X : SpecialLinearGroup (Fin n) K := g * t * g⁻¹ with hX
  have hXX : X * X = 1 := by
    rw [hX]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hs : X⁻¹ * t ∈ scalars n K := proj_eq_proj_iff.mp h
  obtain ⟨c, hc, hcmat⟩ := mem_scalars.mp hs
  have h1 : ((X⁻¹ * t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) (c : K) := hcmat
  have htval : (t : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) := by
    have h2 : t = X * scalarElement c hc := by
      conv_lhs => rw [← mul_inv_cancel_left X t]
      rw [show X⁻¹ * t = scalarElement c hc from Subtype.ext h1]
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement]
  have htt : (t : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ht, Matrix.SpecialLinearGroup.coe_one]
  have hXXmat : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hXX, Matrix.SpecialLinearGroup.coe_one]
  have hSc : scalar (Fin n) (c : K) * scalar (Fin n) (c : K) =
      scalar (Fin n) ((c : K) * (c : K)) := by
    rw [Matrix.scalar_apply]
    exact Matrix.diagonal_mul_diagonal _ _
  have hsq : (t : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) ((c : K) * (c : K)) := by
    rw [htval]
    calc (X : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) *
        ((X : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)) =
        (X : Matrix (Fin n) (Fin n) K) * (scalar (Fin n) (c : K) *
          (X : Matrix (Fin n) (Fin n) K)) * scalar (Fin n) (c : K) := by
          noncomm_ring
      _ = (X : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) *
          scalar (Fin n) (c : K)) * scalar (Fin n) (c : K) := by
          rw [Matrix.scalar_comm (c : K) (fun r => mul_comm (c : K) r)]
      _ = ((X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K)) *
          (scalar (Fin n) (c : K) * scalar (Fin n) (c : K)) := by
          noncomm_ring
      _ = 1 * scalar (Fin n) ((c : K) * (c : K)) := by rw [hXXmat, hSc]
      _ = scalar (Fin n) ((c : K) * (c : K)) := by rw [Matrix.one_mul]
  have hcc : (c : K) * (c : K) = 1 := by
    have hsq1 : scalar (Fin n) ((c : K) * (c : K)) = 1 := by rw [← hsq, htt]
    have := congrFun (congrFun hsq1 (0 : Fin n)) (0 : Fin n)
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply] using this
  have hc1 : c = 1 := Units.ext (HypSixTypeA.eq_one_of_mul_self_eq_one hcc)
  apply Subtype.ext
  rw [htval, hc1, Units.val_one, Matrix.scalar_apply, Matrix.diagonal_one, Matrix.mul_one]

private lemma commute_of_mem_centralizer {g t : SpecialLinearGroup (Fin n) K} (ht : t * t = 1)
    (h : proj n K g ∈ Subgroup.centralizer {proj n K t}) : g * t = t * g := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp h
  have hconj : proj n K (g * t * g⁻¹) = proj n K t := by
    rw [map_mul, map_mul, map_inv]
    calc proj n K g * proj n K t * (proj n K g)⁻¹ =
        proj n K t * proj n K g * (proj n K g)⁻¹ := by rw [hc]
      _ = proj n K t := by simp
  have hgt := conj_eq_of_proj_eq_transvection g t ht hconj
  calc g * t = g * t * g⁻¹ * g := by simp
    _ = t * g := by rw [hgt]

private lemma col_zero_of_commute_sl (b : SpecialLinearGroup (Fin n) K) {l : Fin n}
    (h0l : (0 : Fin n) ≠ l)
    (h : b * SpecialLinearGroup.transvection h0l 1 =
      SpecialLinearGroup.transvection h0l 1 * b) :
    (b : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 =
      ((b : Matrix (Fin n) (Fin n) K) l l) • Pi.single (0 : Fin n) 1 := by
  apply col_zero_of_commute_single
  have h' := congrArg (fun x : SpecialLinearGroup (Fin n) K =>
    (x : Matrix (Fin n) (Fin n) K)) h
  simpa [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe] using h'

private lemma col_zero_of_commute_gl (A : GL (Fin n) K) {l : Fin n} (h0l : (0 : Fin n) ≠ l)
    (h : A * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection h0l 1) =
      SpecialLinearGroup.toGL (SpecialLinearGroup.transvection h0l 1) * A) :
    (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 =
      ((A : Matrix (Fin n) (Fin n) K) l l) • Pi.single (0 : Fin n) 1 := by
  apply col_zero_of_commute_single
  have h' := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
  simpa [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.transvection_coe] using h'

private lemma transvection_mulVec_e0 {i j : Fin n} (hij : i ≠ j) (hj0 : j ≠ 0) (t : K) :
    ((SpecialLinearGroup.transvection hij t : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 = Pi.single (0 : Fin n) 1 := by
  rw [AutPSL.transvection_mulVec, Pi.single_eq_of_ne hj0, mul_zero, Pi.single_zero,
    add_zero]


private lemma slConj_commute_of_commute (A : GL (Fin n) K)
    {g t : SpecialLinearGroup (Fin n) K}
    (hA : A * SpecialLinearGroup.toGL t = SpecialLinearGroup.toGL t * A)
    (hg : g * t = t * g) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A g * t =
      t * CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A g := by
  have hAinv : A⁻¹ * SpecialLinearGroup.toGL t = SpecialLinearGroup.toGL t * A⁻¹ := by
    calc A⁻¹ * SpecialLinearGroup.toGL t
        = A⁻¹ * (SpecialLinearGroup.toGL t * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * SpecialLinearGroup.toGL t) * A⁻¹ := by rw [← hA]
      _ = SpecialLinearGroup.toGL t * A⁻¹ := by group
  have hgt : SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL t =
      SpecialLinearGroup.toGL t * SpecialLinearGroup.toGL g := by
    rw [← map_mul, ← map_mul, hg]
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  calc A * SpecialLinearGroup.toGL g * A⁻¹ * SpecialLinearGroup.toGL t
      = A * SpecialLinearGroup.toGL g * (A⁻¹ * SpecialLinearGroup.toGL t) := by group
    _ = A * SpecialLinearGroup.toGL g * (SpecialLinearGroup.toGL t * A⁻¹) := by rw [hAinv]
    _ = A * (SpecialLinearGroup.toGL g * SpecialLinearGroup.toGL t) * A⁻¹ := by group
    _ = A * (SpecialLinearGroup.toGL t * SpecialLinearGroup.toGL g) * A⁻¹ := by rw [hgt]
    _ = (A * SpecialLinearGroup.toGL t) * SpecialLinearGroup.toGL g * A⁻¹ := by group
    _ = (SpecialLinearGroup.toGL t * A) * SpecialLinearGroup.toGL g * A⁻¹ := by rw [hA]
    _ = SpecialLinearGroup.toGL t * (A * SpecialLinearGroup.toGL g * A⁻¹) := by group

private lemma scalar_mulVec_single (a : K) :
    Matrix.scalar (Fin n) a *ᵥ Pi.single (0 : Fin n) 1 = a • Pi.single (0 : Fin n) 1 := by
  ext i
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]

private lemma matrix_eq_of_proj_eq_of_col {X g : SpecialLinearGroup (Fin n) K}
    (h : proj n K X = proj n K g)
    (hX : (X : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 = Pi.single (0 : Fin n) 1)
    (hg : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 = Pi.single (0 : Fin n) 1) :
    (X : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, hc, hcmat⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  have hmat : (X : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) =
      (g : Matrix (Fin n) (Fin n) K) := by
    rw [← hcmat, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hc1 : (c : K) = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ Pi.single (0 : Fin n) 1) hmat
    rw [← Matrix.mulVec_mulVec, scalar_mulVec_single, Matrix.mulVec_smul, hX, hg] at h
    have := congrFun h 0
    simpa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] using this
  rw [hc1, Matrix.scalar_apply, Matrix.diagonal_one, Matrix.mul_one] at hmat
  exact hmat

private lemma scalar_of_proj_eq_of_col {X g : SpecialLinearGroup (Fin n) K}
    (h : proj n K X = proj n K g) {a b : K}
    (hX : (X : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 =
      a • Pi.single (0 : Fin n) 1)
    (hg : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 =
      b • Pi.single (0 : Fin n) 1) :
    ∃ c : Kˣ, c ^ n = 1 ∧ (c : K) * a = b := by
  obtain ⟨c, hc, hcmat⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  have hmat : (X : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) =
      (g : Matrix (Fin n) (Fin n) K) := by
    rw [← hcmat, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  refine ⟨c, hc, ?_⟩
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ Pi.single (0 : Fin n) 1) hmat
  rw [← Matrix.mulVec_mulVec, scalar_mulVec_single, Matrix.mulVec_smul, hX, hg] at h
  have := congrFun h 0
  simpa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_assoc] using this



private noncomputable def diagElt (f : Fin n → K) (hf : ∏ i, f i = 1) :
    SpecialLinearGroup (Fin n) K :=
  ⟨Matrix.diagonal f, by rw [Matrix.det_diagonal]; exact hf⟩

private lemma coe_diagElt (f : Fin n → K) (hf : ∏ i, f i = 1) :
    (diagElt f hf : Matrix (Fin n) (Fin n) K) = Matrix.diagonal f := rfl

private lemma prod_inv_eq_one {f : Fin n → K} (hf : ∏ i, f i = 1) :
    ∏ i, (f i)⁻¹ = 1 := by
  rw [Finset.prod_inv_distrib, hf, inv_one]

private lemma diagElt_inv (f : Fin n → K) (hf : ∏ i, f i = 1) :
    (diagElt f hf)⁻¹ = diagElt (fun i => (f i)⁻¹) (prod_inv_eq_one hf) := by
  have hfnz : ∀ i, f i ≠ 0 := by
    intro i hi
    have h0 : ∏ j, f j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h0] at hf
    exact zero_ne_one hf
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagElt, coe_diagElt,
    Matrix.diagonal_mul_diagonal, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
    exact mul_inv_cancel₀ (hfnz i)
  · rw [if_neg hij, if_neg hij]

private lemma gammaSL_diagElt (f : Fin n → K) (hf : ∏ i, f i = 1) :
    (AutPSL.gammaSL (diagElt f hf) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => (f (Fin.rev i))⁻¹) := by
  rw [AutPSL.coe_gammaSL, diagElt_inv, coe_diagElt, Matrix.diagonal_transpose]
  change (Matrix.diagonal (fun i => (f i)⁻¹)).submatrix Fin.rev Fin.rev =
    Matrix.diagonal (fun i => (f (Fin.rev i))⁻¹)
  rw [Matrix.submatrix_diagonal _ _ Fin.rev_injective]
  rfl

private lemma prod_rev_inv_eq_one {f : Fin n → K} (hf : ∏ i, f i = 1) :
    ∏ i, (f (Fin.rev i))⁻¹ = 1 := by
  have hfrev : ∏ i, f (Fin.rev i) = 1 := by
    change ∏ i, f (Fin.revPerm i) = 1
    rw [Equiv.prod_comp Fin.revPerm f]
    exact hf
  exact prod_inv_eq_one hfrev

private lemma graphAut_diagElt (f : Fin n → K) (hf : ∏ i, f i = 1) :
    AutPSL.graphAut (proj n K (diagElt f hf)) =
      proj n K (diagElt (fun i => (f (Fin.rev i))⁻¹) (prod_rev_inv_eq_one hf)) := by
  rw [AutPSL.graphAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_diagElt]
  exact gammaSL_diagElt f hf

private lemma diagElt_mulVec_e0 (f : Fin n → K) (hf : ∏ i, f i = 1) :
    (diagElt f hf : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (0 : Fin n) 1 =
      (f 0) • Pi.single (0 : Fin n) 1 := by
  rw [coe_diagElt]
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hi : i = 0 <;> simp [hi]

private lemma diagElt_commute_transvection (f : Fin n → K) (hf : ∏ i, f i = 1)
    {i j : Fin n} (hij : i ≠ j) (hfij : f i = f j) :
    diagElt f hf * SpecialLinearGroup.transvection hij 1 =
      SpecialLinearGroup.transvection hij 1 * diagElt f hf := by
  apply Subtype.ext
  change Matrix.diagonal f * (1 + Matrix.single i j 1) =
    (1 + Matrix.single i j 1) * Matrix.diagonal f
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  ext a b
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [hfij]
  · have hs : Matrix.single i j (1 : K) a b = 0 := by
      rw [Matrix.single_apply]
      split_ifs with h'
      · exact absurd ⟨h'.1.symm, h'.2.symm⟩ h
      · rfl
    by_cases hab : a = b
    · subst hab
      simp [hs]
    · simp [hs, hab]

private noncomputable def cornerFun {m : ℕ} (hm : 3 ≤ m) (lam : K) : Fin (m + 1) → K :=
  fun i => if i = 0 then lam else if i = Fin.last m then lam else if i = 1 then lam⁻¹ * lam⁻¹ else 1

private lemma prod_cornerFun {m : ℕ} (hm : 3 ≤ m) {lam : K} (hlam : lam ≠ 0) :
    ∏ i : Fin (m + 1), cornerFun (K := K) hm lam i = 1 := by
  have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := (AutPSL.last_ne_zero (m := m) (by omega)).symm
  have hm0 : m ≠ 0 := by omega
  have hmod : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have h01 : (0 : Fin (m + 1)) ≠ 1 := by
    intro h
    have h' : (0 : Fin (m + 1)).val = (1 : Fin (m + 1)).val := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_one', hmod] at h'
    omega
  have hl1 : Fin.last m ≠ (1 : Fin (m + 1)) := by
    intro h
    have h' : (Fin.last m).val = (1 : Fin (m + 1)).val := congrArg Fin.val h
    rw [Fin.val_last, Fin.val_one', hmod] at h'
    omega
  have h1l : (1 : Fin (m + 1)) ≠ Fin.last m := hl1.symm
  have hsub : ({0, Fin.last m, (1 : Fin (m + 1))} : Finset (Fin (m + 1))) ⊆ Finset.univ := by
    simp
  rw [← Finset.prod_subset hsub]
  · rw [Finset.prod_insert (by simp [h0l, h01]), Finset.prod_insert (by simp [hl1]),
      Finset.prod_singleton]
    simp [cornerFun, h0l, h01, hl1, h1l, hlam, hm0]
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hx0, hxl, hx1⟩ := hx
    simp [cornerFun, hx0, hxl, hx1]

private lemma cornerFun_zero {m : ℕ} (hm : 3 ≤ m) (lam : K) :
    cornerFun (K := K) hm lam 0 = lam := by
  simp [cornerFun]

private lemma cornerFun_last {m : ℕ} (hm : 3 ≤ m) (lam : K) :
    cornerFun (K := K) hm lam (Fin.last m) = lam := by
  have h0l : (Fin.last m : Fin (m + 1)) ≠ 0 := AutPSL.last_ne_zero (m := m) (by omega)
  simp [cornerFun, h0l]

private lemma cornerFun_rev_zero {m : ℕ} (hm : 3 ≤ m) (lam : K) :
    cornerFun (K := K) hm lam (Fin.rev 0) = lam := by
  simpa using cornerFun_last (K := K) hm lam

private lemma cornerFun_rev_last {m : ℕ} (hm : 3 ≤ m) (lam : K) :
    cornerFun (K := K) hm lam (Fin.rev (Fin.last m)) = lam := by
  simpa using cornerFun_zero (K := K) hm lam

private lemma entry_D_eq (D : GL (Fin n) K) {i j r s : Fin n} (hij : i ≠ j)
    (hD : (D : Matrix (Fin n) (Fin n) K) *
      ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1) :
    ((D : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single r s (1 : K)) *
      ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j =
      (D : Matrix (Fin n) (Fin n) K) i r *
        ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) s j := by
  have hD' : (D : Matrix (Fin n) (Fin n) K) *
      ((D : Matrix (Fin n) (Fin n) K))⁻¹ = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact hD
  rw [Matrix.GeneralLinearGroup.coe_inv]
  rw [entry_conj_single (D : Matrix (Fin n) (Fin n) K) (1 : K) hD' hij, one_mul,
    entry_conj_single_one]



private lemma col_actions_of_levi {m : ℕ} (hm : 3 ≤ m)
    {A : GL (Fin (m + 1)) K}
    (hA₂ : A * SpecialLinearGroup.toGL (ty (K := K) hm) =
      SpecialLinearGroup.toGL (ty (K := K) hm) * A)
    {b : SpecialLinearGroup (Fin (m + 1)) K} {h : projectiveSL (m + 1) K}
    (hb : proj (m + 1) K b = h) (hh : h ∈ levi (K := K) hm) :
    ∃ β β' α α' : K,
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
        β • Pi.single (0 : Fin (m + 1)) 1 ∧
      ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
        β' • Pi.single (0 : Fin (m + 1)) 1 ∧
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
        α • Pi.single (0 : Fin (m + 1)) 1 ∧
      ((A⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
          Pi.single (0 : Fin (m + 1)) 1 = α' • Pi.single (0 : Fin (m + 1)) 1 ∧
      β * β' = 1 ∧ α * α' = 1 := by
  have hm1 : 1 ≤ m := by omega
  have h0l : (0 : Fin (m + 1)) ≠ Fin.last m :=
    (AutPSL.last_ne_zero (m := m) hm1).symm
  have hh' : proj (m + 1) K b ∈ levi (K := K) hm := by rw [hb]; exact hh
  have hby : b * ty (K := K) hm = ty (K := K) hm * b :=
    commute_of_mem_centralizer (ty_mul_self hm) (by simpa [ty] using hh'.2)
  have hBicol : ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
      (((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 := by
    apply col_zero_of_commute_sl
    calc b⁻¹ * ty (K := K) hm
        = b⁻¹ * (ty (K := K) hm * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * ty (K := K) hm) * b⁻¹ := by rw [← hby]
      _ = ty (K := K) hm * b⁻¹ := by group
  have hBcol : (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 =
      ((b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 :=
    col_zero_of_commute_sl b h0l (by simpa [ty] using hby)
  have hAinv : A⁻¹ * SpecialLinearGroup.toGL (ty (K := K) hm) =
      SpecialLinearGroup.toGL (ty (K := K) hm) * A⁻¹ := by
    calc A⁻¹ * SpecialLinearGroup.toGL (ty (K := K) hm)
        = A⁻¹ * (SpecialLinearGroup.toGL (ty (K := K) hm) * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * SpecialLinearGroup.toGL (ty (K := K) hm)) * A⁻¹ := by rw [← hA₂]
      _ = SpecialLinearGroup.toGL (ty (K := K) hm) * A⁻¹ := by group
  have hAicol : ((A⁻¹ : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
      (((A⁻¹ : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 :=
    col_zero_of_commute_gl A⁻¹ h0l (by simpa [ty] using hAinv)
  have hAcol : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 =
      ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 :=
    col_zero_of_commute_gl A h0l (by simpa [ty] using hA₂)
  let β : K := (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  let β' : K := ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  let α : K := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  let α' : K := ((A⁻¹ : GL (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  refine ⟨β, β', α, α', hBcol, hBicol, hAcol, hAicol, ?_, ?_⟩
  · have hmat : ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) K =>
      M *ᵥ Pi.single (0 : Fin (m + 1)) 1) hmat
    rw [← Matrix.mulVec_mulVec, hBcol, Matrix.mulVec_smul, hBicol, smul_smul] at h
    have h0 := congrFun h 0
    simpa [β, β', Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm] using h0
  · have hmat : ((A⁻¹ : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) K =>
      M *ᵥ Pi.single (0 : Fin (m + 1)) 1) hmat
    rw [← Matrix.mulVec_mulVec, hAcol, Matrix.mulVec_smul, hAicol, smul_smul] at h
    have h0 := congrFun h 0
    simpa [α, α', Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm] using h0

private lemma matrix_eq_of_key [Finite K] {m : ℕ} (hm : 3 ≤ m)
    {A : GL (Fin (m + 1)) K}
    (hA₁ : A * SpecialLinearGroup.toGL (t0 (K := K) hm) =
      SpecialLinearGroup.toGL (t0 (K := K) hm) * A)
    (hA₂ : A * SpecialLinearGroup.toGL (ty (K := K) hm) =
      SpecialLinearGroup.toGL (ty (K := K) hm) * A)
    {b : SpecialLinearGroup (Fin (m + 1)) K} {h : projectiveSL (m + 1) K}
    (hb : proj (m + 1) K b = h) (hh : h ∈ levi (K := K) hm)
    {c : MulAut (projectiveSL (m + 1) K)}
    (hkey : ∀ k ∈ levi (K := K) hm, (conjAut (m + 1) K A * c) k ∈ levi (K := K) hm →
      h * (conjAut (m + 1) K A * c) k * h⁻¹ = k)
    {i j r s : Fin (m + 1)} (hij : i ≠ j) (hrs : r ≠ s)
    (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hil : i ≠ Fin.last m) (hjl : j ≠ Fin.last m)
    (hrl : r ≠ Fin.last m) (hsl : s ≠ Fin.last m)
    {σ : K ≃+* K}
    (hτ : ∀ t : K, c (proj (m + 1) K (SpecialLinearGroup.transvection hij t)) =
      proj (m + 1) K (SpecialLinearGroup.transvection hrs (σ t))) :
    ∀ t : K, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (((SpecialLinearGroup.transvection hrs (σ t) :
            SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          (((A⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
            ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K)))) =
      1 + Matrix.single i j t := by
  intro t
  have hm1 : 1 ≤ m := by omega
  have h0l : (0 : Fin (m + 1)) ≠ Fin.last m :=
    (AutPSL.last_ne_zero (m := m) hm1).symm
  have hh' : proj (m + 1) K b ∈ levi (K := K) hm := by rw [hb]; exact hh
  have hb0 : b * t0 (K := K) hm = t0 (K := K) hm * b :=
    commute_of_mem_centralizer (t0_mul_self hm) (by simpa [t0] using hh'.1)
  have hby : b * ty (K := K) hm = ty (K := K) hm * b :=
    commute_of_mem_centralizer (ty_mul_self hm) (by simpa [ty] using hh'.2)
  have hBicol : ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
      (((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 := by
    apply col_zero_of_commute_sl
    calc b⁻¹ * ty (K := K) hm
        = b⁻¹ * (ty (K := K) hm * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * ty (K := K) hm) * b⁻¹ := by rw [← hby]
      _ = ty (K := K) hm * b⁻¹ := by group
  have hBcol : (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 =
      ((b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 :=
    col_zero_of_commute_sl b h0l (by simpa [ty] using hby)
  have hAinv : A⁻¹ * SpecialLinearGroup.toGL (ty (K := K) hm) =
      SpecialLinearGroup.toGL (ty (K := K) hm) * A⁻¹ := by
    calc A⁻¹ * SpecialLinearGroup.toGL (ty (K := K) hm)
        = A⁻¹ * (SpecialLinearGroup.toGL (ty (K := K) hm) * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * SpecialLinearGroup.toGL (ty (K := K) hm)) * A⁻¹ := by rw [← hA₂]
      _ = SpecialLinearGroup.toGL (ty (K := K) hm) * A⁻¹ := by group
  have hAicol : ((A⁻¹ : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
      (((A⁻¹ : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 :=
    col_zero_of_commute_gl A⁻¹ h0l (by simpa [ty] using hAinv)
  have hAcol : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 =
      ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) •
        Pi.single (0 : Fin (m + 1)) 1 :=
    col_zero_of_commute_gl A h0l (by simpa [ty] using hA₂)
  let β : K := (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  let β' : K := ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  let α : K := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  let α' : K := ((A⁻¹ : GL (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)
  have hBcolβ : (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 = β • Pi.single (0 : Fin (m + 1)) 1 := hBcol
  have hBicolβ : ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
      β' • Pi.single (0 : Fin (m + 1)) 1 := hBicol
  have hAcolα : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 = α • Pi.single (0 : Fin (m + 1)) 1 := hAcol
  have hAicolα : ((A⁻¹ : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ Pi.single (0 : Fin (m + 1)) 1 =
      α' • Pi.single (0 : Fin (m + 1)) 1 := hAicol
  have hβ : β * β' = 1 := by
    have hmat : ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) K =>
      M *ᵥ Pi.single (0 : Fin (m + 1)) 1) hmat
    rw [← Matrix.mulVec_mulVec, hBcolβ, Matrix.mulVec_smul, hBicolβ, smul_smul] at h
    have h0 := congrFun h 0
    simpa [β, β', Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm] using h0
  have hα : α * α' = 1 := by
    have hmat : ((A⁻¹ : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) K =>
      M *ᵥ Pi.single (0 : Fin (m + 1)) 1) hmat
    rw [← Matrix.mulVec_mulVec, hAcolα, Matrix.mulVec_smul, hAicolα, smul_smul] at h
    have h0 := congrFun h 0
    simpa [α, α', Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm] using h0
  have hTm : (((SpecialLinearGroup.transvection hrs (σ t) :
      SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 = Pi.single (0 : Fin (m + 1)) 1 :=
    transvection_mulVec_e0 hrs hs0 (σ t)
  have hgcol : (((SpecialLinearGroup.transvection hij t :
      SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 = Pi.single (0 : Fin (m + 1)) 1 :=
    transvection_mulVec_e0 hij hj0 t
  have hτ0 : SpecialLinearGroup.transvection hrs (σ t) * t0 (K := K) hm =
      t0 (K := K) hm * SpecialLinearGroup.transvection hrs (σ t) := by
    simpa [t0] using AutPSL.transvection_comm hrs
      (AutPSL.last_ne_zero (m := m) hm1) hsl hr0.symm (σ t) 1
  have hτy : SpecialLinearGroup.transvection hrs (σ t) * ty (K := K) hm =
      ty (K := K) hm * SpecialLinearGroup.transvection hrs (σ t) := by
    simpa [ty] using AutPSL.transvection_comm hrs
      (AutPSL.last_ne_zero (m := m) hm1).symm hs0 hrl.symm (σ t) 1
  have hgt0 : SpecialLinearGroup.transvection hij t * t0 (K := K) hm =
      t0 (K := K) hm * SpecialLinearGroup.transvection hij t := by
    simpa [t0] using AutPSL.transvection_comm hij
      (AutPSL.last_ne_zero (m := m) hm1) hjl hi0.symm t 1
  have hgty : SpecialLinearGroup.transvection hij t * ty (K := K) hm =
      ty (K := K) hm * SpecialLinearGroup.transvection hij t := by
    simpa [ty] using AutPSL.transvection_comm hij
      (AutPSL.last_ne_zero (m := m) hm1).symm hj0 hil.symm t 1
  have hgt_mem : proj (m + 1) K (SpecialLinearGroup.transvection hij t) ∈
      levi (K := K) hm :=
    mem_levi_of_commute hm hgt0 hgty
  have hτ_mem : proj (m + 1) K (SpecialLinearGroup.transvection hrs (σ t)) ∈
      levi (K := K) hm :=
    mem_levi_of_commute hm hτ0 hτy
  have hcτ : (conjAut (m + 1) K A * c)
      (proj (m + 1) K (SpecialLinearGroup.transvection hij t)) =
      proj (m + 1) K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        (m + 1) K A (SpecialLinearGroup.transvection hrs (σ t))) := by
    rw [MulAut.mul_apply, hτ t, conjAut_proj]
  have hck_mem : (conjAut (m + 1) K A * c)
      (proj (m + 1) K (SpecialLinearGroup.transvection hij t)) ∈ levi (K := K) hm := by
    rw [hcτ]
    exact mem_levi_of_commute hm
      (slConj_commute_of_commute A (by simpa [t0] using hA₁) hτ0)
      (slConj_commute_of_commute A (by simpa [ty] using hA₂) hτy)
  have h := hkey (proj (m + 1) K (SpecialLinearGroup.transvection hij t))
    hgt_mem hck_mem
  rw [← hb, hcτ] at h
  rw [← map_mul, ← map_inv, ← map_mul] at h
  let X : SpecialLinearGroup (Fin (m + 1)) K :=
    b * CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      (m + 1) K A (SpecialLinearGroup.transvection hrs (σ t)) * b⁻¹
  have hXproj : proj (m + 1) K X =
      proj (m + 1) K (SpecialLinearGroup.transvection hij t) := by
    dsimp [X]; exact h
  have hXmat : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          (((SpecialLinearGroup.transvection hrs (σ t) :
              SpecialLinearGroup (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
            (((A⁻¹ : GL (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
              ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) K)))) := by
    dsimp [X]
    rw [coe_slConjugation]
    simp only [Matrix.mul_assoc]
  have hXcol : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 = Pi.single (0 : Fin (m + 1)) 1 := by
    rw [hXmat]
    simp only [← Matrix.mulVec_mulVec, hBicolβ, hAicolα, hTm, hAcolα, hBcolβ,
      Matrix.mulVec_smul, smul_smul]
    have hscalar : β' * α' * α * β = 1 := by
      calc β' * α' * α * β = (β' * β) * (α' * α) := by ring
        _ = 1 := by rw [mul_comm β' β, hβ, mul_comm α' α, hα, one_mul]
    rw [hscalar, one_smul]
  have hmatXg : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      ((SpecialLinearGroup.transvection hij t :
        SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :=
    matrix_eq_of_proj_eq_of_col hXproj hXcol hgcol
  rw [← hXmat, hmatXg, SpecialLinearGroup.transvection_coe]


private lemma key_to_gl {m : ℕ} (b : SpecialLinearGroup (Fin (m + 1)) K)
    (A : GL (Fin (m + 1)) K) {r s i j : Fin (m + 1)} (hrs : r ≠ s) {σ : K ≃+* K}
    (hmat : ∀ t : K, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (((SpecialLinearGroup.transvection hrs (σ t) :
            SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          (((A⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
            ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K)))) =
      1 + Matrix.single i j t) :
    ∀ t : K, (((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) * (1 + Matrix.single r s (σ t)) *
      ((((SpecialLinearGroup.toGL b * A)⁻¹ : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K))) = 1 + Matrix.single i j t := by
  intro t
  let D : GL (Fin (m + 1)) K := SpecialLinearGroup.toGL b * A
  have hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    dsimp [D]
  have hDi : ((D⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      ((A⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have hDinv : D⁻¹ = A⁻¹ * SpecialLinearGroup.toGL b⁻¹ := by
      dsimp [D]
      rw [_root_.mul_inv_rev, map_inv]
    rw [hDinv, Matrix.GeneralLinearGroup.coe_mul, SpecialLinearGroup.coe_GL_coe_matrix]
  show ((D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * (1 + Matrix.single r s (σ t)) *
      (((D⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) =
    1 + Matrix.single i j t
  rw [hD, hDi]
  rw [← hmat t]
  rw [SpecialLinearGroup.transvection_coe]
  simp only [Matrix.mul_assoc]



theorem eq_one_of_conj_levi [Finite K] {m : ℕ} (hm : 3 ≤ m)
    (hq : 4 ≤ m ∨ 4 ≤ Nat.card K) {c : MulAut (projectiveSL (m + 1) K)}
    (hc : c ∈ AutPSL.compl) {A : GL (Fin (m + 1)) K}
    (hA₁ : A * SpecialLinearGroup.toGL (AutPSL.rootInv (K := K) (m := m) (by omega)) =
      SpecialLinearGroup.toGL (AutPSL.rootInv (by omega)) * A)
    (hA₂ : A * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection
        (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K)) =
      SpecialLinearGroup.toGL (SpecialLinearGroup.transvection
        (AutPSL.last_ne_zero (m := m) (by omega)).symm 1) * A)
    {h : projectiveSL (m + 1) K}
    (hh : h ∈
      Subgroup.centralizer
        {proj (m + 1) K (AutPSL.rootInv (K := K) (m := m) (by omega))} ⊓
      Subgroup.centralizer {proj (m + 1) K (SpecialLinearGroup.transvection
        (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K))})
    (hkey : ∀ k ∈
      (Subgroup.centralizer
        {proj (m + 1) K (AutPSL.rootInv (K := K) (m := m) (by omega))} ⊓
      Subgroup.centralizer {proj (m + 1) K (SpecialLinearGroup.transvection
        (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K))}),
      (conjAut (m + 1) K A * c) k ∈
        (Subgroup.centralizer
          {proj (m + 1) K (AutPSL.rootInv (K := K) (m := m) (by omega))} ⊓
        Subgroup.centralizer {proj (m + 1) K (SpecialLinearGroup.transvection
          (AutPSL.last_ne_zero (m := m) (by omega)).symm (1 : K))}) →
      h * (conjAut (m + 1) K A * c) k * h⁻¹ = k) : c = 1 := by
  classical
  change h ∈ levi (K := K) hm at hh
  change ∀ k ∈ levi (K := K) hm, (conjAut (m + 1) K A * c) k ∈ levi (K := K) hm →
    h * (conjAut (m + 1) K A * c) k * h⁻¹ = k at hkey
  obtain ⟨b, hb⟩ := proj_surjective (m + 1) K h
  have hA₁' : A * SpecialLinearGroup.toGL (t0 (K := K) hm) =
      SpecialLinearGroup.toGL (t0 (K := K) hm) * A := by simpa [t0] using hA₁
  have hA₂' : A * SpecialLinearGroup.toGL (ty (K := K) hm) =
      SpecialLinearGroup.toGL (ty (K := K) hm) * A := by simpa [ty] using hA₂
  let i : Fin (m + 1) := ⟨1, by omega⟩
  let j : Fin (m + 1) := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hi0 : i ≠ 0 := by simp [i, Fin.ext_iff]
  have hj0 : j ≠ 0 := by simp [j, Fin.ext_iff]
  have hil : i ≠ Fin.last m := by
    simp only [i, ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  have hjl : j ≠ Fin.last m := by
    simp only [j, ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  have h0l : (0 : Fin (m + 1)) ≠ Fin.last m :=
    (AutPSL.last_ne_zero (m := m) (by omega)).symm
  obtain ⟨σ, hc | hc⟩ := mem_compl.mp hc
  · rw [hc] at hkey ⊢
    have hmat := matrix_eq_of_key hm hA₁' hA₂' hb hh hkey hij hij hi0 hj0 hi0 hj0
      hil hjl hil hjl (fun t => fieldAut_proj_transvection σ hij t)
    have hσ : σ = 1 := by
      apply field_eq_one_of_conj_single (SpecialLinearGroup.toGL b * A) hij
      intro t
      exact key_to_gl b A hij hmat t
    rw [hσ, map_one]
  · rw [hc] at hkey ⊢
    have hrs : Fin.rev j ≠ Fin.rev i := Fin.rev_injective.ne hij.symm
    have hr0 : Fin.rev j ≠ 0 := by
      intro h
      apply hjl
      have := congrArg Fin.rev h
      simpa using this
    have hs0 : Fin.rev i ≠ 0 := by
      intro h
      apply hil
      have := congrArg Fin.rev h
      simpa using this
    have hrl : Fin.rev j ≠ Fin.last m := by
      intro h
      apply hj0
      have := congrArg Fin.rev h
      simpa using this
    have hsl : Fin.rev i ≠ Fin.last m := by
      intro h
      apply hi0
      have := congrArg Fin.rev h
      simpa using this
    have hτ : ∀ t : K, (fieldAut (m + 1) K σ * AutPSL.graphAut (n := m + 1) (K := K))
        (proj (m + 1) K (SpecialLinearGroup.transvection hij t)) =
        proj (m + 1) K (SpecialLinearGroup.transvection hrs (σ t)) := by
      intro t
      rw [MulAut.mul_apply, AutPSL.graphAut_proj_transvection,
        AutPSL.fieldAut_proj_transvection]
    have hmat := matrix_eq_of_key hm hA₁' hA₂' hb hh hkey hij hrs hi0 hj0 hr0 hs0
      hil hjl hrl hsl hτ
    have hσ : σ = 1 := by
      apply field_eq_one_of_conj_single (SpecialLinearGroup.toGL b * A) hij
      intro t
      exact key_to_gl b A hrs hmat t
    rw [hσ, map_one, one_mul] at hkey ⊢
    exfalso
    by_cases hm4 : 4 ≤ m
    ·
      let i₂ : Fin (m + 1) := ⟨3, by omega⟩
      have hi₂j : i₂ ≠ j := by simp [i₂, j, Fin.ext_iff]
      have hi₂0 : i₂ ≠ 0 := by simp [i₂, Fin.ext_iff]
      have hi₂l : i₂ ≠ Fin.last m := by
        simp only [i₂, ne_eq, Fin.ext_iff, Fin.val_last]
        omega
      have hrs₂ : Fin.rev j ≠ Fin.rev i₂ := Fin.rev_injective.ne hi₂j.symm
      have hs0₂ : Fin.rev i₂ ≠ 0 := by
        intro h
        apply hi₂l
        have := congrArg Fin.rev h
        simpa using this
      have hsl₂ : Fin.rev i₂ ≠ Fin.last m := by
        intro h
        apply hi₂0
        have := congrArg Fin.rev h
        simpa using this
      have hτ₂ : ∀ t : K, AutPSL.graphAut (n := m + 1) (K := K)
          (proj (m + 1) K (SpecialLinearGroup.transvection hi₂j t)) =
          proj (m + 1) K (SpecialLinearGroup.transvection hrs₂
            ((1 : K ≃+* K) t)) := by
        intro t
        simpa using AutPSL.graphAut_proj_transvection hi₂j t
      have hmat₂ := matrix_eq_of_key hm hA₁' hA₂' hb hh hkey hi₂j hrs₂ hi₂0 hj0
        hr0 hs0₂ hi₂l hjl hrl hsl₂ hτ₂
      have hD : (((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          ((((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K))⁻¹ :
            GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
        rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one]
      have hD1 := key_to_gl b A hrs hmat 1
      rw [show σ 1 = 1 from by rw [hσ]; rfl] at hD1
      have hD2 := key_to_gl b A hrs₂ hmat₂ 1
      have hD2' : (((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          (1 + Matrix.single (Fin.rev j) (Fin.rev i₂) (1 : K)) *
          ((((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K))⁻¹ :
            GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K)) =
          1 + Matrix.single i₂ j 1 := by
        simpa using hD2
      have h1 : ((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i (Fin.rev j) *
          ((((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K))⁻¹ :
            GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.rev i) j = 1 := by
        have h := congrFun (congrFun hD1 i) j
        rw [entry_D_eq (SpecialLinearGroup.toGL b * A) hij hD] at h
        simpa [Matrix.one_apply, Matrix.single_apply, hij] using h
      have h2 : ((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i₂ (Fin.rev j) *
          ((((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K))⁻¹ :
            GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.rev i₂) j = 1 := by
        have h := congrFun (congrFun hD2' i₂) j
        rw [entry_D_eq (SpecialLinearGroup.toGL b * A) hi₂j hD] at h
        simpa [Matrix.one_apply, Matrix.single_apply, hi₂j] using h
      have hii₂ : i ≠ i₂ := by simp [i, i₂, Fin.ext_iff]
      have h3 : ((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i (Fin.rev j) *
          ((((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K))⁻¹ :
            GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.rev i₂) j = 0 := by
        have h := congrFun (congrFun hD2' i) j
        rw [entry_D_eq (SpecialLinearGroup.toGL b * A) (i := i) (j := j)
          (r := Fin.rev j) (s := Fin.rev i₂) (by simpa using hij) hD] at h
        have hR : (1 + Matrix.single i₂ j (1 : K)) i j = 0 := by
          simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hij, hii₂, hii₂.symm]
        rw [hR] at h
        simpa using h
      have hne : ((((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K))⁻¹ :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.rev i₂) j ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h2
        exact zero_ne_one h2
      have hzero : ((SpecialLinearGroup.toGL b * A : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i (Fin.rev j) = 0 := by
        rcases mul_eq_zero.mp h3 with h0 | h0
        · exact h0
        · exact absurd h0 hne
      rw [hzero, zero_mul] at h1
      exact zero_ne_one h1
    ·
      have hm3 : m = 3 := by omega
      have hK : 4 ≤ Nat.card K := by
        rcases hq with h | h
        · omega
        · exact h
      haveI : Fintype K := Fintype.ofFinite K
      haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
      have hcardu : 1 < Nat.card Kˣ := by
        rw [Nat.card_units]
        omega
      have hcardu' : 1 < Fintype.card Kˣ := by
        have := hcardu
        rwa [Nat.card_eq_fintype_card] at this
      obtain ⟨lam, hlam1⟩ := Fintype.exists_ne_of_one_lt_card hcardu' (1 : Kˣ)
      have hlam0 : (lam : K) ≠ 0 := Units.ne_zero lam
      have hvalne : (lam : K) ≠ 1 := fun h => hlam1 (Units.ext h)
      let f : Fin (m + 1) → K := cornerFun (K := K) hm (lam : K)
      have hf : ∏ x, f x = 1 := prod_cornerFun (K := K) hm hlam0
      let k : SpecialLinearGroup (Fin (m + 1)) K := diagElt f hf
      have hk_mem : proj (m + 1) K k ∈ levi (K := K) hm := by
        apply mem_levi_of_commute hm
        · have h := diagElt_commute_transvection f hf
            (i := Fin.last m) (j := 0) (AutPSL.last_ne_zero (m := m) (by omega))
            (by simp [f, cornerFun_zero, cornerFun_last])
          simpa [k, t0] using h
        · have h := diagElt_commute_transvection f hf
            (i := 0) (j := Fin.last m) (AutPSL.last_ne_zero (m := m) (by omega)).symm
            (by simp [f, cornerFun_zero, cornerFun_last])
          simpa [k, ty] using h
      let f' : Fin (m + 1) → K := fun x => (f (Fin.rev x))⁻¹
      have hf' : ∏ x, f' x = 1 := prod_rev_inv_eq_one hf
      let k' : SpecialLinearGroup (Fin (m + 1)) K := diagElt f' hf'
      have hγ : AutPSL.graphAut (n := m + 1) (K := K) (proj (m + 1) K k) =
          proj (m + 1) K k' := by
        simpa [k, k', f'] using graphAut_diagElt f hf
      have hk'_mem : proj (m + 1) K k' ∈ levi (K := K) hm := by
        apply mem_levi_of_commute hm
        · have h := diagElt_commute_transvection f' hf'
            (i := Fin.last m) (j := 0) (AutPSL.last_ne_zero (m := m) (by omega))
            (by simp [f', f, cornerFun_zero, cornerFun_last, Fin.rev_zero, Fin.rev_last])
          simpa [k', t0] using h
        · have h := diagElt_commute_transvection f' hf'
            (i := 0) (j := Fin.last m) (AutPSL.last_ne_zero (m := m) (by omega)).symm
            (by simp [f', f, cornerFun_zero, cornerFun_last, Fin.rev_zero, Fin.rev_last])
          simpa [k', ty] using h
      have hck_mem : (conjAut (m + 1) K A * AutPSL.graphAut (n := m + 1) (K := K))
          (proj (m + 1) K k) ∈
          levi (K := K) hm := by
        rw [MulAut.mul_apply, hγ, conjAut_proj]
        exact mem_levi_of_commute hm
          (slConj_commute_of_commute A hA₁'
            (commute_of_mem_centralizer (t0_mul_self hm) (by simpa [t0] using hk'_mem.1)))
          (slConj_commute_of_commute A hA₂'
            (commute_of_mem_centralizer (ty_mul_self hm) (by simpa [ty] using hk'_mem.2)))
      have hkeyk := hkey (proj (m + 1) K k) hk_mem hck_mem
      rw [← hb, MulAut.mul_apply, hγ, conjAut_proj] at hkeyk
      rw [← map_mul, ← map_inv, ← map_mul] at hkeyk
      let X : SpecialLinearGroup (Fin (m + 1)) K :=
        b * CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          (m + 1) K A k' * b⁻¹
      have hXproj : proj (m + 1) K X = proj (m + 1) K k := by
        dsimp [X]; exact hkeyk
      obtain ⟨β, β', α, α', hBcol, hBicol, hAcol, hAicol, hβ, hα⟩ :=
        col_actions_of_levi hm hA₂' hb hh
      have hγcol : (k' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
          Pi.single (0 : Fin (m + 1)) 1 = (lam : K)⁻¹ • Pi.single (0 : Fin (m + 1)) 1 := by
        rw [show (k' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
            Pi.single (0 : Fin (m + 1)) 1 = f' 0 • Pi.single (0 : Fin (m + 1)) 1 from
          diagElt_mulVec_e0 f' hf']
        congr 1
        simp [f', f, cornerFun_zero, cornerFun_last, Fin.rev_zero, Fin.rev_last]
      have hkcol : (k : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
          Pi.single (0 : Fin (m + 1)) 1 = (lam : K) • Pi.single (0 : Fin (m + 1)) 1 := by
        rw [show (k : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
            Pi.single (0 : Fin (m + 1)) 1 = f 0 • Pi.single (0 : Fin (m + 1)) 1 from
          diagElt_mulVec_e0 f hf]
        rfl
      have hXcol : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ
          Pi.single (0 : Fin (m + 1)) 1 = (lam : K)⁻¹ • Pi.single (0 : Fin (m + 1)) 1 := by
        have hXmat : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
            (b : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
              ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
                (((k' : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) *
                  (((A⁻¹ : GL (Fin (m + 1)) K) :
                    Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
                    ((b⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
                      Matrix (Fin (m + 1)) (Fin (m + 1)) K)))) := by
          dsimp [X]
          rw [coe_slConjugation]
          simp only [Matrix.mul_assoc]
        rw [hXmat]
        simp only [← Matrix.mulVec_mulVec, hBicol, hAicol, hγcol, hAcol, hBcol,
          Matrix.mulVec_smul, smul_smul]
        have hscalar : β' * α' * (lam : K)⁻¹ * α * β = (lam : K)⁻¹ := by
          calc β' * α' * (lam : K)⁻¹ * α * β
              = (β' * β) * (α' * α) * (lam : K)⁻¹ := by ring
            _ = (lam : K)⁻¹ := by
              rw [mul_comm β' β, hβ, mul_comm α' α, hα, one_mul, one_mul]
        rw [hscalar]
      obtain ⟨c, hc, hclam⟩ := scalar_of_proj_eq_of_col hXproj hXcol hkcol
      have hc_eq : (c : K) = (lam : K) * (lam : K) := by
        have h := congrArg (fun x : K => x * (lam : K)) hclam
        rw [mul_assoc, inv_mul_cancel₀ hlam0, mul_one] at h
        exact h
      have hc4 : (c : K) ^ 4 = 1 := by
        have h := congrArg (fun u : Kˣ => (u : K)) hc
        rw [hm3] at h
        simpa [Units.val_pow_eq_pow_val] using h
      have hlam8 : (lam : K) ^ 8 = 1 := by
        have h := hc4
        rw [hc_eq] at h
        calc (lam : K) ^ 8 = ((lam : K) * (lam : K)) ^ 4 := by ring
          _ = 1 := h
      have h4 : (lam : K) ^ 4 = 1 := by
        apply HypSixTypeA.eq_one_of_mul_self_eq_one
        rw [← pow_add]
        norm_num
        exact hlam8
      have h2 : (lam : K) ^ 2 = 1 := by
        apply HypSixTypeA.eq_one_of_mul_self_eq_one
        rw [← pow_add]
        norm_num
        exact h4
      have h1 : (lam : K) = 1 := by
        apply HypSixTypeA.eq_one_of_mul_self_eq_one
        simpa [pow_two] using h2
      exact hvalne h1



end CFSG.StandardType.KGPSL
