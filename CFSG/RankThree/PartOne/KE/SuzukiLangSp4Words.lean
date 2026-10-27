module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LieType.AlgebraicGroups.GLCoordPoints
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Matrices

variable {R S : Type} [CommRing R] [CommRing S]

@[expose] def transvMatR (v : Fin 4 → R) (t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1 + t * v 0 * v 3, t * v 0 * v 2, t * v 0 * v 1, t * v 0 * v 0;
    t * v 1 * v 3, 1 + t * v 1 * v 2, t * v 1 * v 1, t * v 1 * v 0;
    t * v 2 * v 3, t * v 2 * v 2, 1 + t * v 2 * v 1, t * v 2 * v 0;
    t * v 3 * v 3, t * v 3 * v 2, t * v 3 * v 1, 1 + t * v 3 * v 0]

theorem transvMatR_eq_transvMat {K : Type} [Field K] (v : Fin 4 → K) (t : K) :
    transvMatR v t = transvMat v t :=
  rfl

theorem transvMatR_eq_one_add (v : Fin 4 → R) (t : R) :
    transvMatR v t = 1 + Matrix.vecMulVec (t • v) (fun j => v (Fin.rev j)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMatR, Matrix.vecMulVec_apply] <;> ring

theorem transvMatR_map {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)
    (v : Fin 4 → R) (t : R) :
    (transvMatR v t).map f = transvMatR (fun i => f (v i)) (f t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMatR]

theorem transvMatR_zero (v : Fin 4 → R) : transvMatR v 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMatR]

theorem det_transvMatR [CharP R 2] (v : Fin 4 → R) (t : R) : (transvMatR v t).det = 1 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  rw [transvMatR_eq_one_add, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Fin.sum_univ_four]
  simp
  linear_combination (t * (v 0 * v 3 + v 1 * v 2)) * h2

theorem transvMatR_mul_self [CharP R 2] (v : Fin 4 → R) (t : R) :
    transvMatR v t * transvMatR v t = 1 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, transvMatR]
  all_goals first
    | ring1
    | linear_combination (t * v 0 * v 0 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 0 * v 1 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 0 * v 2 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 0 * v 3 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 1 * v 0 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 1 * v 1 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 1 * v 2 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 1 * v 3 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 2 * v 0 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 2 * v 1 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 2 * v 2 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 2 * v 3 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 3 * v 0 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 3 * v 1 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 3 * v 2 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2
    | linear_combination (t * v 3 * v 3 * (1 + t * (v 0 * v 3 + v 1 * v 2))) * h2

theorem map_ofFn_prod {F : Type*} [FunLike F R S] [RingHomClass F R S] (z : F) {n : ℕ}
    (f : Fin n → Matrix (Fin 4) (Fin 4) R) :
    (List.ofFn f).prod.map z = (List.ofFn fun i => (f i).map z).prod := by
  have h := map_list_prod ((z : R →+* S).mapMatrix (m := Fin 4)) (List.ofFn f)
  rw [List.map_ofFn] at h
  simpa [RingHom.mapMatrix_apply, Function.comp_def] using h

end Matrices

section Words

variable {k : Type} [Field k] [CharP k 2]

@[expose] def transvGL (p : (Fin 4 → k) × k) : GL (Fin 4) k :=
  GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
    (minorForm k) minorForm_isAlt p.1 p.2)

theorem glMat_transvGL (p : (Fin 4 → k) × k) : glMat (transvGL p) = transvMatR p.1 p.2 :=
  glMat_transvection p.1 p.2

theorem transvGL_mem (p : (Fin 4 → k) × k) : transvGL p ∈ antiSp k := by
  rw [antiSp_eq_closure]
  exact Subgroup.subset_closure ⟨p.1, p.2, rfl⟩

theorem transvGL_zero (v : Fin 4 → k) : transvGL (v, (0 : k)) = 1 := by
  show GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
    (minorForm k) minorForm_isAlt v 0) = 1
  rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_zero, map_one]

theorem transvGL_inv (p : (Fin 4 → k) × k) : (transvGL p)⁻¹ = transvGL p := by
  unfold transvGL
  rw [← map_inv, CFSG.ClassicalGroups.Alternating.symplecticTransvection_inv, CharTwo.neg_eq]

@[expose] def wordGL (w : List ((Fin 4 → k) × k)) : GL (Fin 4) k := (w.map transvGL).prod

theorem wordGL_append (w w' : List ((Fin 4 → k) × k)) :
    wordGL (w ++ w') = wordGL w * wordGL w' := by
  simp [wordGL]

theorem glMat_wordGL (w : List ((Fin 4 → k) × k)) :
    glMat (wordGL w) = (w.map fun p => transvMatR p.1 p.2).prod := by
  have h := map_list_prod (Units.coeHom (Matrix (Fin 4) (Fin 4) k)) (w.map transvGL)
  refine h.trans ?_
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => glMat_transvGL p

theorem wordGL_mem (w : List ((Fin 4 → k) × k)) : wordGL w ∈ antiSp k :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
    exact transvGL_mem p

theorem wordGL_ofFn_eq_one {m : ℕ} (c : Fin m → (Fin 4 → k) × k) (hc : ∀ i, (c i).2 = 0) :
    wordGL (List.ofFn c) = 1 := by
  unfold wordGL
  rw [List.map_ofFn]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  have h := hc i
  show transvGL (c i) = 1
  generalize c i = p at h ⊢
  obtain ⟨v, t⟩ := p
  have ht : t = 0 := h
  subst ht
  exact transvGL_zero v

theorem wordGL_inv (w : List ((Fin 4 → k) × k)) : (wordGL w)⁻¹ = wordGL w.reverse := by
  unfold wordGL
  have h : (w.map transvGL).map (fun x => x⁻¹) = w.map transvGL := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => transvGL_inv p
  rw [List.prod_inv_reverse, h, List.map_reverse]

theorem exists_wordGL_eq {g : GL (Fin 4) k} (hg : g ∈ antiSp k) :
    ∃ w : List ((Fin 4 → k) × k), wordGL w = g := by
  rw [antiSp_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, t, rfl⟩ := hx
    exact ⟨[(v, t)], by simp [wordGL, transvGL]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    exact ⟨w ++ w', wordGL_append w w'⟩
  | inv x _ hx =>
    obtain ⟨w, rfl⟩ := hx
    exact ⟨w.reverse, (wordGL_inv w).symm⟩

end Words

section LiftOne

variable {k : Type} [Field k] {D : Type} [CommRing D] [Algebra k D]

@[expose] def glLiftOne (M : Matrix (Fin 4) (Fin 4) D) (h : M.det = 1) :
    GLCoord k (Fin 4) →ₐ[k] D :=
  GLCoord.lift k (Fin 4) M 1 (by rw [h, one_mul])

theorem glLiftOne_glEntry (M : Matrix (Fin 4) (Fin 4) D) (h : M.det = 1) (i j : Fin 4) :
    glLiftOne (k := k) M h (glEntry k (Fin 4) i j) = M i j :=
  GLCoord.lift_glEntry k (Fin 4) _ _ _ i j

theorem glMat_glPointEquiv_symm_apply (φ : WithConv (GLCoord k (Fin 4) →ₐ[k] k)) (i j : Fin 4) :
    glMat (glPointEquiv.symm φ : GL (Fin 4) k) i j = φ.ofConv (glEntry k (Fin 4) i j) :=
  rfl

theorem glMat_glPointEquiv_symm_comp_glLiftOne (M : Matrix (Fin 4) (Fin 4) D)
    (h : M.det = 1) (z : D →ₐ[k] k) :
    glMat (glPointEquiv.symm (WithConv.toConv (z.comp (glLiftOne M h))) : GL (Fin 4) k) =
      M.map z := by
  ext i j
  rw [glMat_glPointEquiv_symm_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    glLiftOne_glEntry, Matrix.map_apply]

end LiftOne

section Generic

variable (k : Type) [Field k]

abbrev TransvPoly (n : ℕ) : Type := MvPolynomial (Fin n × (Fin 4 ⊕ Unit)) k

@[expose] def genProd (n : ℕ) : Matrix (Fin 4) (Fin 4) (TransvPoly k n) :=
  (List.ofFn fun i : Fin n => transvMatR
    (fun j => (MvPolynomial.X (i, Sum.inl j) : TransvPoly k n))
    (MvPolynomial.X (i, Sum.inr ()))).prod

theorem det_genProd [CharP k 2] (n : ℕ) : (genProd k n).det = 1 := by
  have h := map_list_prod (Matrix.detMonoidHom (n := Fin 4) (R := TransvPoly k n))
    (List.ofFn fun i : Fin n => transvMatR
      (fun j => (MvPolynomial.X (i, Sum.inl j) : TransvPoly k n))
      (MvPolynomial.X (i, Sum.inr ())))
  rw [List.map_ofFn] at h
  rw [genProd]
  refine h.trans (List.prod_eq_one fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact det_transvMatR _ _

@[expose] def transvCo [CharP k 2] (n : ℕ) : GLCoord k (Fin 4) →ₐ[k] TransvPoly k n :=
  glLiftOne (genProd k n) (det_genProd k n)

end Generic

section Points

variable {k : Type} [Field k] [CharP k 2]

@[expose] def pointWord {n : ℕ} (z : TransvPoly k n →ₐ[k] k) : Fin n → (Fin 4 → k) × k :=
  fun i => (fun j => z (MvPolynomial.X (i, Sum.inl j)), z (MvPolynomial.X (i, Sum.inr ())))

omit [CharP k 2] in
theorem exists_pointWord_eq {n : ℕ} (c : Fin n → (Fin 4 → k) × k) :
    ∃ z : TransvPoly k n →ₐ[k] k, pointWord z = c := by
  refine ⟨MvPolynomial.aeval fun p => Sum.elim (fun j => (c p.1).1 j) (fun _ => (c p.1).2) p.2,
    ?_⟩
  funext i
  refine Prod.ext (funext fun j => ?_) ?_
  · simp [pointWord]
  · simp [pointWord]

theorem glPointEquiv_symm_comp_transvCo {n : ℕ} (z : TransvPoly k n →ₐ[k] k) :
    glPointEquiv.symm (WithConv.toConv (z.comp (transvCo k n))) =
      wordGL (List.ofFn (pointWord z)) := by
  refine Units.ext ?_
  refine ((glMat_glPointEquiv_symm_comp_glLiftOne (genProd k n) (det_genProd k n) z).trans
    ?_).trans (glMat_wordGL _).symm
  rw [genProd, map_ofFn_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  rw [Function.comp_apply, transvMatR_map]
  rfl

end Points

end CFSG.RankThree.PartOne.KE
