module

public import CFSG.Monster.Griess.Space
public import CFSG.Monster.Jordan

public noncomputable section

namespace CFSG.Monster.Parity

open CFSG.Monster CFSG.Monster.Griess Matrix Module

theorem eq_or_eq_neg_of_vecMulVec_eq {K n : Type*} [Field K] {v w : n → K}
    (h : vecMulVec v v = vecMulVec w w) : w = v ∨ w = -v := by
  by_cases hv : v = 0
  · subst hv
    left
    funext j
    have hj := congrFun (congrFun h j) j
    simp only [vecMulVec_apply, Pi.zero_apply, mul_zero] at hj
    exact mul_self_eq_zero.1 hj.symm
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (funext hc)
    have hii := congrFun (congrFun h i) i
    simp only [vecMulVec_apply] at hii
    have hw : (w i - v i) * (w i + v i) = 0 := by linear_combination -hii
    have hrow : ∀ j, v i * v j = w i * w j := fun j => by
      have := congrFun (congrFun h i) j
      simpa only [vecMulVec_apply] using this
    rcases mul_eq_zero.1 hw with h1 | h1
    · left
      have hwi : w i = v i := sub_eq_zero.1 h1
      funext j
      have := hrow j
      rw [hwi] at this
      exact (mul_left_cancel₀ hi this).symm
    · right
      have hwi : w i = -v i := eq_neg_of_add_eq_zero_left h1
      funext j
      have := hrow j
      rw [hwi, neg_mul] at this
      have e : v i * (-w j) = v i * v j := by rw [mul_neg, ← this]
      rw [Pi.neg_apply, ← mul_left_cancel₀ hi e, neg_neg]

@[expose] def jordanQ (A B : symMat) : symMat :=
  ⟨(1 / 2 : ℚ) • ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ) +
      (B : Matrix (Fin 24) (Fin 24) ℚ) * (A : Matrix (Fin 24) (Fin 24) ℚ)), by
    have hA : (A : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = A := A.2
    have hB : (B : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = B := B.2
    rw [mem_symMat, transpose_smul, transpose_add, transpose_mul, transpose_mul, hA, hB,
      add_comm]⟩

theorem coe_jordanQ (A B : symMat) :
    (jordanQ A B : Matrix (Fin 24) (Fin 24) ℚ) =
      (1 / 2 : ℚ) • ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ) +
        (B : Matrix (Fin 24) (Fin 24) ℚ) * (A : Matrix (Fin 24) (Fin 24) ℚ)) := rfl

abbrev castR : Matrix (Fin 24) (Fin 24) ℚ →+* Matrix (Fin 24) (Fin 24) ℝ :=
  (Rat.castHom ℝ).mapMatrix

theorem castR_apply (M : Matrix (Fin 24) (Fin 24) ℚ) (i j : Fin 24) :
    castR M i j = (M i j : ℝ) := rfl

theorem castR_transpose (M : Matrix (Fin 24) (Fin 24) ℚ) : castR Mᵀ = (castR M)ᵀ := rfl

theorem castR_smul (q : ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    castR (q • M) = (q : ℝ) • castR M := by
  ext i j
  simp [castR_apply]

theorem castR_injective : Function.Injective castR := fun M N h => by
  ext i j
  exact Rat.cast_injective (congrFun (congrFun h i) j)

theorem trace_castR (M : Matrix (Fin 24) (Fin 24) ℚ) : trace (castR M) = ((trace M : ℚ) : ℝ) := by
  simp only [trace, diag, castR_apply, Rat.cast_sum]

@[expose] def castSym (A : symMat) : Jordan.symMat (Fin 24) :=
  ⟨castR A, by
    have hA : (A : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = A := A.2
    rw [Jordan.mem_symMat, ← castR_transpose, hA]⟩

theorem coe_castSym (A : symMat) : (castSym A : Matrix (Fin 24) (Fin 24) ℝ) = castR A := rfl

theorem castSym_add (A B : symMat) : castSym (A + B) = castSym A + castSym B :=
  Subtype.ext (map_add castR _ _)

theorem castSym_smul (q : ℚ) (A : symMat) : castSym (q • A) = (q : ℝ) • castSym A :=
  Subtype.ext (castR_smul q _)

theorem castSym_zero : castSym 0 = 0 := Subtype.ext (map_zero castR)

@[expose] def castSymHom : symMat →+ Jordan.symMat (Fin 24) where
  toFun := castSym
  map_zero' := castSym_zero
  map_add' := castSym_add

theorem castSym_sum {ι : Type*} (s : Finset ι) (A : ι → symMat) :
    castSym (∑ i ∈ s, A i) = ∑ i ∈ s, castSym (A i) :=
  map_sum castSymHom A s

theorem castSym_jordanQ (A B : symMat) :
    castSym (jordanQ A B) = Jordan.jordanMul (castSym A) (castSym B) := by
  refine Subtype.ext ?_
  rw [coe_castSym, coe_jordanQ, Jordan.coe_jordanMul, coe_castSym, coe_castSym, castR_smul,
    map_add, map_mul, map_mul]
  norm_num

theorem trace_castSym_mul (A B : symMat) :
    trace ((castSym A : Matrix (Fin 24) (Fin 24) ℝ) * (castSym B : Matrix (Fin 24) (Fin 24) ℝ)) =
      ((trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) : ℚ) : ℝ) := by
  rw [coe_castSym, coe_castSym, ← map_mul, trace_castR]

@[expose] def symEntryR (A : Jordan.symMat (Fin 24)) : PairIdx → ℝ :=
  Sym2.lift ⟨fun i j => (A : Matrix (Fin 24) (Fin 24) ℝ) i j,
    fun i j => (congrFun (congrFun (Jordan.transpose_coe A) i) j).symm⟩

theorem symEntryR_mk (A : Jordan.symMat (Fin 24)) (i j : Fin 24) :
    symEntryR A s(i, j) = (A : Matrix (Fin 24) (Fin 24) ℝ) i j := Sym2.lift_mk _ _ _

@[expose] def symCoordR : Jordan.symMat (Fin 24) ≃ₗ[ℝ] (PairIdx → ℝ) where
  toFun := symEntryR
  map_add' A B := by
    funext z
    induction z using Sym2.ind with | h i j => simp [symEntryR_mk]
  map_smul' c A := by
    funext z
    induction z using Sym2.ind with | h i j => simp [symEntryR_mk]
  invFun f := ⟨Matrix.of fun i j => f s(i, j), by
      rw [Jordan.mem_symMat]
      ext i j
      simp only [transpose_apply, of_apply, Sym2.eq_swap]⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp only [of_apply, symEntryR_mk]
  right_inv f := by
    funext z
    induction z using Sym2.ind with | h i j => simp only [symEntryR_mk, of_apply]

@[expose] def basisAR : Basis PairIdx ℝ (Jordan.symMat (Fin 24)) := Basis.ofEquivFun symCoordR

theorem basisAR_apply (z : PairIdx) (k l : Fin 24) :
    (basisAR z : Matrix (Fin 24) (Fin 24) ℝ) k l = if s(k, l) = z then 1 else 0 := by
  rw [basisAR, Basis.coe_ofEquivFun]
  change (Pi.single z 1 : PairIdx → ℝ) s(k, l) = _
  rw [Pi.single_apply]

theorem castSym_basisA (z : PairIdx) : castSym (basisA z) = basisAR z := by
  refine Subtype.ext ?_
  ext k l
  rw [coe_castSym, castR_apply, basisA_apply, basisAR_apply]
  split_ifs <;> simp

theorem castSym_eq_sum (A : symMat) :
    castSym A = ∑ z, ((basisA.repr A z : ℚ) : ℝ) • basisAR z := by
  conv_lhs => rw [← basisA.sum_repr A]
  rw [castSym_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [castSym_smul, castSym_basisA]

@[expose] def extR (f : symMat →ₗ[ℚ] symMat) :
    Jordan.symMat (Fin 24) →ₗ[ℝ] Jordan.symMat (Fin 24) :=
  basisAR.constr ℝ fun z => castSym (f (basisA z))

theorem extR_basisAR (f : symMat →ₗ[ℚ] symMat) (z : PairIdx) :
    extR f (basisAR z) = castSym (f (basisA z)) :=
  basisAR.constr_basis ℝ _ z

theorem extR_castSym (f : symMat →ₗ[ℚ] symMat) (A : symMat) :
    extR f (castSym A) = castSym (f A) := by
  rw [castSym_eq_sum, map_sum]
  simp only [map_smul, extR_basisAR]
  conv_rhs => rw [← basisA.sum_repr A]
  rw [map_sum, castSym_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_smul, castSym_smul]

@[expose] def jordanBil :
    Jordan.symMat (Fin 24) →ₗ[ℝ] Jordan.symMat (Fin 24) →ₗ[ℝ] Jordan.symMat (Fin 24) :=
  LinearMap.mk₂ ℝ Jordan.jordanMul
    (fun A A' B => Subtype.ext (by
      simp only [Jordan.coe_jordanMul, Submodule.coe_add, Matrix.add_mul, Matrix.mul_add]
      module))
    (fun c A B => Subtype.ext (by
      simp only [Jordan.coe_jordanMul, Submodule.coe_smul, Matrix.smul_mul, Matrix.mul_smul]
      module))
    (fun A B B' => Subtype.ext (by
      simp only [Jordan.coe_jordanMul, Submodule.coe_add, Matrix.add_mul, Matrix.mul_add]
      module))
    (fun c A B => Subtype.ext (by
      simp only [Jordan.coe_jordanMul, Submodule.coe_smul, Matrix.smul_mul, Matrix.mul_smul]
      module))

theorem jordanBil_apply (A B : Jordan.symMat (Fin 24)) :
    jordanBil A B = Jordan.jordanMul A B := rfl

@[expose] def traceBil : Jordan.symMat (Fin 24) →ₗ[ℝ] Jordan.symMat (Fin 24) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun A B => trace ((A : Matrix (Fin 24) (Fin 24) ℝ) * (B : Matrix (Fin 24) (Fin 24) ℝ)))
    (fun A A' B => by simp only [Submodule.coe_add, Matrix.add_mul, trace_add])
    (fun c A B => by simp only [Submodule.coe_smul, Matrix.smul_mul, trace_smul, smul_eq_mul])
    (fun A B B' => by simp only [Submodule.coe_add, Matrix.mul_add, trace_add])
    (fun c A B => by simp only [Submodule.coe_smul, Matrix.mul_smul, trace_smul, smul_eq_mul])

theorem traceBil_apply (A B : Jordan.symMat (Fin 24)) :
    traceBil A B = trace ((A : Matrix (Fin 24) (Fin 24) ℝ) * (B : Matrix (Fin 24) (Fin 24) ℝ)) :=
  rfl

theorem extR_jordanMul (f : symMat →ₗ[ℚ] symMat)
    (hJ : ∀ A B, f (jordanQ A B) = jordanQ (f A) (f B)) (A B : Jordan.symMat (Fin 24)) :
    extR f (Jordan.jordanMul A B) = Jordan.jordanMul (extR f A) (extR f B) := by
  have h : jordanBil.compr₂ (extR f) = jordanBil.compl₁₂ (extR f) (extR f) := by
    refine LinearMap.ext_basis basisAR basisAR fun z z' => ?_
    rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, jordanBil_apply, jordanBil_apply,
      ← castSym_basisA, ← castSym_basisA, ← castSym_jordanQ, extR_castSym, hJ, extR_castSym,
      extR_castSym, castSym_jordanQ]
  exact LinearMap.congr_fun₂ h A B

theorem extR_trace (f : symMat →ₗ[ℚ] symMat)
    (hT : ∀ A B, trace ((f A : Matrix (Fin 24) (Fin 24) ℚ) * (f B : Matrix (Fin 24) (Fin 24) ℚ)) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)))
    (A B : Jordan.symMat (Fin 24)) :
    trace ((extR f A : Matrix (Fin 24) (Fin 24) ℝ) * (extR f B : Matrix (Fin 24) (Fin 24) ℝ)) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℝ) * (B : Matrix (Fin 24) (Fin 24) ℝ)) := by
  have h : traceBil.compl₁₂ (extR f) (extR f) = traceBil := by
    refine LinearMap.ext_basis basisAR basisAR fun z z' => ?_
    rw [LinearMap.compl₁₂_apply, traceBil_apply, traceBil_apply, ← castSym_basisA,
      ← castSym_basisA, extR_castSym, extR_castSym, trace_castSym_mul, trace_castSym_mul, hT]
  exact LinearMap.congr_fun₂ h A B

theorem exists_real_orthogonal_conj (f : symMat →ₗ[ℚ] symMat)
    (hJ : ∀ A B, f (jordanQ A B) = jordanQ (f A) (f B))
    (hT : ∀ A B, trace ((f A : Matrix (Fin 24) (Fin 24) ℚ) * (f B : Matrix (Fin 24) (Fin 24) ℚ)) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ))) :
    ∃ G ∈ Matrix.orthogonalGroup (Fin 24) ℝ,
      ∀ A : symMat, castR (f A) = Gᵀ * castR A * G := by
  obtain ⟨G, hG, hconj⟩ :=
    Jordan.exists_orthogonal_eq_conj (extR f) (extR_jordanMul f hJ) (extR_trace f hT)
  refine ⟨G, hG, fun A => ?_⟩
  rw [← coe_castSym, ← extR_castSym, hconj, coe_castSym]

private def diagQ (i : Fin 24) : symMat := ⟨single i i 1, transpose_single i i 1⟩

private def pairQ (i j : Fin 24) : symMat :=
  ⟨single i j 1 + single j i 1, by
    rw [mem_symMat, transpose_add, transpose_single, transpose_single, add_comm]⟩

theorem eq_or_eq_neg_of_conj_eq_rat {g g' : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (hg' : g' * g'ᵀ = 1)
    (h : ∀ A : symMat, gᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * g =
      g'ᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * g') :
    g' = g ∨ g' = -g := by
  have hgtg : gᵀ * g = 1 := mul_eq_one_comm.1 hg
  obtain ⟨k, hk⟩ : ∃ k : Matrix (Fin 24) (Fin 24) ℚ, k = g' * gᵀ := ⟨_, rfl⟩
  have hkk : k * kᵀ = 1 := by
    rw [hk, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hgtg,
      Matrix.one_mul, hg']
  have hconj : ∀ A : symMat, kᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * k = A := by
    intro A
    rw [hk, transpose_mul, transpose_transpose]
    calc g * g'ᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * (g' * gᵀ) = g * (g'ᵀ * A * g') * gᵀ := by
          simp only [Matrix.mul_assoc]
      _ = g * (gᵀ * A * g) * gᵀ := by rw [h A]
      _ = A := by
          simp only [Matrix.mul_assoc, hg, Matrix.mul_one]
          rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
  have hcomm : ∀ A : symMat, Commute (A : Matrix (Fin 24) (Fin 24) ℚ) k := by
    intro A
    change (A : Matrix (Fin 24) (Fin 24) ℚ) * k = k * A
    calc (A : Matrix (Fin 24) (Fin 24) ℚ) * k = k * kᵀ * A * k := by rw [hkk, Matrix.one_mul]
      _ = k * (kᵀ * A * k) := by simp only [Matrix.mul_assoc]
      _ = k * A := by rw [hconj A]
  have hsingle : Pairwise fun x y => Commute (single x y (1 : ℚ)) k := by
    intro x y hxy
    have e : single x y (1 : ℚ) = single x x 1 * (single x y 1 + single y x 1) := by
      simp [Matrix.mul_add, hxy]
    rw [e]
    exact (hcomm (diagQ x)).mul_left (hcomm (pairQ x y))
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_single hsingle
  have hc2 : c * c = 1 := by
    rw [← hc, scalar_apply, diagonal_transpose, diagonal_mul_diagonal] at hkk
    simpa using congrFun (congrFun hkk 0) 0
  have hg'k : g' = k * g := by rw [hk, Matrix.mul_assoc, hgtg, Matrix.mul_one]
  rcases mul_self_eq_one_iff.1 hc2 with rfl | rfl
  · left
    rw [hg'k, ← hc, map_one, Matrix.one_mul]
  · right
    rw [hg'k, ← hc, map_neg, map_one, Matrix.neg_mul, Matrix.one_mul]

end CFSG.Monster.Parity
