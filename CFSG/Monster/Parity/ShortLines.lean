module

public import CFSG.Monster.Parity.TraceSplitting
public import CFSG.Monster.Parity.RealExtension

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Parity

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Griess Matrix Module

theorem gmul_inA_inA (A B : symMat) : gmul (inA A) (inA B) = inA ((4 : ℚ) • jordanQ A B) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun c => ?_) ?_)
  · change gmulA (inA A) (inA B) = (4 : ℚ) • ((1 / 2 : ℚ) •
      ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ) +
        (B : Matrix (Fin 24) (Fin 24) ℚ) * (A : Matrix (Fin 24) (Fin 24) ℚ)))
    simp only [gmulA, Am_inA, xs_inA, Nm_inA, Pi.zero_apply, mul_zero, zero_smul,
      Finset.sum_const_zero, smul_zero, add_zero, transpose_zero, Matrix.zero_mul, trace_zero,
      zero_div, smul_smul]
    norm_num
  · change gmulX (inA A) (inA B) c = 0
    simp [gmulX, qf_zero]
  · change gmulWHalf (inA A) (inA B) + gmulWHalf (inA B) (inA A) = 0
    simp [gmulWHalf]

theorem gmul_inA_inX (A : symMat) (x : SpaceX) :
    gmul (inA A) (inX x) = inX (fun c => x c * qf c A / 8) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun c => ?_) ?_)
  · change gmulA (inA A) (inX x) = 0
    simp [gmulA]
  · change gmulX (inA A) (inX x) c = x c * qf c A / 8
    simp [gmulX, qf_zero]
  · change gmulWHalf (inA A) (inX x) + gmulWHalf (inX x) (inA A) = 0
    simp [gmulWHalf]

theorem bform_inA_inA (A B : symMat) :
    bform (inA A) (inA B) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) := by
  rw [bform_apply]
  simp

theorem bform_inX_inX (x y : SpaceX) : bform (inX x) (inX y) = x ⬝ᵥ y := by
  rw [bform_apply]
  simp [dotProduct]

theorem eq_zero_of_trace_mul_self {M : Matrix (Fin 24) (Fin 24) ℚ} (hM : Mᵀ = M)
    (h : trace (M * M) = 0) : M = 0 := by
  have hs : trace (M * M) = ∑ i, ∑ j, M i j ^ 2 := by
    simp only [trace, diag, mul_apply, sq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← transpose_apply M i j, hM]
  rw [hs] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (M i j)).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (M i j)).1 h1 j
    (Finset.mem_univ _)
  simpa using h2

theorem eq_of_forall_trace_mul_eq {M M' : symMat}
    (h : ∀ B : symMat, trace ((M : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) =
      trace ((M' : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ))) : M = M' := by
  have hD := h (M - M')
  have h0 : ((M - M' : symMat) : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
    refine eq_zero_of_trace_mul_self (M - M').2 ?_
    rw [Submodule.coe_sub] at hD ⊢
    rw [Matrix.sub_mul, trace_sub, hD, sub_self]
  exact sub_eq_zero.1 (Subtype.ext h0)

@[expose] def UmatS (c : ShortIdx) : symMat := ⟨Umat c, Umat_symm c⟩

theorem coe_UmatS (c : ShortIdx) : (UmatS c : Matrix (Fin 24) (Fin 24) ℚ) = Umat c := rfl

theorem eq_of_forall_qf_eq {d d' : ShortIdx} (h : ∀ B : symMat, qf d B = qf d' B) : d = d' := by
  have hU : UmatS d = UmatS d' := eq_of_forall_trace_mul_eq fun B => by
    rw [coe_UmatS, coe_UmatS, trace_Umat_mul, trace_Umat_mul, h]
  have hv : vecMulVec (uQ d) (uQ d) = vecMulVec (uQ d') (uQ d') := congrArg Subtype.val hU
  have hcl : classOf (uvec d) = classOf (uvec d') := by
    refine (classOf_eq_iff (uvec_mem d) (uvec_mem d')).2 ?_
    rcases eq_or_eq_neg_of_vecMulVec_eq hv with h1 | h1
    · exact Or.inl (funext fun i => Int.cast_injective (α := ℚ) (congrFun h1 i))
    · refine Or.inr (funext fun i => Int.cast_injective (α := ℚ) ?_)
      rw [Pi.neg_apply, Int.cast_neg]
      exact congrFun h1 i
  rw [classOf_uvec, classOf_uvec] at hcl
  exact Subtype.ext (SpinLattice.phi0_injective hcl)

@[expose] def resA (f : SpaceB ≃ₗ[ℚ] SpaceB) : symMat →ₗ[ℚ] symMat :=
  LinearMap.fst ℚ symMat (SpaceX × SpaceW) ∘ₗ f.toLinearMap ∘ₗ
    LinearMap.inl ℚ symMat (SpaceX × SpaceW)

theorem resA_apply (f : SpaceB ≃ₗ[ℚ] SpaceB) (A : symMat) : resA f A = (f (inA A)).1 := rfl

@[expose] def resX (f : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceX →ₗ[ℚ] SpaceX :=
  (LinearMap.fst ℚ SpaceX SpaceW ∘ₗ LinearMap.snd ℚ symMat (SpaceX × SpaceW)) ∘ₗ f.toLinearMap ∘ₗ
    (LinearMap.inr ℚ symMat (SpaceX × SpaceW) ∘ₗ LinearMap.inl ℚ SpaceX SpaceW)

theorem resX_apply (f : SpaceB ≃ₗ[ℚ] SpaceB) (x : SpaceX) : resX f x = (f (inX x)).2.1 := rfl

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

theorem apply_inA (hf : IsParityAut f) (A : symMat) : f (inA A) = inA (resA f A) := by
  obtain ⟨h1, h2⟩ := mem_subA.1 (hf.map_subA (u := inA A) ⟨rfl, rfl⟩)
  exact Prod.ext rfl (Prod.ext h1 h2)

theorem apply_inX (hf : IsParityAut f) (x : SpaceX) : f (inX x) = inX (resX f x) := by
  obtain ⟨h1, h2⟩ := mem_subX.1 (hf.map_subX (u := inX x) ⟨rfl, rfl⟩)
  exact Prod.ext h1 (Prod.ext rfl h2)

theorem resA_resA_symm (hf : IsParityAut f) (B : symMat) : resA f (resA f.symm B) = B := by
  rw [resA_apply, ← hf.symm.apply_inA, LinearEquiv.apply_symm_apply]

theorem resA_surjective (hf : IsParityAut f) : Function.Surjective (resA f) :=
  fun B => ⟨resA f.symm B, hf.resA_resA_symm B⟩

theorem resX_injective (hf : IsParityAut f) : Function.Injective (resX f) := fun x y h => by
  have h' : f (inX x) = f (inX y) := by rw [hf.apply_inX x, hf.apply_inX y, h]
  exact congrArg (fun w : SpaceB => w.2.1) (f.injective h')

theorem resA_jordanQ (hf : IsParityAut f) (A B : symMat) :
    resA f (jordanQ A B) = jordanQ (resA f A) (resA f B) := by
  have h := hf.map_gmul (inA A) (inA B)
  rw [gmul_inA_inA A B, hf.apply_inA ((4 : ℚ) • jordanQ A B), hf.apply_inA A, hf.apply_inA B,
    gmul_inA_inA (resA f A) (resA f B)] at h
  have h1 : resA f ((4 : ℚ) • jordanQ A B) = (4 : ℚ) • jordanQ (resA f A) (resA f B) :=
    congrArg Prod.fst h
  rw [map_smul] at h1
  exact smul_right_injective _ (by norm_num : (4 : ℚ) ≠ 0) h1

theorem resA_trace (hf : IsParityAut f) (A B : symMat) :
    trace ((resA f A : Matrix (Fin 24) (Fin 24) ℚ) * (resA f B : Matrix (Fin 24) (Fin 24) ℚ)) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) := by
  have h := hf.map_bform (inA A) (inA B)
  rwa [hf.apply_inA A, hf.apply_inA B, bform_inA_inA, bform_inA_inA] at h

theorem resX_eigen (hf : IsParityAut f) (A : symMat) (x : SpaceX) :
    resX f (fun c => x c * qf c A / 8) = fun c => resX f x c * qf c (resA f A) / 8 := by
  have h := hf.map_gmul (inA A) (inX x)
  rw [gmul_inA_inX A x, hf.apply_inX (fun c => x c * qf c A / 8), hf.apply_inA A,
    hf.apply_inX x, gmul_inA_inX (resA f A) (resX f x)] at h
  exact congrArg (fun w : SpaceB => w.2.1) h

theorem resX_single_apply (hf : IsParityAut f) (c d : ShortIdx) (A : symMat) :
    resX f (Pi.single c 1) d * (qf c A - qf d (resA f A)) = 0 := by
  have h := congrFun (hf.resX_eigen A (Pi.single c 1)) d
  have e : (fun e => (Pi.single c 1 : SpaceX) e * qf e A / 8) =
      (qf c A / 8) • (Pi.single c 1 : SpaceX) := by
    funext e
    by_cases he : e = c
    · subst he
      simp
    · simp [he]
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul] at h
  linear_combination 8 * h

theorem exists_line (hf : IsParityAut f) (c : ShortIdx) :
    ∃ d : ShortIdx, ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      resX f (Pi.single c 1) = ε • Pi.single d 1 ∧ ∀ A : symMat, qf d (resA f A) = qf c A := by
  set y := resX f (Pi.single c 1) with hy_def
  have hy0 : y ≠ 0 := fun h0 => by
    have h1 : resX f (Pi.single c 1) = resX f 0 := by rw [← hy_def, h0, map_zero]
    have := congrFun (hf.resX_injective h1) c
    simp at this
  obtain ⟨d, hd⟩ : ∃ d, y d ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy0 (funext hc)
  have hchar : ∀ e, y e ≠ 0 → ∀ A, qf e (resA f A) = qf c A := fun e he A => by
    have := (mul_eq_zero.1 (hf.resX_single_apply c e A)).resolve_left he
    linarith
  have hsupp : ∀ e, e ≠ d → y e = 0 := by
    intro e he
    by_contra hye
    exact he (eq_of_forall_qf_eq fun B => by
      obtain ⟨A, rfl⟩ := hf.resA_surjective B
      rw [hchar e hye, hchar d hd])
  have hy : y = y d • Pi.single d 1 := by
    funext e
    by_cases he : e = d
    · subst he
      simp
    · simp [he, hsupp e he]
  have hnorm : y d * y d = 1 := by
    have h := hf.map_bform (inX (Pi.single c 1)) (inX (Pi.single c 1))
    rw [hf.apply_inX, bform_inX_inX, bform_inX_inX, ← hy_def, hy, smul_dotProduct,
      dotProduct_smul, single_dotProduct_single, single_dotProduct_single] at h
    simpa [smul_eq_mul] using h
  exact ⟨d, y d, mul_self_eq_one_iff.1 hnorm, hy, hchar d hd⟩

@[expose] def lineMap (hf : IsParityAut f) (c : ShortIdx) : ShortIdx := (hf.exists_line c).choose

@[expose] def lineSign (hf : IsParityAut f) (c : ShortIdx) : ℚ :=
  (hf.exists_line c).choose_spec.choose

theorem lineSign_eq (hf : IsParityAut f) (c : ShortIdx) :
    hf.lineSign c = 1 ∨ hf.lineSign c = -1 :=
  (hf.exists_line c).choose_spec.choose_spec.1

theorem resX_single (hf : IsParityAut f) (c : ShortIdx) :
    resX f (Pi.single c 1) = hf.lineSign c • Pi.single (hf.lineMap c) 1 :=
  (hf.exists_line c).choose_spec.choose_spec.2.1

theorem qf_lineMap (hf : IsParityAut f) (c : ShortIdx) (A : symMat) :
    qf (hf.lineMap c) (resA f A) = qf c A :=
  (hf.exists_line c).choose_spec.choose_spec.2.2 A

theorem lineSign_ne_zero (hf : IsParityAut f) (c : ShortIdx) : hf.lineSign c ≠ 0 := by
  rcases hf.lineSign_eq c with h | h <;> rw [h] <;> norm_num

theorem lineMap_injective (hf : IsParityAut f) : Function.Injective hf.lineMap := by
  intro c c' h
  have h1 : resX f (hf.lineSign c' • Pi.single c 1) = resX f (hf.lineSign c • Pi.single c' 1) := by
    rw [map_smul, map_smul, hf.resX_single, hf.resX_single, h, smul_smul, smul_smul, mul_comm]
  have h2 := congrFun (hf.resX_injective h1) c
  by_contra hne
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, smul_zero,
    smul_eq_mul, mul_one] at h2
  exact hf.lineSign_ne_zero c' h2

theorem lineMap_bijective (hf : IsParityAut f) : Function.Bijective hf.lineMap :=
  Finite.injective_iff_bijective.1 hf.lineMap_injective

theorem resA_UmatS (hf : IsParityAut f) (c : ShortIdx) :
    resA f (UmatS c) = UmatS (hf.lineMap c) := by
  refine eq_of_forall_trace_mul_eq fun B => ?_
  obtain ⟨A, rfl⟩ := hf.resA_surjective B
  rw [hf.resA_trace, coe_UmatS, coe_UmatS, trace_Umat_mul, trace_Umat_mul, hf.qf_lineMap]

theorem apply_Xlift (hf : IsParityAut f) {r : Q} (hr : IsShortCoord (coordOf r)) :
    f (inX (Xlift r)) = inX ((sgn (centralCoord r) * hf.lineSign ⟨coordOf r, hr⟩) •
      Xlift (rep (hf.lineMap ⟨coordOf r, hr⟩).1)) := by
  rw [hf.apply_inX, Xlift_eq hr, map_smul, hf.resX_single, Xlift_rep_eq, smul_smul]

end IsParityAut

end CFSG.Monster.Parity
