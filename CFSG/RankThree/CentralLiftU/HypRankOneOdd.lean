module

public import CFSG.RankThree.CentralLiftU.HypRankOneWeyl

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W coe_sl2Diag coe_sl2W)
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r : ℕ}

section DiagJ3

theorem diag_isometry_J3 {u : Fin 3 → K} (h02 : h.bar (u 0) * u 2 = 1)
    (h11 : h.bar (u 1) * u 1 = 1) :
    ((diagonal u).map h.bar)ᵀ * gramJ3 K * diagonal u = gramJ3 K := by
  have h20 : h.bar (u 2) * u 0 = 1 := by
    have := congrArg h.bar h02
    rwa [map_mul, h.bar_bar, map_one, mul_comm] at this
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gramJ3, Matrix.mul_apply, Fin.sum_univ_three, h02, h11, h20]

@[expose] noncomputable def dkVec (a : Kˣ) : Fin 3 → K :=
  ![(a : K), h.bar a / a, (h.bar a)⁻¹]

theorem dkVec_isometry (a : Kˣ) :
    ((diagonal (dkVec h a)).map h.bar)ᵀ * gramJ3 K * diagonal (dkVec h a) = gramJ3 K := by
  have ha := a.ne_zero
  have hba : h.bar a ≠ 0 := (h.bar_eq_zero_iff).not.mpr ha
  refine diag_isometry_J3 h ?_ ?_
  · simp [dkVec, hba]
  · have e : dkVec h a 1 = h.bar a / a := rfl
    rw [e, map_div₀, h.bar_bar]
    field_simp

theorem det_dkVec (a : Kˣ) : (diagonal (dkVec h a)).det = 1 := by
  have ha := a.ne_zero
  have hba : h.bar a ≠ 0 := (h.bar_eq_zero_iff).not.mpr ha
  rw [det_diagonal, Fin.prod_univ_three]
  simp only [dkVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  field_simp

@[expose] noncomputable def dkHom : Kˣ →* gramSU h (gramJ3 K) where
  toFun a := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal (dkVec h a))
      (by rw [det_dkVec]; exact one_ne_zero),
    by rw [mem_gramSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
       exact ⟨dkVec_isometry h a, det_dkVec h a⟩⟩
  map_one' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Subgroup.coe_one, Units.val_one,
      ← diagonal_one]
    congr 1
    funext x
    fin_cases x <;> simp [dkVec]))
  map_mul' a b := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Subgroup.coe_mul, Units.val_mul,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      diagonal_mul_diagonal]
    congr 1
    funext x
    have ha := a.ne_zero
    have hb := b.ne_zero
    fin_cases x <;> simp [dkVec] <;> field_simp))

theorem coe_dkHom (a : Kˣ) :
    ((dkHom h a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal (dkVec h a) :=
  rfl

theorem det_conj_diagonal {u : Fin 3 → K} (hu0 : ∀ x, u x ≠ 0) (X : Matrix (Fin 3) (Fin 3) K) :
    (diagonal u * X * diagonal u⁻¹).det = X.det := by
  rw [det_mul, det_mul, mul_comm (diagonal u).det, mul_assoc, ← det_mul, diagonal_mul_diagonal]
  have : (fun x => u x * u⁻¹ x) = 1 := by funext x; exact mul_inv_cancel₀ (hu0 x)
  rw [this]
  simp

@[expose] noncomputable def conjDiagJ3Elt {u : Fin 3 → K} (hu0 : ∀ x, u x ≠ 0)
    (h02 : h.bar (u 0) * u 2 = 1) (h11 : h.bar (u 1) * u 1 = 1) (X : gramSU h (gramJ3 K)) :
    gramSU h (gramJ3 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (diagonal u * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal u⁻¹)
      (by rw [det_conj_diagonal hu0, X.2.2]; exact one_ne_zero), by
    rw [mem_gramSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    have hX := X.2
    rw [mem_gramSU] at hX
    have hD := diag_isometry_J3 h h02 h11
    have hDi : ((diagonal u⁻¹).map h.bar)ᵀ * gramJ3 K * diagonal u⁻¹ = gramJ3 K := by
      refine diag_isometry_J3 h ?_ ?_
      · simp only [Pi.inv_apply, map_inv₀, ← mul_inv, h02, inv_one]
      · simp only [Pi.inv_apply, map_inv₀, ← mul_inv, h11, inv_one]
    refine ⟨?_, by rw [det_conj_diagonal hu0, hX.2]⟩
    rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
    calc ((diagonal u⁻¹).map h.bar)ᵀ *
          ((((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
            ((diagonal u).map h.bar)ᵀ) * gramJ3 K *
          (diagonal u * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal u⁻¹)
        = ((diagonal u⁻¹).map h.bar)ᵀ *
          ((((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
            (((diagonal u).map h.bar)ᵀ * gramJ3 K * diagonal u) *
              ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * diagonal u⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = gramJ3 K := by rw [hD, hX.1, hDi]⟩

theorem coe_conjDiagJ3Elt {u : Fin 3 → K} (hu0 : ∀ x, u x ≠ 0) (h02 : h.bar (u 0) * u 2 = 1)
    (h11 : h.bar (u 1) * u 1 = 1) (X : gramSU h (gramJ3 K)) :
    ((conjDiagJ3Elt h hu0 h02 h11 X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal u * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal u⁻¹ :=
  rfl

@[expose] noncomputable def conjDiagJ3 {u : Fin 3 → K} (hu0 : ∀ x, u x ≠ 0)
    (h02 : h.bar (u 0) * u 2 = 1) (h11 : h.bar (u 1) * u 1 = 1) :
    gramSU h (gramJ3 K) →* gramSU h (gramJ3 K) where
  toFun := conjDiagJ3Elt h hu0 h02 h11
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_conjDiagJ3Elt]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, diagonal_mul_diagonal]
    have : (fun x => u x * u⁻¹ x) = 1 := by funext x; exact mul_inv_cancel₀ (hu0 x)
    rw [this]
    simp
  map_mul' X Y := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_conjDiagJ3Elt, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul,
      coe_conjDiagJ3Elt, coe_conjDiagJ3Elt]
    have hinv : diagonal u⁻¹ * diagonal u = 1 := by
      rw [diagonal_mul_diagonal]
      have : (fun x => u⁻¹ x * u x) = 1 := by funext x; exact inv_mul_cancel₀ (hu0 x)
      rw [this]
      simp
    calc diagonal u * (((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * diagonal u⁻¹
        = diagonal u * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (diagonal u⁻¹ * diagonal u) * ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              diagonal u⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_conjDiagJ3 {u : Fin 3 → K} (hu0 : ∀ x, u x ≠ 0) (h02 : h.bar (u 0) * u 2 = 1)
    (h11 : h.bar (u 1) * u 1 = 1) (X : gramSU h (gramJ3 K)) :
    ((conjDiagJ3 h hu0 h02 h11 X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal u * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal u⁻¹ :=
  rfl

theorem conjDiagJ3_dkHom {u : Fin 3 → K} (hu0 : ∀ x, u x ≠ 0) (h02 : h.bar (u 0) * u 2 = 1)
    (h11 : h.bar (u 1) * u 1 = 1) (a : Kˣ) : conjDiagJ3 h hu0 h02 h11 (dkHom h a) = dkHom h a := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_conjDiagJ3, coe_dkHom, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  rw [Pi.inv_apply, mul_comm (u x), mul_assoc, mul_inv_cancel₀ (hu0 x), mul_one]

end DiagJ3

section Iota3

variable {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

@[expose] noncomputable def iota3Mat (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    Matrix (Fin 3) (Fin 3) K :=
  !![((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K), 0,
      c⁻¹ * ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
    0, 1, 0;
    c * ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K), 0,
      ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)]

theorem iota3Mat_eq_blockMat (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    iota3Mat h (c := c) g = blockMat (![0, 2] : Fin 2 → Fin 3) (iota2Mat h c g) := by
  have hinj : Function.Injective (![0, 2] : Fin 2 → Fin 3) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  ext x y
  fin_cases x <;> fin_cases y <;>
    first
    | exact (blockMat_apply_e (e := (![0, 2] : Fin 2 → Fin 3)) hinj (iota2Mat h c g) 0 0).symm
    | exact (blockMat_apply_e (e := (![0, 2] : Fin 2 → Fin 3)) hinj (iota2Mat h c g) 0 1).symm
    | exact (blockMat_apply_e (e := (![0, 2] : Fin 2 → Fin 3)) hinj (iota2Mat h c g) 1 0).symm
    | exact (blockMat_apply_e (e := (![0, 2] : Fin 2 → Fin 3)) hinj (iota2Mat h c g) 1 1).symm
    | (rw [blockMat_apply_of_notMem_left]
       · simp [iota3Mat, one_apply]
       · intro a; fin_cases a <;> simp)
    | (rw [blockMat_apply_of_notMem_right]
       · simp [iota3Mat, one_apply]
       · intro a; fin_cases a <;> simp)

include hc0 in
theorem iota3Mat_mul (g g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    iota3Mat h (c := c) (g * g') = iota3Mat h (c := c) g * iota3Mat h (c := c) g' := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [iota3Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem iota3Mat_one : iota3Mat h (c := c) 1 = 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [iota3Mat, one_apply]

include hc hc0 in
theorem iota3Mat_mem (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((iota3Mat h (c := c) g).map h.bar)ᵀ * gramJ3 K * iota3Mat h (c := c) g = gramJ3 K ∧
      (iota3Mat h (c := c) g).det = 1 := by
  have hbc : h.bar c = -c := by have : c + h.bar c = 0 := hc; linear_combination this
  have hfix : ∀ x : h.fixedField, h.bar (x : K) = x := fun x => x.2
  have hdet : ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K) *
      ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K) -
      ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K) *
      ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K) = 1 := by
    have := congrArg (Subtype.val : h.fixedField → K) g.2
    rw [det_fin_two] at this
    simpa using this
  refine ⟨?_, ?_⟩
  · ext x y
    fin_cases x <;> fin_cases y <;>
      simp [iota3Mat, gramJ3, Matrix.mul_apply, Fin.sum_univ_three, hbc, hfix, map_inv₀] <;>
      field_simp <;> first | ring1 | linear_combination hdet
  · rw [det_fin_three]
    simp [iota3Mat]
    field_simp
    linear_combination hdet

include hc hc0 in
@[expose] noncomputable def iota3 :
    SpecialLinearGroup (Fin 2) h.fixedField →* gramSU h (gramJ3 K) where
  toFun g := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (iota3Mat h (c := c) g)
      (by rw [(iota3Mat_mem h hc hc0 g).2]; exact one_ne_zero),
    by rw [mem_gramSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
       exact iota3Mat_mem h hc hc0 g⟩
  map_one' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, iota3Mat_one]; rfl))
  map_mul' g g' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, iota3Mat_mul h hc0]; rfl))

theorem coe_iota3 (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((iota3 h hc hc0 g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = iota3Mat h (c := c) g :=
  rfl

theorem iotaU_eq_kappaU_comp (k : Fin r) :
    iotaU (ε := 1) h hc hc0 k = (kappaU h k).comp (iota3 h hc hc0) := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rw [MonoidHom.comp_apply, coe_kappaU, coe_iota3, coe_iotaU, iota3Mat_eq_blockMat,
    blockMat_blockMat]
  have : tripIdx k ∘ (![0, 2] : Fin 2 → Fin 3) = pairIdx k := by
    funext a; fin_cases a <;> rfl
  rw [this]
  rfl

theorem iota3_sl2Diag_neg_one : iota3 h hc hc0 (sl2Diag (-1)) = dkHom h (-1) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_iota3, coe_dkHom]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [iota3Mat, dkVec]

@[expose] noncomputable def barInv (a : Kˣ) : Kˣ := (Units.map (h.bar : K →* K) a)⁻¹

theorem coe_barInv (a : Kˣ) : ((barInv h a : Kˣ) : K) = (h.bar a)⁻¹ := by
  simp [barInv]

theorem iota3_sl2W_conj_dk (a : Kˣ) :
    iota3 h hc hc0 sl2W * dkHom h a * (iota3 h hc hc0 sl2W)⁻¹ = dkHom h (barInv h a) := by
  have hcinv : ((sl2W : SpecialLinearGroup (Fin 2) h.fixedField)⁻¹ :
      SpecialLinearGroup (Fin 2) h.fixedField) = sl2W * sl2Diag (-1) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_sl2W_inv,
      Matrix.SpecialLinearGroup.coe_mul]
    fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← map_inv, hcinv]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_iota3, coe_iota3,
    coe_dkHom, coe_dkHom]
  have ha := a.ne_zero
  have hba : h.bar a ≠ 0 := (h.bar_eq_zero_iff).not.mpr ha
  have hw : iota3Mat h (c := c) sl2W = !![0, 0, -c⁻¹; 0, 1, 0; c, 0, 0] := by
    ext x y; fin_cases x <;> fin_cases y <;> simp [iota3Mat]
  have hw' : iota3Mat h (c := c) (sl2W * sl2Diag (-1)) = !![0, 0, c⁻¹; 0, 1, 0; -c, 0, 0] := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [iota3Mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hd : diagonal (dkVec h a) = !![(a : K), 0, 0; 0, h.bar a / a, 0; 0, 0, (h.bar a)⁻¹] := by
    ext x y; fin_cases x <;> fin_cases y <;> simp [dkVec]
  have hd' : diagonal (dkVec h (barInv h a)) =
      !![(h.bar a)⁻¹, 0, 0; 0, a⁻¹ * h.bar a, 0; 0, 0, (a : K)] := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [dkVec, coe_barInv, map_inv₀, h.bar_bar]
  rw [hw, hw', hd, hd', Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext x y
  fin_cases x <;> fin_cases y <;> simp <;> field_simp

end Iota3

section Kappa

@[expose] noncomputable def kappaDiag (k : Fin r) (a : Kˣ) : HypIndex r 1 → K
  | .inl x => if x = k then (a : K) else 1
  | .inr (.inl _) => h.bar a / a
  | .inr (.inr x) => if x = k then (h.bar a)⁻¹ else 1

theorem coe_kappaU_dkHom (k : Fin r) (a : Kˣ) :
    ((kappaU h k (dkHom h a) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      diagonal (kappaDiag h k a) := by
  rw [coe_kappaU, coe_dkHom]
  refine blockMat_diagonal (tripIdx_injective k) ?_ ?_
  · intro a'
    fin_cases a' <;> simp [tripIdx, kappaDiag, dkVec]
  · rintro (x | l | x) hx
    · have h1 : x ≠ k := fun h1 => hx 0 (by simp [tripIdx, h1])
      simp [kappaDiag, h1]
    · exact absurd (by fin_cases l; rfl) (hx 1)
    · have h1 : x ≠ k := fun h1 => hx 2 (by simp [tripIdx, h1])
      simp [kappaDiag, h1]

theorem diag_trip_ne_zero {d : hypSU h r 1} {q : HypIndex r 1 → K}
    (hd : ((d : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) (x : Fin 3) : (q ∘ tripIdx k) x ≠ 0 :=
  diag_entry_ne_zero h hd _

theorem diag_trip_02 {d : hypSU h r 1} {q : HypIndex r 1 → K}
    (hd : ((d : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) : h.bar ((q ∘ tripIdx k) 0) * (q ∘ tripIdx k) 2 = 1 :=
  diag_entries h hd (.inl k)

theorem diag_trip_11 {d : hypSU h r 1} {q : HypIndex r 1 → K}
    (hd : ((d : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) : h.bar ((q ∘ tripIdx k) 1) * (q ∘ tripIdx k) 1 = 1 :=
  diag_entries h hd (.inr (.inl 0))

theorem conj_diag_kappaU {d : hypSU h r 1} {q : HypIndex r 1 → K}
    (hd : ((d : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) (X : gramSU h (gramJ3 K)) :
    d * kappaU h k X * d⁻¹ = kappaU h k (conjDiagJ3 h (diag_trip_ne_zero h hd k)
      (diag_trip_02 h hd k) (diag_trip_11 h hd k) X) := by
  have hq0 := diag_entry_ne_zero h hd
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hd,
    coe_inv_of_diagonal h hd, coe_kappaU, coe_kappaU]
  refine (conj_blockMat (diagonal_mul_embMat _ q) (transpose_embMat_mul_diagonal _ q⁻¹) ?_ ?_
    _).trans rfl
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    exact mul_inv_cancel₀ (hq0 x)
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hq0 _)

theorem wSignU_comp_tripIdx (j k : Fin r) :
    (wSignU (K := K) (ε := 1) j ∘ tripIdx k) = ![lineSign j k, 1, lineSign j k] := by
  funext a; fin_cases a <;> rfl

theorem swapIdx_comp_tripIdx (i j k : Fin r) :
    swapIdx (ε := 1) i j ∘ tripIdx k = tripIdx (Equiv.swap i j k) := by
  funext a; fin_cases a <;> rfl

theorem lineSign_isometry_J3 (j k : Fin r) :
    h.bar ((![lineSign j k, 1, lineSign j k] : Fin 3 → K) 0) *
        (![lineSign j k, 1, lineSign j k] : Fin 3 → K) 2 = 1 ∧
      h.bar ((![lineSign j k, 1, lineSign j k] : Fin 3 → K) 1) *
        (![lineSign j k, 1, lineSign j k] : Fin 3 → K) 1 = 1 := by
  unfold lineSign
  split_ifs <;> simp

theorem conj_rhoU_sl2W_kappaU {i j : Fin r} (hij : i ≠ j) (k : Fin r)
    (X : gramSU h (gramJ3 K)) :
    rhoU h hij sl2W * kappaU h k X * (rhoU h hij sl2W)⁻¹ =
      kappaU h (Equiv.swap i j k) (conjDiagJ3 h (u := ![lineSign j k, 1, lineSign j k])
        (fun x => by fin_cases x <;> simp [lineSign_ne_zero])
        (lineSign_isometry_J3 h j k).1 (lineSign_isometry_J3 h j k).2 X) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_rhoU_sl2W h hij,
    coe_rhoU_sl2W_inv h hij, coe_kappaU, coe_kappaU, coe_conjDiagJ3,
    conj_signedPerm_blockMat _ ?_, swapIdx_comp_tripIdx, wSignU_comp_tripIdx]
  · congr 2
    funext a
    simp only [Equiv.symm_apply_apply]
    fin_cases a <;> rfl
  · intro x
    rw [Equiv.symm_apply_apply]
    exact wSignU_mul_inv j x

theorem commute_rhoU_kappaU {i j : Fin r} (hij : i ≠ j) {k : Fin r} (hik : i ≠ k)
    (hjk : j ≠ k) (g : SpecialLinearGroup (Fin 2) K) (X : gramSU h (gramJ3 K)) :
    Commute (rhoU h hij g) (kappaU h k X) := by
  refine hypSU_commute_of_val h ?_
  rw [coe_rhoU, coe_kappaU]
  refine commute_blockMat ?_ _ _
  rintro (a | a) b <;> fin_cases a <;> fin_cases b <;> simp_all [quadIdx, tripIdx]

theorem commute_iotaU_kappaU {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {k l : Fin r}
    (hkl : k ≠ l) (g : SpecialLinearGroup (Fin 2) h.fixedField) (X : gramSU h (gramJ3 K)) :
    Commute (iotaU (ε := 1) h hc hc0 k g) (kappaU h l X) := by
  refine hypSU_commute_of_val h ?_
  rw [coe_iotaU, coe_kappaU]
  refine commute_blockMat ?_ _ _
  intro a b
  fin_cases a <;> fin_cases b <;> simp_all [pairIdx, tripIdx]

end Kappa

end CFSG.RankThree.CentralLiftU
