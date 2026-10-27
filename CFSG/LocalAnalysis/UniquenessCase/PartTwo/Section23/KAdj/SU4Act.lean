module

public import CFSG.Quasithin.H13.U4ParLevi
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

theorem su4_exists_coroot (c : Kˣ) :
    ∃ g : ↥(hypSU h 2 0),
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        Matrix.diagonal (torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ)) := by
  have hp : torusRatio h ![c, c⁻¹] (![] : Fin 0 → Kˣ) = 1 := by
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    simp only [torusRatio, Fin.prod_univ_two, Fin.prod_univ_zero, mul_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv]
    field_simp <;> ring
  obtain ⟨g, -, hg⟩ := torusMat_mem_hypSU h ![c, c⁻¹] (d := (![] : Fin 0 → Kˣ))
    (fun k => k.elim0) hp
  exact ⟨g, hg⟩

@[expose] noncomputable def su4Coroot (c : Kˣ) : ↥(hypSU h 2 0) :=
  (su4_exists_coroot h c).choose

theorem coe_su4Coroot (c : Kˣ) :
    (((su4Coroot h c : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        Matrix.diagonal (torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ)) :=
  (su4_exists_coroot h c).choose_spec

theorem su4_exists_eq_coroot_of_mem_hypTorus {g : ↥(hypSU h 2 0)} (hg : g ∈ hypTorus h 2 0)
    (hχ : (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          (Sum.inl 0) (Sum.inl 0)) *
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          (Sum.inl 1) (Sum.inl 1)) = 1) :
    ∃ c : Kˣ, g = su4Coroot h c := by
  obtain ⟨a, d, -, -, hg'⟩ := hg
  have h1 : (a 0 : K) * (a 1 : K) = 1 := by
    have hh := hχ
    rw [hg'] at hh
    simpa [Matrix.diagonal_apply_eq, torusEntries] using hh
  have ha1 : a 1 = (a 0)⁻¹ := by
    apply Units.ext
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right h1
  refine ⟨a 0, hypSU_ext h ?_⟩
  rw [hg', coe_su4Coroot]
  have hfun : torusEntries h a d = torusEntries h ![a 0, (a 0)⁻¹] (![] : Fin 0 → Kˣ) := by
    funext x
    rcases x with i | k | i
    · fin_cases i <;> simp [torusEntries, Matrix.cons_val_zero, Matrix.cons_val_one, ha1]
    · exact k.elim0
    · fin_cases i <;> simp [torusEntries, Matrix.cons_val_zero, Matrix.cons_val_one, ha1]
  rw [hfun]

private noncomputable def su4CorootHom_D04 : Kˣ →* ↥(hypSU h 2 0) where
  toFun := su4Coroot h
  map_one' := by
    apply hypSU_ext h
    rw [coe_su4Coroot, Subgroup.coe_one, Units.val_one, Matrix.diagonal_eq_one]
    funext x
    rcases ix_cases x with rfl | rfl | rfl | rfl <;>
      simp [torusEntries, ie1, ie2, if1, if2, Matrix.cons_val_zero, Matrix.cons_val_one]
  map_mul' c c' := by
    apply hypSU_ext h
    rw [coe_su4Coroot, coe_mul_hypSU, coe_su4Coroot, coe_su4Coroot, Matrix.diagonal_mul_diagonal]
    have hfun : torusEntries h ![c * c', (c * c')⁻¹] (![] : Fin 0 → Kˣ) =
        fun i => torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ) i *
          torusEntries h ![c', c'⁻¹] (![] : Fin 0 → Kˣ) i := by
      funext x
      rcases ix_cases x with rfl | rfl | rfl | rfl <;>
        simp [torusEntries, ie1, ie2, if1, if2, map_mul, map_inv₀, mul_inv_rev, mul_comm,
          Units.val_inv_eq_inv_val]
    rw [hfun]

private theorem su4CorootHom_D04_injective : Function.Injective (su4CorootHom_D04 h) := by
  intro c c' hcc
  have h0 : (((su4Coroot h c : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) ie1 ie1 =
      (((su4Coroot h c' : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) ie1 ie1 :=
    congrArg (fun g : ↥(hypSU h 2 0) =>
      (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ie1 ie1)) hcc
  have hh : torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ) ie1 =
      torusEntries h ![c', c'⁻¹] (![] : Fin 0 → Kˣ) ie1 := by
    simpa only [coe_su4Coroot, Matrix.diagonal_apply_eq] using h0
  exact Units.ext (by simpa [ie1, torusEntries, Matrix.cons_val_zero] using hh)

theorem orderOf_su4Coroot (c : Kˣ) : orderOf (su4Coroot h c) = orderOf c :=
  orderOf_injective (su4CorootHom_D04 h) (su4CorootHom_D04_injective h) c

theorem su4_exists_fixedField_unit_of_orderOf_dvd (c : Kˣ) (hc : orderOf c ∣ 2 ^ a - 1) :
    ∃ c' : h.fixedFieldˣ, ((c' : h.fixedField) : K) = (c : K) := by
  have h1 : c ^ (2 ^ a - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hc
  have hval : (c : K) ^ (2 ^ a - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hpow : (c : K) ^ 2 ^ a = (c : K) := by
    have hsucc : 2 ^ a = (2 ^ a - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm
    rw [hsucc, pow_succ, hval, one_mul]
  have hmem : (c : K) ∈ h.fixedField := h.mem_fixedField.mpr (by rw [h.bar_apply, hpow])
  exact ⟨Units.mk0 ⟨(c : K), hmem⟩ (fun h0 => c.ne_zero (congrArg Subtype.val h0)), rfl⟩

@[expose] noncomputable def su4Diag2 (c : h.fixedFieldˣ) :
    Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨Matrix.diagonal ![((c⁻¹ : h.fixedFieldˣ) : h.fixedField), (c : h.fixedField)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

private noncomputable def su4Diag2Hom_D04 :
    h.fixedFieldˣ →* Matrix.SpecialLinearGroup (Fin 2) h.fixedField where
  toFun := su4Diag2 h
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su4Diag2, Matrix.SpecialLinearGroup.coe_one, Matrix.diagonal_apply, Matrix.one_apply]
  map_mul' c d := by
    apply Subtype.ext
    show (↑(su4Diag2 h (c * d)) : Matrix (Fin 2) (Fin 2) h.fixedField) =
      (↑(su4Diag2 h c) : Matrix (Fin 2) (Fin 2) h.fixedField) *
        (↑(su4Diag2 h d) : Matrix (Fin 2) (Fin 2) h.fixedField)
    rw [show (↑(su4Diag2 h (c * d)) : Matrix (Fin 2) (Fin 2) h.fixedField) =
      Matrix.diagonal ![(((c * d)⁻¹ : h.fixedFieldˣ) : h.fixedField),
        ((c * d : h.fixedFieldˣ) : h.fixedField)] from rfl,
      show (↑(su4Diag2 h c) : Matrix (Fin 2) (Fin 2) h.fixedField) =
        Matrix.diagonal ![((c⁻¹ : h.fixedFieldˣ) : h.fixedField), (c : h.fixedField)] from rfl,
      show (↑(su4Diag2 h d) : Matrix (Fin 2) (Fin 2) h.fixedField) =
        Matrix.diagonal ![((d⁻¹ : h.fixedFieldˣ) : h.fixedField), (d : h.fixedField)] from rfl,
      Matrix.diagonal_mul_diagonal]
    have hfun : (![(((c * d)⁻¹ : h.fixedFieldˣ) : h.fixedField),
        ((c * d : h.fixedFieldˣ) : h.fixedField)] : Fin 2 → h.fixedField) =
        fun i => ![((c⁻¹ : h.fixedFieldˣ) : h.fixedField), (c : h.fixedField)] i *
          ![((d⁻¹ : h.fixedFieldˣ) : h.fixedField), (d : h.fixedField)] i := by
      funext i
      fin_cases i <;> simp [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev, mul_comm]
    rw [hfun]

private theorem su4Diag2Hom_D04_injective : Function.Injective (su4Diag2Hom_D04 h) := by
  intro c d hcd
  have hh := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField =>
    (A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1) hcd
  simp only [su4Diag2Hom_D04, su4Diag2, Matrix.diagonal_apply_eq, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hh
  exact Units.ext hh

private theorem slMat_su4Diag2_D04 (c' : h.fixedFieldˣ) :
    slMat h (su4Diag2 h c') = Matrix.diagonal ![(c' : K)⁻¹, (c' : K)] := by
  show ((↑(su4Diag2 h c') : Matrix (Fin 2) (Fin 2) h.fixedField)).map h.fixedField.subtype =
    Matrix.diagonal ![(c' : K)⁻¹, (c' : K)]
  rw [show (↑(su4Diag2 h c') : Matrix (Fin 2) (Fin 2) h.fixedField) =
    Matrix.diagonal ![((c'⁻¹ : h.fixedFieldˣ) : h.fixedField), (c' : h.fixedField)] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_inv_eq_inv_val, Subfield.coe_inv]

private theorem slMat_su4Diag2_inv_D04 (c' : h.fixedFieldˣ) :
    slMat h ((su4Diag2 h c')⁻¹) = Matrix.diagonal ![(c' : K), (c' : K)⁻¹] := by
  have h1 : su4Diag2 h c' * su4Diag2 h c'⁻¹ = 1 := by
    change su4Diag2Hom_D04 h c' * su4Diag2Hom_D04 h c'⁻¹ = 1
    rw [← map_mul (su4Diag2Hom_D04 h), mul_inv_cancel, map_one]
  have hinv : (su4Diag2 h c')⁻¹ = su4Diag2 h c'⁻¹ := (eq_inv_of_mul_eq_one_right h1).symm
  rw [hinv, slMat_su4Diag2_D04 h c'⁻¹]
  congr 1
  funext i
  fin_cases i <;> simp [Units.val_inv_eq_inv_val, Subfield.coe_inv, inv_inv]

private theorem levMat_diagonal_D04 {x y : K} :
    levMat (Matrix.diagonal ![x, y]) =
      Matrix.diagonal (fun i : Ix =>
        if i = ie1 then 1 else if i = ie2 then x else if i = if1 then 1 else y) := by
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ie1, ie2, if1, if2]

private theorem torusEntries_su4_D04 {c : Kˣ} (hbar : h.bar (c : K) = c) :
    torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ) =
      fun i : Ix => if i = ie1 then (c : K) else if i = ie2 then (c : K)⁻¹
        else if i = if1 then (c : K)⁻¹ else (c : K) := by
  funext i
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    simp [torusEntries, ie1, ie2, if1, if2, Units.val_inv_eq_inv_val, map_inv₀, hbar]

private theorem su4_mat_identity_D04 {c : Kˣ} {c' : h.fixedFieldˣ}
    (hc : ((c' : h.fixedField) : K) = (c : K))
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    Matrix.diagonal (torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ)) * levMat (slMat h A) =
      levMat (slMat h (su4Diag2 h c' * A * (su4Diag2 h c')⁻¹)) *
        Matrix.diagonal (torusEntries h ![c, c⁻¹] (![] : Fin 0 → Kˣ)) := by
  have hbar : h.bar (c : K) = c := by
    have hh := h.mem_fixedField.mp (c' : h.fixedField).2
    rwa [hc] at hh
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hdecomp : slMat h (su4Diag2 h c' * A * (su4Diag2 h c')⁻¹) =
      Matrix.diagonal ![(c' : K)⁻¹, (c' : K)] * slMat h A *
        Matrix.diagonal ![(c' : K), (c' : K)⁻¹] := by
    rw [slMat_mul, slMat_mul, slMat_su4Diag2_D04, slMat_su4Diag2_inv_D04]
  rw [hdecomp, ← levMat_mul, ← levMat_mul, levMat_diagonal_D04, levMat_diagonal_D04,
    torusEntries_su4_D04 h hbar]
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ie1, ie2, if1, if2, hc, hc0,
      mul_inv_cancel₀, inv_mul_cancel₀] <;>
    field_simp <;> ring

theorem orderOf_levHom_su4Diag2 {c : Kˣ} {c' : h.fixedFieldˣ}
    (hc : ((c' : h.fixedField) : K) = (c : K)) :
    orderOf (levHom h (su4Diag2 h c')) = orderOf c := by
  have h1 : orderOf (levHom h (su4Diag2 h c')) = orderOf c' := by
    rw [orderOf_injective (levHom h) (CFSG.Quasithin.F112R.St84.levHom_injective_u4 h)
      (su4Diag2 h c')]
    exact orderOf_injective (su4Diag2Hom_D04 h) (su4Diag2Hom_D04_injective h) c'
  have hmap : Units.map (h.fixedField.subtype : h.fixedField →* K) c' = c := by
    apply Units.ext
    change h.fixedField.subtype (c' : h.fixedField) = (c : K)
    rw [Subfield.coe_subtype]
    exact hc
  have h2 : orderOf c' = orderOf c := by
    rw [← orderOf_injective (Units.map (h.fixedField.subtype : h.fixedField →* K))
      (Units.map_injective h.fixedField.subtype_injective) c', hmap]
  rw [h1, h2]

theorem su4Coroot_mul_levHom_mul_inv {c : Kˣ} {c' : h.fixedFieldˣ}
    (hc : ((c' : h.fixedField) : K) = (c : K))
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    su4Coroot h c * levHom h A * (su4Coroot h c)⁻¹ =
      levHom h (su4Diag2 h c' * A * (su4Diag2 h c')⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply hypSU_ext h
  rw [coe_mul_hypSU, coe_mul_hypSU, coe_su4Coroot, coe_levHom, coe_levHom]
  exact su4_mat_identity_D04 h hc A

theorem su4Coroot_mem_normalizer_levHom_range {c : Kˣ} {c' : h.fixedFieldˣ}
    (hc : ((c' : h.fixedField) : K) = (c : K)) :
    su4Coroot h c ∈ Subgroup.normalizer ((levHom h).range : Set ↥(hypSU h 2 0)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨su4Diag2 h c' * A * (su4Diag2 h c')⁻¹,
      (su4Coroot_mul_levHom_mul_inv h hc A).symm⟩
  · rintro ⟨B, hB⟩
    have hcinv : (((c'⁻¹ : h.fixedFieldˣ) : h.fixedField) : K) = ((c⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Subfield.coe_inv, hc]
    refine ⟨su4Diag2 h c'⁻¹ * B * (su4Diag2 h c'⁻¹)⁻¹, ?_⟩
    have hDinv : su4Coroot h c⁻¹ = (su4Coroot h c)⁻¹ := map_inv (su4CorootHom_D04 h) c
    have hx : su4Coroot h c⁻¹ * levHom h B * (su4Coroot h c⁻¹)⁻¹ = x := by
      rw [hDinv, inv_inv, hB]
      group
    rw [← su4Coroot_mul_levHom_mul_inv h hcinv B]
    exact hx

theorem su4Coroot_conj_eq_of_mem_levHom_range {c : Kˣ} {c' : h.fixedFieldˣ}
    (hc : ((c' : h.fixedField) : K) = (c : K)) {x : ↥(hypSU h 2 0)}
    (hx : x ∈ (levHom h).range) :
    su4Coroot h c * x * (su4Coroot h c)⁻¹ =
      levHom h (su4Diag2 h c') * x * (levHom h (su4Diag2 h c'))⁻¹ := by
  obtain ⟨A, rfl⟩ := hx
  have hR : levHom h (su4Diag2 h c') * levHom h A * (levHom h (su4Diag2 h c'))⁻¹ =
      levHom h (su4Diag2 h c' * A * (su4Diag2 h c')⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul, mul_assoc]
  rw [su4Coroot_mul_levHom_mul_inv h hc A, hR]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
