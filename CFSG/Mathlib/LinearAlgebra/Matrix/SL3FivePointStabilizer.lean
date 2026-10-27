module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.Mathlib.GroupTheory.PerfectStabilizerLargeOrbit
public import Mathlib.Algebra.Field.ZMod

public section

open Matrix
open scoped MatrixGroups commutatorElement

namespace CFSG.GroupTheory.SL3Five

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev F := ZMod 5

local instance (priority := 2000) : AddCommGroup F :=
  (inferInstance : Field F).toAddCommGroup
abbrev V := Fin 3 → F
abbrev W := Fin 2 → F

@[expose] def e0 : V := Pi.single 0 1

@[expose] def e1 : V := Pi.single 1 1

abbrev SL3 := SL(3, F)
abbrev SL2 := SL(2, F)

@[expose] def rowTranslation (r : W) : Matrix (Fin 3) (Fin 3) F :=
  !![1, r 0, r 1; 0, 1, 0; 0, 0, 1]

@[expose] def blockDiag (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

@[simp]
theorem rowTranslation_det (r : W) : (rowTranslation r).det = 1 := by
  simp [rowTranslation, Matrix.det_fin_three]

@[simp]
theorem blockDiag_det (A : Matrix (Fin 2) (Fin 2) F) :
    (blockDiag A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blockDiag]

@[expose] def rowTranslationSL (r : W) : SL3 :=
  ⟨rowTranslation r, rowTranslation_det r⟩

@[expose] def blockDiagSL (A : SL2) : SL3 :=
  ⟨blockDiag A.1, by rw [blockDiag_det, A.2]⟩

@[simp]
theorem rowTranslationSL_coe (r : W) :
    (rowTranslationSL r : Matrix (Fin 3) (Fin 3) F) = rowTranslation r := rfl

@[simp]
theorem blockDiagSL_coe (A : SL2) :
    (blockDiagSL A : Matrix (Fin 3) (Fin 3) F) = blockDiag A.1 := rfl

@[simp]
theorem rowTranslation_mulVec_e0 (r : W) : rowTranslation r *ᵥ e0 = e0 := by
  ext i
  fin_cases i <;> simp [rowTranslation, e0, Matrix.mulVec]

@[simp]
theorem blockDiag_mulVec_e0 (A : Matrix (Fin 2) (Fin 2) F) :
    blockDiag A *ᵥ e0 = e0 := by
  ext i
  fin_cases i <;> simp [blockDiag, e0, Matrix.mulVec]

@[simp]
theorem rowTranslation_smul_e0 (r : W) : rowTranslationSL r • e0 = e0 := by
  rw [Matrix.SpecialLinearGroup.smul_def, rowTranslationSL_coe]
  simpa only [Matrix.smul_eq_mulVec] using rowTranslation_mulVec_e0 r

@[simp]
theorem blockDiag_smul_e0 (A : SL2) : blockDiagSL A • e0 = e0 := by
  rw [Matrix.SpecialLinearGroup.smul_def, blockDiagSL_coe]
  simpa only [Matrix.smul_eq_mulVec] using blockDiag_mulVec_e0 A.1

@[expose] def pointStabilizer : Subgroup SL3 := MulAction.stabilizer SL3 e0

theorem rowTranslationSL_mem_pointStabilizer (r : W) :
    rowTranslationSL r ∈ pointStabilizer := by
  rw [pointStabilizer, MulAction.mem_stabilizer_iff]
  exact rowTranslation_smul_e0 r

theorem blockDiagSL_mem_pointStabilizer (A : SL2) :
    blockDiagSL A ∈ pointStabilizer := by
  rw [pointStabilizer, MulAction.mem_stabilizer_iff]
  exact blockDiag_smul_e0 A

theorem eq_blockDiag_mul_rowTranslation {g : SL3} (hg : g ∈ pointStabilizer) :
    ∃ (A : SL2) (r : W), g = blockDiagSL A * rowTranslationSL r := by
  classical
  let M : Matrix (Fin 3) (Fin 3) F := g.1
  have hg' : M *ᵥ e0 = e0 := by
    have h := hg
    rw [pointStabilizer, MulAction.mem_stabilizer_iff,
      Matrix.SpecialLinearGroup.smul_def] at h
    simpa [M] using h
  have hcol (i : Fin 3) : M i 0 = e0 i := by
    have h := congrFun hg' i
    simpa [Matrix.mulVec, dotProduct, e0, Fin.sum_univ_succ] using h
  have h00 : M 0 0 = 1 := by simpa [e0] using hcol 0
  have h10 : M 1 0 = 0 := by simpa [e0] using hcol 1
  have h20 : M 2 0 = 0 := by simpa [e0] using hcol 2
  let A : Matrix (Fin 2) (Fin 2) F := M.submatrix Fin.succ Fin.succ
  let r : W := fun j => M 0 (Fin.succ j)
  have hA : A.det = 1 := by
    have h := Matrix.det_succ_column_zero M
    rw [g.2] at h
    rw [Finset.sum_eq_single 0] at h
    · simpa [A, h00, Fin.succAbove_zero] using h.symm
    · intro i _ hi
      rw [hcol i]
      simp [e0, hi]
    · simp
  refine ⟨⟨A, hA⟩, r, ?_⟩
  apply Subtype.ext
  change M = blockDiag A * rowTranslation r
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, blockDiag, rowTranslation, A, r,
      Matrix.mul_apply, Fin.sum_univ_succ, h00, h10, h20]

theorem blockDiag_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    blockDiag (A * B) = blockDiag A * blockDiag B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem blockDiag_one : blockDiag (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag]

@[expose] def blockDiagHom : SL2 →* SL3 where
  toFun := blockDiagSL
  map_one' := by
    apply Subtype.ext
    change blockDiag (1 : Matrix (Fin 2) (Fin 2) F) = 1
    exact blockDiag_one
  map_mul' A B := by
    apply Subtype.ext
    change blockDiag (A.1 * B.1) = blockDiag A.1 * blockDiag B.1
    exact blockDiag_mul A.1 B.1

theorem sl2_isPerfect : Group.IsPerfect SL2 := by
  rw [Group.isPerfect_def]
  exact Matrix.SL2.commutator_eq_top (a := 2) (by decide) (by decide)

@[expose] def diagNeg : SL2 := ⟨!![-1, 0; 0, -1], by
  rw [Matrix.det_fin_two]
  decide⟩

@[simp]
theorem diagNeg_coe : (diagNeg : Matrix (Fin 2) (Fin 2) F) = !![(-1 : F), 0; 0, -1] := rfl

theorem diagNeg_mul_self : diagNeg * diagNeg = 1 := by
  apply Subtype.ext
  change (diagNeg : Matrix (Fin 2) (Fin 2) F) * (diagNeg : Matrix (Fin 2) (Fin 2) F) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagNeg, Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] def t : SL3 := blockDiagSL diagNeg

@[simp]
theorem t_coe : (t : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  simp [t, blockDiagSL, blockDiag, diagNeg]

theorem t_mul_self : t * t = 1 := by
  change blockDiagHom diagNeg * blockDiagHom diagNeg = 1
  rw [← blockDiagHom.map_mul, diagNeg_mul_self, blockDiagHom.map_one]

theorem t_inv : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right t_mul_self

theorem rowTranslationSL_add (r s : W) :
    rowTranslationSL (r + s) = rowTranslationSL r * rowTranslationSL s := by
  apply Subtype.ext
  change rowTranslation (r + s) = rowTranslation r * rowTranslation s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowTranslation, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

@[simp]
theorem rowTranslationSL_zero : rowTranslationSL (0 : W) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowTranslationSL, rowTranslation]

theorem rowTranslationSL_neg (s : W) :
    rowTranslationSL s * rowTranslationSL (-s) = 1 := by
  have h : s + -s = 0 := by
    funext j
    exact add_neg_cancel (s j)
  rw [← rowTranslationSL_add, h, rowTranslationSL_zero]

theorem rowTranslationSL_inv (s : W) :
    (rowTranslationSL s)⁻¹ = rowTranslationSL (-s) :=
  inv_eq_of_mul_eq_one_right (rowTranslationSL_neg s)

theorem conj_t_rowTranslation (s : W) :
    t * rowTranslationSL s * t = rowTranslationSL (fun j => -s j) := by
  apply Subtype.ext
  change (t : Matrix (Fin 3) (Fin 3) F) * rowTranslation s * (t : Matrix (Fin 3) (Fin 3) F) =
    rowTranslation (fun j => -s j)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t_coe, rowTranslation, Matrix.mul_apply, Fin.sum_univ_succ]

theorem commutator_t_rowTranslation (s : W) :
    ⁅t, rowTranslationSL s⁆ = rowTranslationSL (fun j => (-2 : F) * s j) := by
  rw [commutatorElement_def, t_inv, rowTranslationSL_inv, conj_t_rowTranslation,
    ← rowTranslationSL_add]
  congr 1
  funext j
  simp only [Pi.add_apply, Pi.neg_apply]
  ring_nf

theorem blockDiagSL_mem_commutator (A : SL2) :
    blockDiagSL A ∈ ⁅pointStabilizer, pointStabilizer⁆ := by
  have hSL2 : Group.IsPerfect SL2 := sl2_isPerfect
  let B : Subgroup SL3 := blockDiagHom.range
  have hBperf : Group.IsPerfect B :=
    @Group.IsPerfect.range SL2 SL3 _ _ blockDiagHom hSL2
  have hBP : B ≤ pointStabilizer := by
    rintro x ⟨A, rfl⟩
    exact blockDiagSL_mem_pointStabilizer A
  have hBle : B ≤ ⁅pointStabilizer, pointStabilizer⁆ := by
    have hBcomm : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hBperf
    rw [← hBcomm]
    exact Subgroup.commutator_mono hBP hBP
  exact hBle (MonoidHom.mem_range.mpr ⟨A, rfl⟩)

theorem rowTranslationSL_mem_commutator (r : W) :
    rowTranslationSL r ∈ ⁅pointStabilizer, pointStabilizer⁆ := by
  let s : W := fun j => 2 * r j
  have hs : (fun j => (-2 : F) * s j) = r := by
    funext j
    have h2 : (-2 : F) * 2 = 1 := by decide
    calc
      (-2 : F) * s j = (-2 * 2) * r j := by
        rw [show s j = 2 * r j from rfl, mul_assoc]
      _ = 1 * r j := by rw [h2]
      _ = r j := one_mul _
  have hcomm : ⁅t, rowTranslationSL s⁆ = rowTranslationSL r := by
    rw [commutator_t_rowTranslation, hs]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (blockDiagSL_mem_pointStabilizer diagNeg)
    (rowTranslationSL_mem_pointStabilizer s)

theorem pointStabilizer_le_commutator :
    pointStabilizer ≤ ⁅pointStabilizer, pointStabilizer⁆ := by
  intro g hg
  obtain ⟨A, r, hg_eq⟩ := eq_blockDiag_mul_rowTranslation hg
  rw [hg_eq]
  exact (⁅pointStabilizer, pointStabilizer⁆).mul_mem
    (blockDiagSL_mem_commutator A) (rowTranslationSL_mem_commutator r)

theorem pointStabilizer_commutator_le :
    ⁅pointStabilizer, pointStabilizer⁆ ≤ pointStabilizer :=
  Subgroup.commutator_le_self pointStabilizer

theorem pointStabilizer_isPerfect : Group.IsPerfect pointStabilizer :=
  Subgroup.isPerfect_iff.mpr
    (le_antisymm pointStabilizer_commutator_le pointStabilizer_le_commutator)

@[expose] def tail (v : V) : W := fun j => v (Fin.succ j)

theorem tail_ne_zero_iff {v : V} : tail v ≠ 0 ↔ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    apply h
    funext j
    fin_cases j <;> simp [tail, h'.1, h'.2]
  · rintro (h1 | h2) h
    · have := congrFun h 0
      simp [tail] at this
      exact h1 this
    · have := congrFun h 1
      simp [tail] at this
      exact h2 this

theorem rowTranslation_smul (r : W) (v : V) :
    rowTranslationSL r • v = ![v 0 + r 0 * v 1 + r 1 * v 2, v 1, v 2] := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, rowTranslationSL_coe]
  ext i
  fin_cases i <;>
    simp [rowTranslation, Matrix.mulVec, vecHead, vecTail]
  all_goals ring

theorem blockDiag_smul (A : SL2) (v : V) :
    blockDiagSL A • v = ![v 0, (A.1 *ᵥ tail v) 0, (A.1 *ᵥ tail v) 1] := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, blockDiagSL_coe]
  ext i
  fin_cases i <;>
    simp [blockDiag, tail, Matrix.mulVec, vecHead, vecTail]

theorem blockDiag_smul_e1 (B : SL2) :
    blockDiagSL B • e1 = ![0, (B.1 *ᵥ ![1, 0]) 0, (B.1 *ᵥ ![1, 0]) 1] := by
  rw [blockDiag_smul]
  have h : tail e1 = ![1, 0] := by
    ext j
    fin_cases j <;> simp [tail, e1]
  rw [h]
  simp [e1]

theorem tail_rowTranslation_smul (r : W) (v : V) :
    tail (rowTranslationSL r • v) = tail v := by
  rw [rowTranslation_smul]
  ext j
  fin_cases j <;> simp [tail]

theorem tail_blockDiag_smul (A : SL2) (v : V) :
    tail (blockDiagSL A • v) = A.1 *ᵥ tail v := by
  rw [blockDiag_smul]
  ext j
  fin_cases j <;> simp [tail]

theorem blockDiag_tail_ne_zero (A : SL2) {x : W} (hx : x ≠ 0) :
    A.1 *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have hx0 : (A⁻¹).1 *ᵥ (A.1 *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [h] at hx0
  simpa using hx0.symm

theorem exists_SL2_mulVec_single (x : W) (hx : x ≠ 0) :
    ∃ B : SL2, B.1 *ᵥ ![1, 0] = x := by
  classical
  by_cases h0 : x 0 ≠ 0
  · refine ⟨⟨!![x 0, 0; x 1, (x 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp [h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec]
  · have h0' : x 0 = 0 := by simpa using h0
    have h1 : x 1 ≠ 0 := by
      intro h1'
      apply hx
      ext i
      fin_cases i <;> simp [h0', h1']
    refine ⟨⟨!![0, -(x 1)⁻¹; x 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp [h1]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, h0']

theorem exists_rowTranslation_adjust (v : V) (hv : v 1 ≠ 0 ∨ v 2 ≠ 0) :
    ∃ r : W, rowTranslationSL r • ![0, v 1, v 2] = v := by
  by_cases h1 : v 1 ≠ 0
  · refine ⟨![v 0 / v 1, 0], ?_⟩
    rw [rowTranslation_smul]
    ext i
    fin_cases i <;> simp [h1]
  · have h2 : v 2 ≠ 0 := by
      rcases hv with h1' | h2
      · exact (h1 h1').elim
      · exact h2
    refine ⟨![0, v 0 / v 2], ?_⟩
    rw [rowTranslation_smul]
    ext i
    fin_cases i <;> simp [h2]

theorem pointStabilizer_tail_ne_zero {p : SL3} (hp : p ∈ pointStabilizer) {v : V}
    (hv : tail v ≠ 0) : tail (p • v) ≠ 0 := by
  obtain ⟨A, r, rfl⟩ := eq_blockDiag_mul_rowTranslation hp
  rw [mul_smul, tail_blockDiag_smul, tail_rowTranslation_smul]
  exact blockDiag_tail_ne_zero A hv

theorem exists_pointStabilizer_smul_e1_eq (v : V) (hv : tail v ≠ 0) :
    ∃ p : pointStabilizer, p • e1 = v := by
  obtain ⟨B, hB⟩ := exists_SL2_mulVec_single (tail v) hv
  have hB_e1 : blockDiagSL B • e1 = ![0, v 1, v 2] := by
    rw [blockDiag_smul_e1, hB]
    ext i
    fin_cases i <;> simp [tail]
  obtain ⟨r, hr⟩ := exists_rowTranslation_adjust v (tail_ne_zero_iff.mp hv)
  refine ⟨⟨rowTranslationSL r * blockDiagSL B, ?_⟩, ?_⟩
  · exact pointStabilizer.mul_mem (rowTranslationSL_mem_pointStabilizer r)
      (blockDiagSL_mem_pointStabilizer B)
  · rw [MulAction.subgroup_smul_def, mul_smul, hB_e1, hr]

theorem orbit_e1_eq :
    MulAction.orbit pointStabilizer e1 = {v : V | tail v ≠ 0} := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨p, rfl⟩
    have he1 : tail e1 ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [tail, e1] at this
    simpa [MulAction.subgroup_smul_def] using
      pointStabilizer_tail_ne_zero p.2 he1
  · intro hv
    exact exists_pointStabilizer_smul_e1_eq v hv

theorem orbit_e1_eq_compl_line :
    MulAction.orbit pointStabilizer e1 = {v : V | v 1 ≠ 0 ∨ v 2 ≠ 0} := by
  rw [orbit_e1_eq]
  ext v
  exact tail_ne_zero_iff

theorem orbit_e1_ncard : Nat.card (MulAction.orbit pointStabilizer e1) = 120 := by
  rw [orbit_e1_eq_compl_line, Nat.card_coe_set_eq]
  let L : Set V := {v : V | v 1 = 0 ∧ v 2 = 0}
  have hcompl : {v : V | v 1 ≠ 0 ∨ v 2 ≠ 0} = Lᶜ := by
    ext v
    simp [L]
    tauto
  rw [hcompl, Set.ncard_compl]
  have hV : Nat.card V = 125 := by
    rw [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hL : L.ncard = 5 := by
    have hset : L = (fun c : F => c • e0) '' (Set.univ : Set F) := by
      ext v
      constructor
      · intro hv
        have hv' : v 1 = 0 ∧ v 2 = 0 := by simpa [L] using hv
        refine ⟨v 0, Set.mem_univ _, ?_⟩
        ext i
        fin_cases i <;> simp [e0, hv'.1, hv'.2]
      · rintro ⟨c, -, rfl⟩
        simp [L, e0]
    rw [hset, Set.ncard_image_of_injective _ ?inj, Set.ncard_univ]
    · simp [F]
    · intro a b hab
      have := congrFun hab 0
      simpa [e0] using this
  omega

abbrev Vsharp := {v : V // v ≠ 0}

local instance : MulAction (GL (Fin 3) F) Vsharp where
  smul g v :=
    ⟨g • (v : V), by
      intro hv
      apply v.2
      calc
        (v : V) = (g⁻¹ : GL (Fin 3) F) • (g • (v : V)) := by
          rw [inv_smul_smul]
        _ = (g⁻¹ : GL (Fin 3) F) • (0 : V) := by rw [hv]
        _ = 0 := smul_zero _⟩
  one_smul v := by
    apply Subtype.ext
    change ((1 : GL (Fin 3) F) • (v : V)) = (v : V)
    exact one_smul _ _
  mul_smul g h v := by
    apply Subtype.ext
    change (((g * h : GL (Fin 3) F)) • (v : V)) = g • (h • (v : V))
    exact mul_smul g h (v : V)

@[expose] def e0s : Vsharp := ⟨e0, by simp [e0]⟩

@[expose] def e1s : Vsharp := ⟨e1, by simp [e1]⟩

theorem natCard_Vsharp : Nat.card Vsharp = 124 := by
  change Nat.card ({v : V | v ≠ 0} : Set V) = 124
  rw [Nat.card_coe_set_eq]
  have hcompl : {v : V | v ≠ 0} = ({0} : Set V)ᶜ := by
    ext v
    simp
  rw [hcompl, Set.ncard_compl]
  have hV : Nat.card V = 125 := by
    rw [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hzero : ({0} : Set V).ncard = 1 := by simp
  omega

theorem isPerfect_of_linear_image
    (H : Subgroup (GL (Fin 3) F))
    (hlower : ∀ g : pointStabilizer,
      Matrix.SpecialLinearGroup.toGL (g : SL3) ∈ H)
    (hupper : ∀ g ∈ H, g • e0 = e0 →
      (g : Matrix (Fin 3) (Fin 3) F).det = 1)
    (htrans : ∀ v : V, v ≠ 0 → ∃ g ∈ H, g • e0 = v) :
    Group.IsPerfect H := by
  classical
  have htransV : MulAction.IsPretransitive H Vsharp := by
    rw [MulAction.isPretransitive_iff_base e0s]
    intro x
    obtain ⟨g, hgH, hg⟩ := htrans (x : V) x.2
    refine ⟨⟨g, hgH⟩, ?_⟩
    apply Subtype.ext
    change (g • (e0 : V)) = (x : V)
    simpa [e0s] using hg
  let K : Subgroup H := MulAction.stabilizer H e0s
  let φ : pointStabilizer →* K :=
    { toFun := fun g =>
        ⟨⟨Matrix.SpecialLinearGroup.toGL (g : SL3), hlower g⟩, by
          apply Subtype.ext
          have hg : (g : SL3) • e0 = e0 :=
            MulAction.mem_stabilizer_iff.mp
              (show (g : SL3) ∈ MulAction.stabilizer SL3 e0 from g.2)
          change (Matrix.SpecialLinearGroup.toGL (g : SL3) • (e0 : V)) = e0
          simpa [e0s, Units.smul_def, Matrix.SpecialLinearGroup.smul_def,
            Matrix.smul_eq_mulVec, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hg⟩
      map_one' := by ext; rfl
      map_mul' := by intro g h; ext; rfl }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨h, hhK⟩
    have hhK' : h • e0s = e0s := by
      simpa [K, MulAction.mem_stabilizer_iff] using hhK
    have hfix : (h : GL (Fin 3) F) • e0 = e0 := by
      have := congrArg (fun x : Vsharp => (x : V)) hhK'
      change ((h : H) : GL (Fin 3) F) • (e0 : V) = e0 at this
      simpa [MulAction.subgroup_smul_def, e0s] using this
    have hdet : ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
      hupper (h : GL (Fin 3) F) h.2 hfix
    have hdetUnit : Matrix.GeneralLinearGroup.det (h : GL (Fin 3) F) = 1 := by
      ext
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using hdet
    have hker : (h : GL (Fin 3) F) ∈
        (Matrix.SpecialLinearGroup.toGL : SL3 →* GL (Fin 3) F).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact MonoidHom.mem_ker.mpr hdetUnit
    obtain ⟨s, hs⟩ := hker
    refine ⟨⟨s, ?_⟩, ?_⟩
    · rw [pointStabilizer, MulAction.mem_stabilizer_iff]
      change (s : SL3) • e0 = e0
      have hmat : (s : Matrix (Fin 3) (Fin 3) F) =
          ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [← hs, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      rw [Matrix.SpecialLinearGroup.smul_def, hmat]
      simpa [Units.smul_def, Matrix.smul_eq_mulVec, e0] using hfix
    · apply Subtype.ext
      apply Subtype.ext
      exact hs
  have hKperfect : Group.IsPerfect K :=
    @Group.IsPerfect.ofSurjective pointStabilizer K _ _ φ
      pointStabilizer_isPerfect hφsurj
  have hOrbitCard : Nat.card (MulAction.orbit K e1s) = 120 := by
    have hset : (MulAction.orbit K e1s : Set Vsharp) =
        {x : Vsharp | (x : V) ∈
          (MulAction.orbit pointStabilizer e1 : Set V)} := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        obtain ⟨s, hs⟩ := hφsurj k
        refine ⟨s, ?_⟩
        rw [← hs]
        rfl
      · rintro ⟨s, hsO⟩
        refine ⟨φ s, ?_⟩
        apply Subtype.ext
        rw [← hsO]
        rfl
    rw [Nat.card_coe_set_eq, hset]
    rw [Set.ncard_subtype]
    have hOsub : (MulAction.orbit pointStabilizer e1 : Set V) ⊆ {v : V | v ≠ 0} := by
      intro v hv
      have hv' : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
        simpa [orbit_e1_eq_compl_line] using hv
      intro hzero
      rcases hv' with h1 | h2
      · exact h1 (by rw [hzero]; rfl)
      · exact h2 (by rw [hzero]; rfl)
    rw [Set.inter_eq_left.mpr hOsub]
    rw [← Nat.card_coe_set_eq]
    exact orbit_e1_ncard
  have hbig : ∃ y : Vsharp,
      2 * Nat.card (MulAction.orbit K y) > Nat.card Vsharp := by
    refine ⟨e1s, ?_⟩
    rw [hOrbitCard, natCard_Vsharp]
    norm_num
  exact CFSG.GroupTheory.isPerfect_of_isPerfect_stabilizer_of_large_orbit
    (G := H) (X := Vsharp) e0s hKperfect hbig

theorem transitive_of_pointStabilizer_of_move
    (H : Subgroup (GL (Fin 3) F))
    (hlower : ∀ g : pointStabilizer, SpecialLinearGroup.toGL (g : SL3) ∈ H)
    (hmove : ∃ m ∈ H, m • e0 = e1) :
    ∀ v : V, v ≠ 0 → ∃ g ∈ H, g • e0 = v := by
  classical
  obtain ⟨m, hm, hme⟩ := hmove
  have hcompat (g : SL3) (v : V) : SpecialLinearGroup.toGL g • v = g • v := by
    simp only [Units.smul_def, Matrix.smul_eq_mulVec,
      SpecialLinearGroup.smul_def, SpecialLinearGroup.coe_GL_coe_matrix]
  have hout (u w : V) (hu : tail u ≠ 0) (hw : tail w ≠ 0) :
      ∃ s ∈ H, s • u = w := by
    obtain ⟨su, hsu⟩ := exists_pointStabilizer_smul_e1_eq u hu
    obtain ⟨sw, hsw⟩ := exists_pointStabilizer_smul_e1_eq w hw
    let gu := SpecialLinearGroup.toGL (su : SL3)
    let gw := SpecialLinearGroup.toGL (sw : SL3)
    have hgu : gu • e1 = u := (hcompat _ _).trans hsu
    have hgw : gw • e1 = w := (hcompat _ _).trans hsw
    refine ⟨gw * gu⁻¹, H.mul_mem (hlower sw) (H.inv_mem (hlower su)), ?_⟩
    rw [mul_smul, ← hgu, inv_smul_smul, hgw]
  have he1 : tail e1 ≠ 0 := tail_ne_zero_iff.mpr (Or.inl (by simp [e1]))
  intro v hv
  by_cases hvout : tail v ≠ 0
  · obtain ⟨s, hs, hse⟩ := hout e1 v he1 hvout
    exact ⟨s * m, H.mul_mem hs hm, by rw [mul_smul, hme, hse]⟩
  · have hv12 : v 1 = 0 ∧ v 2 = 0 := by
      have ht : tail v = 0 := not_ne_iff.mp hvout
      constructor
      · exact congrFun ht 0
      · exact congrFun ht 1
    have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      fin_cases i <;> simp [h0, hv12.1, hv12.2]
    let u : V := m⁻¹ • v
    have hu : tail u ≠ 0 := by
      intro htail
      have hu0 : u = u 0 • e0 := by
        have h1 : u 1 = 0 := congrFun htail 0
        have h2 : u 2 = 0 := congrFun htail 1
        ext i
        fin_cases i <;> simp [e0, h1, h2]
      have hv' : v = u 0 • e1 := by
        calc v = m • u := (smul_inv_smul m v).symm
          _ = m • (u 0 • e0) := congrArg (fun x : V => m • x) hu0
          _ = u 0 • (m • e0) := by
            change (m : Matrix (Fin 3) (Fin 3) F) *ᵥ (u 0 • e0) =
              u 0 • ((m : Matrix (Fin 3) (Fin 3) F) *ᵥ e0)
            exact Matrix.mulVec_smul _ _ _
          _ = u 0 • e1 := by rw [hme]
      apply hv0
      have h := congrFun hv' 0
      simpa [e1] using h
    obtain ⟨s, hs, hsu⟩ := hout e1 u he1 hu
    refine ⟨m * s * m, H.mul_mem (H.mul_mem hm hs) hm, ?_⟩
    rw [mul_smul, mul_smul, hme, hsu]
    exact smul_inv_smul m v

end CFSG.GroupTheory.SL3Five
