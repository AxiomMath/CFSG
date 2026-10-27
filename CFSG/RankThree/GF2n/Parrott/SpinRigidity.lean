module

public import CFSG.RankThree.GF2n.Parrott.SpinRigidityBridge
public import CFSG.RankThree.GF2n.Parrott.SpinActionA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)


namespace SpinRigid

@[expose] noncomputable def spinMat : A45 →* Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 8) (Fin 8) (ZMod 2))).comp rhoA

theorem spinMat_apply (a : A45) :
    spinMat a = ((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := rfl

theorem spinMat_spinGenA (i : Fin 3) : colsOf (spinMat (spinGenA i)) = b3 i := by
  fin_cases i
  · have h : spinMat (spinGenA 0) = Mx := congrArg Units.val rhoA_x
    show colsOf (spinMat (spinGenA 0)) = b3 0
    rw [h, colsOf_Mx]
  · have h : spinMat (spinGenA 1) = My := congrArg Units.val rhoA_y
    show colsOf (spinMat (spinGenA 1)) = b3 1
    rw [h, colsOf_My]
  · have h : spinMat (spinGenA 2) = Mf := congrArg Units.val rhoA_f
    show colsOf (spinMat (spinGenA 2)) = b3 2
    rw [h, colsOf_Mf]

theorem colsOf_spinMat_word (w : List (Fin 3 × ℕ)) :
    colsOf (spinMat (evalSpinWord spinGenA w)) = evalB b3 w := by
  rw [map_evalSpinWord]
  exact colsOf_evalSpinWord _ b3 spinMat_spinGenA w

theorem colsOf_spinMat_G5 (i : Fin 5) : colsOf (spinMat (spinG5 i)) = gb i := by
  rw [spinG5_eq, colsOf_spinMat_word]
  fin_cases i
  · exact evalB_g5words_zero
  all_goals rfl

@[expose] noncomputable def G5M (i : Fin 5) : Matrix (Fin 8) (Fin 8) (ZMod 2) := spinMat (spinG5 i)

theorem colsOf_G5M (i : Fin 5) : colsOf (G5M i) = gb i := colsOf_spinMat_G5 i

theorem colsOf_spinMat_G5word (w : List (Fin 5 × ℕ)) :
    colsOf (spinMat (evalSpinWord spinG5 w)) = evalB gb w := by
  rw [map_evalSpinWord]
  exact colsOf_evalSpinWord _ gb colsOf_spinMat_G5 w

theorem commutantM_param (X : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (hX : ∀ j : Fin 5, 2 ≤ (j : ℕ) → X * G5M j = G5M j * X) :
    colsOf X = xc (bitmask (X *ᵥ vecOfNat v0)) := by
  have hT : ∀ k : Fin 8,
      colsOf (spinMat (evalSpinWord spinG5 (mWord (mTrip k)))) = tcM k := fun k =>
    colsOf_spinMat_G5word _
  have hC : ∀ k : Fin 8, X * spinMat (evalSpinWord spinG5 (mWord (mTrip k))) =
      spinMat (evalSpinWord spinG5 (mWord (mTrip k))) * X := by
    intro k
    rw [map_evalSpinWord]
    apply commute_evalSpinWord X (fun i => spinMat (spinG5 i)) (mWord (mTrip k))
    intro l hl
    simp only [mWord, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact hX 2 (by decide)
    · exact hX 3 (by decide)
    · exact hX 4 (by decide)
  exact commutant_param (fun k => spinMat (evalSpinWord spinG5 (mWord (mTrip k)))) tcM hT
    v0 (by decide) b0inv b0inv_bnd b0_inv X hC

theorem comm_of_norm (ρ : A45 →* GL8)
    (hM : ∀ j : Fin 5, 2 ≤ (j : ℕ) → ρ (spinG5 j) = rhoA (spinG5 j))
    (p : Fin 5 × Fin 5 × (ℕ × ℕ × ℕ)) (hp : p ∈ normData) :
    ((rhoA (spinG5 p.1))⁻¹ * ρ (spinG5 p.1)) * rhoA (spinG5 p.2.1) =
      rhoA (spinG5 p.2.1) * ((rhoA (spinG5 p.1))⁻¹ * ρ (spinG5 p.1)) := by
  have hn := spinG5_norm p hp
  have hW : ρ (evalSpinWord spinG5 (mWord p.2.2)) = rhoA (evalSpinWord spinG5 (mWord p.2.2)) := by
    rw [map_evalSpinWord, map_evalSpinWord]
    exact evalSpinWord_congr_mem _ _ _ fun l hl => hM l.1 (mWord_gen _ l hl)
  have hρ : ρ (spinG5 p.1) * rhoA (spinG5 p.2.1) =
      rhoA (evalSpinWord spinG5 (mWord p.2.2)) * ρ (spinG5 p.1) := by
    rw [← hM p.2.1 (normData_j p hp), ← hW, ← map_mul, ← map_mul, hn]
  have hσ : rhoA (spinG5 p.1) * rhoA (spinG5 p.2.1) =
      rhoA (evalSpinWord spinG5 (mWord p.2.2)) * rhoA (spinG5 p.1) := by
    rw [← map_mul, ← map_mul, hn]
  generalize rhoA (spinG5 p.1) = a at hσ ⊢
  generalize rhoA (spinG5 p.2.1) = m at hρ hσ ⊢
  generalize rhoA (evalSpinWord spinG5 (mWord p.2.2)) = W at hρ hσ ⊢
  generalize ρ (spinG5 p.1) = r at hρ ⊢
  have e1 : a⁻¹ * W = m * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hσ, mul_assoc, mul_inv_cancel, mul_one]
  calc a⁻¹ * r * m = a⁻¹ * (r * m) := mul_assoc _ _ _
    _ = a⁻¹ * (W * r) := by rw [hρ]
    _ = (a⁻¹ * W) * r := (mul_assoc _ _ _).symm
    _ = (m * a⁻¹) * r := by rw [e1]
    _ = m * (a⁻¹ * r) := mul_assoc _ _ _

theorem stage1 (ρ : A45 →* GL8)
    (hM : ∀ j : Fin 5, 2 ≤ (j : ℕ) → ρ (spinG5 j) = rhoA (spinG5 j)) :
    ∃ u : GL8, (∀ j : Fin 5, 2 ≤ (j : ℕ) → u * rhoA (spinG5 j) = rhoA (spinG5 j) * u) ∧
      ρ (spinG5 0) * u = u * rhoA (spinG5 0) := by
  set c : GL8 := (rhoA (spinG5 0))⁻¹ * ρ (spinG5 0) with hc
  have hcomm : ∀ j : Fin 5, 2 ≤ (j : ℕ) → c * rhoA (spinG5 j) = rhoA (spinG5 j) * c := by
    intro j hj
    have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
      revert j
      decide
    rcases hj' with rfl | rfl | rfl
    · exact comm_of_norm ρ hM (0, 2, (1, 0, 0)) (by simp [normData])
    · exact comm_of_norm ρ hM (0, 3, (0, 1, 0)) (by simp [normData])
    · exact comm_of_norm ρ hM (0, 4, (0, 0, 2)) (by simp [normData])
  have hX : ∀ j : Fin 5, 2 ≤ (j : ℕ) →
      (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) * G5M j = G5M j * c := fun j hj =>
    val_comm (hcomm j hj)
  have hpar := commutantM_param (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) hX
  set w := bitmask ((c : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ vecOfNat v0) with hw
  have hw256 : w < 256 := bitmask_lt _
  have hxc : rhoA (spinG5 0) * c = ρ (spinG5 0) := by rw [hc, mul_inv_cancel_left]
  have hxx : ρ (spinG5 0) * ρ (spinG5 0) = 1 := by
    rw [← map_mul]
    exact (congrArg ρ spin_x_sq).trans (map_one ρ)
  have h1 : G5M 0 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      ((ρ (spinG5 0) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
    have := congrArg Units.val hxc
    rw [Units.val_mul] at this
    exact this
  have hmat : ((G5M 0 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2))) *
      (G5M 0 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2)))) = 1 := by
    rw [h1, ← Units.val_mul, hxx, Units.val_one]
  have hbit : bmul (bmul (b3 0) (xc w)) (bmul (b3 0) (xc w)) = bone := by
    have := congrArg colsOf hmat
    rw [colsOf_mul, colsOf_mul, colsOf_one, colsOf_G5M, hpar] at this
    exact this
  obtain ⟨w₀, hok, hcom⟩ := spec1 w hw256 hbit
  obtain ⟨U, hU⟩ := exists_colsOf (xc w₀) (bnd_xc w₀)
  simp only [okWit, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hcube, hc1⟩, hc2⟩, hc3⟩ := hok
  have hU3 : U ^ 3 = 1 := by
    apply colsOf_injective
    rw [colsOf_pow, hU, colsOf_one]
    exact hcube
  obtain ⟨u, hu⟩ := exists_unit_of_cube hU3
  have hUj : ∀ j : Fin 5, 2 ≤ (j : ℕ) → U * G5M j = G5M j * U := by
    intro j hj
    have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
      revert j
      decide
    apply colsOf_injective
    rw [colsOf_mul, colsOf_mul, hU, colsOf_G5M]
    rcases hj' with rfl | rfl | rfl
    · exact hc1
    · exact hc2
    · exact hc3
  refine ⟨u, fun j hj => Units.ext ?_, Units.ext ?_⟩
  · rw [Units.val_mul, Units.val_mul, hu]
    exact hUj j hj
  · rw [Units.val_mul, Units.val_mul, hu, ← h1]
    show (G5M 0 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2))) * U = U * G5M 0
    apply colsOf_injective
    rw [colsOf_mul, colsOf_mul, colsOf_mul, hU, colsOf_G5M, hpar]
    exact hcom

theorem rho_eq_word (ρ : A45 →* GL8) (hall : ∀ i : Fin 5, ρ (spinG5 i) = rhoA (spinG5 i))
    (w : List (Fin 5 × ℕ)) : ρ (evalSpinWord spinG5 w) = rhoA (evalSpinWord spinG5 w) :=
  evalSpinWord_congr ρ rhoA spinG5 hall w

theorem stage3 (ρ : A45 →* GL8)
    (hM : ∀ j : Fin 5, 2 ≤ (j : ℕ) → ρ (spinG5 j) = rhoA (spinG5 j))
    (hx : ρ (spinG5 0) = rhoA (spinG5 0)) :
    ∃ u : GL8, (∀ j : Fin 5, 2 ≤ (j : ℕ) → u * rhoA (spinG5 j) = rhoA (spinG5 j) * u) ∧
      u * rhoA (spinG5 0) = rhoA (spinG5 0) * u ∧ ρ (spinG5 1) * u = u * rhoA (spinG5 1) := by
  set c : GL8 := (rhoA (spinG5 1))⁻¹ * ρ (spinG5 1) with hc
  have hcomm : ∀ j : Fin 5, 2 ≤ (j : ℕ) → c * rhoA (spinG5 j) = rhoA (spinG5 j) * c := by
    intro j hj
    have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
      revert j
      decide
    rcases hj' with rfl | rfl | rfl
    · exact comm_of_norm ρ hM (1, 2, (0, 2, 0)) (by simp [normData])
    · exact comm_of_norm ρ hM (1, 3, (2, 2, 1)) (by simp [normData])
    · exact comm_of_norm ρ hM (1, 4, (0, 1, 1)) (by simp [normData])
  have hX : ∀ j : Fin 5, 2 ≤ (j : ℕ) →
      (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) * G5M j = G5M j * c := fun j hj =>
    val_comm (hcomm j hj)
  have hpar := commutantM_param (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) hX
  set w := bitmask ((c : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ vecOfNat v0) with hw
  have hw256 : w < 256 := bitmask_lt _
  have hnc : rhoA (spinG5 1) * c = ρ (spinG5 1) := by rw [hc, mul_inv_cancel_left]
  have h1 : G5M 1 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      ((ρ (spinG5 1) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
    have := congrArg Units.val hnc
    rw [Units.val_mul] at this
    exact this
  let ρM : A45 →* Matrix (Fin 8) (Fin 8) (ZMod 2) := (Units.coeHom _).comp ρ
  have hrel : evalSpinWord (fun i => ρM (spinG5 i)) rN = 1 := by
    rw [← map_evalSpinWord ρM, spinG5_rN, map_one]
  have hcol : ∀ i : Fin 5, colsOf (ρM (spinG5 i)) = gP (bmul bN2 (xc w)) i := by
    intro i
    have hM' : ∀ j : Fin 5, 2 ≤ (j : ℕ) → ρM (spinG5 j) = G5M j := fun j hj => by
      show ((ρ (spinG5 j) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = _
      rw [hM j hj]
      rfl
    fin_cases i
    · show colsOf (ρM (spinG5 0)) = b3 0
      have : ρM (spinG5 0) = G5M 0 := by
        show ((ρ (spinG5 0) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = _
        rw [hx]
        rfl
      rw [this, colsOf_G5M]
      rfl
    · show colsOf (ρM (spinG5 1)) = bmul bN2 (xc w)
      have : ρM (spinG5 1) = G5M 1 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) := h1.symm
      rw [this, colsOf_mul, colsOf_G5M, hpar]
      rfl
    · show colsOf (ρM (spinG5 2)) = bM1
      rw [hM' 2 (by decide), colsOf_G5M]
      rfl
    · show colsOf (ρM (spinG5 3)) = bM2
      rw [hM' 3 (by decide), colsOf_G5M]
      rfl
    · show colsOf (ρM (spinG5 4)) = bM3
      rw [hM' 4 (by decide), colsOf_G5M]
      rfl
  have hbit : evalB (gP (bmul bN2 (xc w))) rN = bone := by
    rw [← colsOf_evalSpinWord (fun i => ρM (spinG5 i)) _ hcol, hrel, colsOf_one]
  obtain ⟨w₀, hok, hcx, hcom⟩ := spec3 w hw256 hbit
  obtain ⟨U, hU⟩ := exists_colsOf (xc w₀) (bnd_xc w₀)
  simp only [okWit, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hcube, hc1⟩, hc2⟩, hc3⟩ := hok
  have hU3 : U ^ 3 = 1 := by
    apply colsOf_injective
    rw [colsOf_pow, hU, colsOf_one]
    exact hcube
  obtain ⟨u, hu⟩ := exists_unit_of_cube hU3
  have hUj : ∀ j : Fin 5, 2 ≤ (j : ℕ) → U * G5M j = G5M j * U := by
    intro j hj
    have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
      revert j
      decide
    apply colsOf_injective
    rw [colsOf_mul, colsOf_mul, hU, colsOf_G5M]
    rcases hj' with rfl | rfl | rfl
    · exact hc1
    · exact hc2
    · exact hc3
  refine ⟨u, fun j hj => Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [Units.val_mul, Units.val_mul, hu]
    exact hUj j hj
  · rw [Units.val_mul, Units.val_mul, hu]
    show U * G5M 0 = G5M 0 * U
    apply colsOf_injective
    rw [colsOf_mul, colsOf_mul, hU, colsOf_G5M]
    exact hcx
  · rw [Units.val_mul, Units.val_mul, hu, ← h1]
    show (G5M 1 * (c : Matrix (Fin 8) (Fin 8) (ZMod 2))) * U = U * G5M 1
    apply colsOf_injective
    rw [colsOf_mul, colsOf_mul, colsOf_mul, hU, colsOf_G5M, hpar]
    exact hcom

theorem stage4 (ρ : A45 →* GL8) (hall : ∀ i : Fin 5, ρ (spinG5 i) = rhoA (spinG5 i)) :
    ρ (spinGenA 1) = rhoA (spinGenA 1) := by
  set c : GL8 := (rhoA (spinGenA 1))⁻¹ * ρ (spinGenA 1) with hc
  have hcomm : ∀ i : Fin 8, c * rhoA (evalSpinWord spinG5 (st4 i).1) =
      rhoA (evalSpinWord spinG5 (st4 i).1) * c := by
    intro i
    have hn := spinG5_st4 i
    have hρ : ρ (spinGenA 1) * rhoA (evalSpinWord spinG5 (st4 i).1) =
        rhoA (evalSpinWord spinG5 (st4 i).2) * ρ (spinGenA 1) := by
      rw [← rho_eq_word ρ hall, ← rho_eq_word ρ hall, ← map_mul, ← map_mul, hn]
    have hσ : rhoA (spinGenA 1) * rhoA (evalSpinWord spinG5 (st4 i).1) =
        rhoA (evalSpinWord spinG5 (st4 i).2) * rhoA (spinGenA 1) := by
      rw [← map_mul, ← map_mul, hn]
    exact comm_of_relations _ _ _ _ hρ hσ
  have hT : ∀ i : Fin 8, colsOf (spinMat (evalSpinWord spinG5 (st4 i).1)) = tlF i :=
    fun i => colsOf_spinMat_G5word _
  have hX : ∀ i : Fin 8, (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
      spinMat (evalSpinWord spinG5 (st4 i).1) =
      spinMat (evalSpinWord spinG5 (st4 i).1) * c := fun i => val_comm (hcomm i)
  have hpar := commutant_param (fun i => spinMat (evalSpinWord spinG5 (st4 i).1)) tlF hT vL
    (by decide) bLinv bLinv_bnd bL_inv (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) hX
  set w := bitmask ((c : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ vecOfNat vL) with hw
  have hw256 : w < 256 := bitmask_lt _
  have hxy : rhoA (spinGenA 1) * c = ρ (spinGenA 1) := by rw [hc, mul_inv_cancel_left]
  have hx : ρ (spinGenA 0) = rhoA (spinGenA 0) := hall 0
  have hrel : (ρ (spinGenA 0) * ρ (spinGenA 1)) ^ 9 = 1 := by
    rw [← map_mul, ← map_pow, spin_xy9, map_one]
  have hmat : (spinMat (spinGenA 0) * (spinMat (spinGenA 1) *
      (c : Matrix (Fin 8) (Fin 8) (ZMod 2)))) ^ 9 = 1 := by
    have h1 : spinMat (spinGenA 1) * (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        ((ρ (spinGenA 1) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      have := congrArg Units.val hxy
      rw [Units.val_mul] at this
      exact this
    have h0 : spinMat (spinGenA 0) =
        ((ρ (spinGenA 0) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      rw [hx]
      rfl
    rw [h1, h0, ← Units.val_mul, ← Units.val_pow_eq_pow_val, hrel, Units.val_one]
  have hbit : bpow (bmul (b3 0) (bmul (b3 1) (yc w))) 9 = bone := by
    have := congrArg colsOf hmat
    rw [colsOf_pow, colsOf_mul, colsOf_mul, colsOf_one, spinMat_spinGenA, spinMat_spinGenA,
      hpar] at this
    exact this
  have hcw : ∀ i : Fin 8, bmul (yc w) (tlF i) = bmul (tlF i) (yc w) := by
    intro i
    have := congrArg colsOf (hX i)
    rw [colsOf_mul, colsOf_mul, hpar, hT] at this
    exact this
  have h1 := spec4 w hw256 hcw hbit
  have hc1 : (c : Matrix (Fin 8) (Fin 8) (ZMod 2)) = 1 := by
    apply colsOf_injective
    rw [hpar]
    exact h1.trans colsOf_one.symm
  have hc1' : c = 1 := Units.ext hc1
  rw [← hxy, hc1', mul_one]

end SpinRigid

theorem spinRep_rigid (ρ : A45 →* GL8) (h₁ : ρ spinE27a = rhoA spinE27a)
    (h₂ : ρ spinE27b = rhoA spinE27b) (h₃ : ρ spinE27c = rhoA spinE27c) :
    ∃ P : GL8, ∀ a : A45, ρ a = P * rhoA a * P⁻¹ := by
  have hM : ∀ j : Fin 5, 2 ≤ (j : ℕ) → ρ (spinG5 j) = rhoA (spinG5 j) := by
    intro j hj
    have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
      revert j
      decide
    rcases hj' with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  obtain ⟨u₁, hu₁c, hu₁x⟩ := stage1 ρ hM
  have hρ₁M : ∀ j : Fin 5, 2 ≤ (j : ℕ) → conjRep u₁ ρ (spinG5 j) = rhoA (spinG5 j) :=
    fun j hj => conjRep_eq_of_comm (hM j hj) (hu₁c j hj)
  have hρ₁x : conjRep u₁ ρ (spinG5 0) = rhoA (spinG5 0) := conjRep_eq_of_mul hu₁x
  obtain ⟨u₂, hu₂c, hu₂x, hu₂n⟩ := stage3 (conjRep u₁ ρ) hρ₁M hρ₁x
  have hρ₂ : ∀ i : Fin 5, conjRep u₂ (conjRep u₁ ρ) (spinG5 i) = rhoA (spinG5 i) := by
    intro i
    fin_cases i
    · exact conjRep_eq_of_comm hρ₁x hu₂x
    · exact conjRep_eq_of_mul hu₂n
    · exact conjRep_eq_of_comm (hρ₁M 2 (by decide)) (hu₂c 2 (by decide))
    · exact conjRep_eq_of_comm (hρ₁M 3 (by decide)) (hu₂c 3 (by decide))
    · exact conjRep_eq_of_comm (hρ₁M 4 (by decide)) (hu₂c 4 (by decide))
  have hy := stage4 _ hρ₂
  have hf : conjRep u₂ (conjRep u₁ ρ) (spinGenA 2) = rhoA (spinGenA 2) := by
    rw [spin_f_word]
    simp only [map_mul, map_pow]
    rw [hy]
    exact congrArg₂ _ (congrArg₂ _ (congrArg₂ _ (congrArg₂ _ rfl (hρ₂ 1)) rfl) (hρ₂ 0)) rfl
  have heq : conjRep u₂ (conjRep u₁ ρ) = rhoA := by
    apply hom_ext_spinGenA
    intro i
    fin_cases i
    · exact hρ₂ 0
    · exact hy
    · exact hf
  refine ⟨u₁ * u₂, fun a => ?_⟩
  have h := DFunLike.congr_fun heq a
  rw [conjRep_apply, conjRep_apply] at h
  rw [← h]
  group

theorem spinRep_rigid_of_forall (ρ : A45 →* GL8) (h : ∀ m ∈ spinE27, ρ m = rhoA m) :
    ∃ P : GL8, ∀ a : A45, ρ a = P * rhoA a * P⁻¹ :=
  spinRep_rigid ρ (h _ (Subgroup.subset_closure (by simp)))
    (h _ (Subgroup.subset_closure (by simp))) (h _ (Subgroup.subset_closure (by simp)))

end CFSG.RankThree.GF2n.Parrott
