module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def locD (a b : Bool) (i : ℕ) (r t : Fˣ) : Fin (locDim a b) → F :=
  match a, b with
  | false, false => fun _ => 1
  | true, false => ![frK F i (r : F), frK F i (t : F), frK F i (((r * t)⁻¹ : Fˣ) : F)]
  | false, true => ![frK F i ((r⁻¹ : Fˣ) : F), frK F i ((t⁻¹ : Fˣ) : F),
      frK F i ((r * t : Fˣ) : F)]
  | true, true => ![frK F i ((r : F) * ((r * t : Fˣ) : F)), frK F i ((t : F) * ((r * t : Fˣ) : F)),
      1, frK F i ((r : F) * ((t⁻¹ : Fˣ) : F)), 1, frK F i ((t : F) * ((r⁻¹ : Fˣ) : F)),
      frK F i ((((r * t)⁻¹ : Fˣ) : F) * ((t⁻¹ : Fˣ) : F)),
      frK F i ((((r * t)⁻¹ : Fˣ) : F) * ((r⁻¹ : Fˣ) : F))]

theorem twistMat_dT_diagonal (i : ℕ) (r t : Fˣ) :
    twistMat F i (dT r t) = Matrix.diagonal
      ![frK F i (r : F), frK F i (t : F), frK F i (((r * t)⁻¹ : Fˣ) : F)] := by
  rw [twistMat_dT]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem co_conjMat_dT (i : ℕ) (r t : Fˣ) (c : Fin 8 → F) (j : Fin 8) :
    co (conjMat F i (dT r t) (Xm c)) j = locD true true i r t j * c j := by
  have h : ((r⁻¹ * t⁻¹)⁻¹ : Fˣ) = r * t := by rw [mul_inv_rev, inv_inv, inv_inv, mul_comm]
  have hr : frK F i (r : F) ≠ 0 := (map_ne_zero (frK F i)).mpr r.ne_zero
  have ht : frK F i (t : F) ≠ 0 := (map_ne_zero (frK F i)).mpr t.ne_zero
  rw [conjMat, dT_inv, twistMat_dT, twistMat_dT, h]
  fin_cases j <;> simp [co, Xm, locD, Matrix.mul_apply, Fin.sum_univ_three, map_mul] <;>
    field_simp

theorem adjRep_dT_apply (i : ℕ) (r t : Fˣ) (j s : Fin 8) :
    adjRep F i (dT r t) j s = if j = s then locD true true i r t j else 0 := by
  rw [adjRep_apply, co_conjMat_dT]
  by_cases hjs : j = s
  · subst hjs
    simp
  · simp [hjs]

theorem locRep_dT (a b : Bool) (i : ℕ) (r t : Fˣ) :
    locRep F a b i (dT r t) = Matrix.diagonal (locD a b i r t) := by
  have hinv : ((r⁻¹ * t⁻¹)⁻¹ : Fˣ) = r * t := by rw [mul_inv_rev, inv_inv, inv_inv, mul_comm]
  cases a <;> cases b
  · show (1 : Matrix (Fin 1) (Fin 1) F) = Matrix.diagonal fun _ => 1
    exact (Matrix.diagonal_one).symm
  · show (twistMat F i (dT r t)⁻¹)ᵀ = Matrix.diagonal ![frK F i ((r⁻¹ : Fˣ) : F),
      frK F i ((t⁻¹ : Fˣ) : F), frK F i ((r * t : Fˣ) : F)]
    rw [dT_inv, twistMat_dT_diagonal, Matrix.diagonal_transpose, hinv]
  · exact twistMat_dT_diagonal i r t
  · show (adjRep F i (dT r t) : Matrix (Fin 8) (Fin 8) F) =
      Matrix.diagonal (fun j : Fin 8 => locD true true i r t j)
    ext j s
    rw [adjRep_dT_apply, Matrix.diagonal_apply]

omit [CharP F 2] in
theorem kron_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, DecidableEq (κ i)] (d : ∀ i, κ i → F) :
    kron (fun i => Matrix.diagonal (d i)) = Matrix.diagonal (fun x => ∏ i, d i (x i)) := by
  ext x' x
  rw [kron_apply]
  by_cases h : x' = x
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x' i ≠ x i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

theorem tensorRep_dT {f : ℕ} (a b : Fin f → Bool) (r t : Fˣ) :
    tensorRep (F := F) F a b (dT r t) =
      Matrix.diagonal (fun x : TIdx f a b => ∏ i, locD (a i) (b i) (i : ℕ) r t (x i)) := by
  show kron (fun i : Fin f => locRep F (a i) (b i) (i : ℕ) (dT r t)) = _
  simp only [locRep_dT]
  exact kron_diagonal _

omit [CharP F 2] in
theorem card_fixed_diagonal [Fintype F] [DecidableEq F] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d : κ → F) :
    Nat.card {v : κ → F // Matrix.diagonal d *ᵥ v = v} =
      Fintype.card F ^ Fintype.card {x // d x = 1} := by
  classical
  have key : ∀ v : κ → F, Matrix.diagonal d *ᵥ v = v ↔ ∀ x, d x ≠ 1 → v x = 0 := by
    intro v
    rw [funext_iff]
    simp only [Matrix.mulVec_diagonal]
    constructor
    · intro h x hx
      have h1 := h x
      have h2 : (d x - 1) * v x = 0 := by rw [sub_mul, one_mul, h1, sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3) hx
      · exact h3
    · intro h x
      by_cases hx : d x = 1
      · simp [hx]
      · simp [h x hx]
  let e : {v : κ → F // Matrix.diagonal d *ᵥ v = v} ≃ ({x // d x = 1} → F) :=
    { toFun := fun v x => (v : κ → F) x
      invFun := fun w => ⟨fun x => if h : d x = 1 then w ⟨x, h⟩ else 0,
        (key _).mpr fun x hx => by simp [hx]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext x
        by_cases hx : d x = 1
        · simp [hx]
        · simp [hx, (key v).mp v.2 x hx]
      right_inv := fun w => by
        funext x
        simp [x.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

theorem three_dvd_of_center {f : ℕ} (a b : Fin f → Bool)
    {ω : Fˣ} (hω : orderOf ω = 3) (h1 : tensorRep (F := F) F a b (dT ω ω) = 1) :
    3 ∣ mBits a + 2 * mBits b := by
  have h := tensorRep_dT_hw F a b ω ω
  rw [h1, Matrix.one_mulVec] at h
  have h2 : ((ω : F) ^ (mBits a + 2 * mBits b) - 1) • hw F a b = 0 := by
    rw [sub_smul, one_smul]
    have e : (ω : F) ^ (mBits a + 2 * mBits b) = algebraMap F F (ω : F) ^ (mBits a + mBits b) *
        algebraMap F F (ω : F) ^ mBits b := by
      rw [Algebra.algebraMap_self, RingHom.id_apply, ← pow_add]
      ring_nf
    rw [e, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have h4 : ω ^ (mBits a + 2 * mBits b) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact sub_eq_zero.mp h3)
    rw [← hω]
    exact orderOf_dvd_of_pow_eq_one h4
  · exact absurd h3 (hw_ne_zero F a b)

@[expose] def locE : (a b : Bool) → Fin (locDim a b) → ℕ
  | false, false => fun _ => 0
  | true, false => ![0, 1, 2]
  | false, true => ![0, 2, 1]
  | true, true => ![1, 2, 0, 2, 0, 1, 1, 2]

theorem locD_eq_frK (a b : Bool) (i : ℕ) (r t : Fˣ) (y : Fin (locDim a b)) :
    locD a b i r t y = frK F i (locD a b 0 r t y) := by
  cases a <;> cases b
  · simp [locD]
  · revert y
    show ∀ y : Fin 3, locD false true i r t y = frK F i (locD false true 0 r t y)
    intro y
    fin_cases y <;> simp [locD, frK_apply]
  · revert y
    show ∀ y : Fin 3, locD true false i r t y = frK F i (locD true false 0 r t y)
    intro y
    fin_cases y <;> simp [locD, frK_apply]
  · revert y
    show ∀ y : Fin 8, locD true true i r t y = frK F i (locD true true 0 r t y)
    intro y
    fin_cases y <;> simp [locD, frK_apply]

theorem locD_zero_one (a b : Bool) {ω : Fˣ} (hω : (ω : F) ^ 3 = 1) (y : Fin (locDim a b)) :
    locD a b 0 1 ω y = (ω : F) ^ locE a b y := by
  have hinv : ((ω⁻¹ : Fˣ) : F) = (ω : F) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hω)
  cases a <;> cases b
  · simp [locD, locE]
  · revert y
    show ∀ y : Fin 3, locD false true 0 1 ω y = (ω : F) ^ locE false true y
    intro y
    fin_cases y <;> simp [locD, locE, frK_apply, hinv]
  · revert y
    show ∀ y : Fin 3, locD true false 0 1 ω y = (ω : F) ^ locE true false y
    intro y
    fin_cases y <;> simp [locD, locE, frK_apply, hinv]
  · revert y
    show ∀ y : Fin 8, locD true true 0 1 ω y = (ω : F) ^ locE true true y
    intro y
    fin_cases y <;> simp [locD, locE, frK_apply, hinv] <;>
      first | ring1 | linear_combination (ω : F) * hω

theorem prod_locD_one (α β : Bool) {ω : Fˣ} (hω : (ω : F) ^ 3 = 1)
    (x : TIdx 2 (fun _ => α) (fun _ => β)) :
    ∏ i : Fin 2, locD α β (i : ℕ) 1 ω (x i) =
      (ω : F) ^ (locE α β (x 0) + 2 * locE α β (x 1)) := by
  rw [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, locD_eq_frK α β 1, locD_zero_one α β hω,
    locD_zero_one α β hω, frK_apply, Algebra.algebraMap_self, RingHom.id_apply, pow_one,
    ← pow_mul, ← pow_add, mul_comm (locE α β (x 1))]

theorem card_eig_one [DecidableEq F] (α β : Bool) {ω : Fˣ} (hω : orderOf ω = 3) :
    Fintype.card {x : TIdx 2 (fun _ => α) (fun _ => β) //
        ∏ i : Fin 2, locD α β (i : ℕ) 1 ω (x i) = 1} =
      Fintype.card {x : TIdx 2 (fun _ => α) (fun _ => β) //
        3 ∣ locE α β (x 0) + 2 * locE α β (x 1)} := by
  have hω3 : (ω : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [prod_locD_one α β hω3, ← hω, orderOf_dvd_iff_pow_eq_one, ← Units.val_pow_eq_pow_val,
    Units.val_eq_one]

end CFSG.Quasithin.H13.Ch4.B414
