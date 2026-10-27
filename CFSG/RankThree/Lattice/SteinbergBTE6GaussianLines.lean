module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFour

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Polynomial Matrix

section Ring

variable {R : Type*} [CommRing R]

@[expose] def e6G4Y (r a b : R) : Fin Tag.E6.rank → R :=
  (![a, r * a, -a, b, r * b, -b] : Fin 6 → R)

@[expose] def e6G4Z (r a b : R) : Fin Tag.E6.rank → R :=
  ((e6F4B⁻¹).map (Int.cast : ℤ → R)).transpose.mulVec (e6G4Y r a b)

theorem e6F4B_inv_eq : e6F4B⁻¹ = toMat Tag.E6.rank e6F4BInv :=
  Matrix.inv_eq_right_inv (by rw [e6F4B_eq]; exact e6F4B_mul_inv)

theorem e6G4Z_eq (r a b : R) :
    e6G4Z r a b =
      ((toMat Tag.E6.rank e6F4BInv).map (Int.cast : ℤ → R)).transpose.mulVec (e6G4Y r a b) := by
  rw [e6G4Z, e6F4B_inv_eq]

theorem charVal_e6G4Z_col (r a b : R) (j : Fin Tag.E6.rank) :
    charVal (e6G4Z r a b) (fun i => e6F4B i j) = e6G4Y r a b j := by
  rw [e6G4Z_eq, charVal_mulVec, e6F4B_eq]
  have e : (toMat Tag.E6.rank e6F4BInv).mulVec (fun i => toMat Tag.E6.rank e6F4BList i j) =
      Pi.single j 1 := by
    funext i
    have := congrFun (congrFun e6F4_inv_mul_B i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Matrix.mulVec, dotProduct, this, Pi.single_apply]
  rw [e, charVal_single]

theorem charVal_e6G4Z_v (r a b : R) : charVal (e6G4Z r a b) e6F4V = a :=
  charVal_e6G4Z_col r a b 0

theorem charVal_e6G4Z_cv (r a b : R) : charVal (e6G4Z r a b) (e6F4C • e6F4V) = b :=
  charVal_e6G4Z_col r a b 3

theorem e6G4Z_zero (r : R) : e6G4Z r 0 0 = 0 := by
  rw [e6G4Z]
  have e : e6G4Y r (0 : R) 0 = 0 := by
    funext k
    revert k
    change ∀ k : Fin 6, (![0, r * 0, -0, 0, r * 0, -0] : Fin 6 → R) k = 0
    intro k
    fin_cases k <;> simp
  rw [e, Matrix.mulVec_zero]

theorem e6F4U_cube_v :
    e6F4U • ((e6F4U ^ 2) • e6F4V) = (e6F4U ^ 2) • e6F4V - e6F4U • e6F4V + e6F4V := by
  rw [e6F4_smul_U2, e6F4_smul_U, e6F4_smul_U]
  decide +kernel

theorem e6F4U_cube_cv :
    e6F4U • ((e6F4U ^ 2) • e6F4C • e6F4V) =
      (e6F4U ^ 2) • e6F4C • e6F4V - e6F4U • e6F4C • e6F4V + e6F4C • e6F4V := by
  rw [e6F4_smul_C, e6F4_smul_U2, e6F4_smul_U, e6F4_smul_U]
  decide +kernel

theorem dualMatrix_mulVec_e6G4Z {r : R} (hr : r ^ 2 + 1 = 0) (a b : R) :
    (dualMatrix R e6F4U).mulVec (e6G4Z r a b) = r • e6G4Z r a b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_charVal_columns e6F4B_mul_inv fun j => ?_
  rw [charVal_sub_col, charVal_dualMatrix, charVal_smul_col, sub_eq_zero]
  have hcol : (fun i => toMat Tag.E6.rank e6F4BList i j) = fun i => e6F4B i j := by
    rw [e6F4B_eq]
  rw [hcol]
  have hc := charVal_e6G4Z_col r a b
  have c0 : charVal (e6G4Z r a b) e6F4V = a := hc 0
  have c1 : charVal (e6G4Z r a b) (e6F4U • e6F4V) = r * a := hc 1
  have c2 : charVal (e6G4Z r a b) ((e6F4U ^ 2) • e6F4V) = -a := hc 2
  have c3 : charVal (e6G4Z r a b) (e6F4C • e6F4V) = b := hc 3
  have c4 : charVal (e6G4Z r a b) (e6F4U • e6F4C • e6F4V) = r * b := hc 4
  have c5 : charVal (e6G4Z r a b) ((e6F4U ^ 2) • e6F4C • e6F4V) = -b := hc 5
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · change charVal (e6G4Z r a b) (e6F4U • e6F4V) = r * charVal (e6G4Z r a b) e6F4V
    rw [c1, c0]
  · change charVal (e6G4Z r a b) (e6F4U • e6F4U • e6F4V) =
      r * charVal (e6G4Z r a b) (e6F4U • e6F4V)
    rw [← mul_smul, ← sq, c2, c1]
    linear_combination (-a) * hr
  · change charVal (e6G4Z r a b) (e6F4U • (e6F4U ^ 2) • e6F4V) =
      r * charVal (e6G4Z r a b) ((e6F4U ^ 2) • e6F4V)
    rw [e6F4U_cube_v, charVal_add, charVal_sub, c2, c1, c0]
    ring
  · change charVal (e6G4Z r a b) (e6F4U • e6F4C • e6F4V) =
      r * charVal (e6G4Z r a b) (e6F4C • e6F4V)
    rw [c4, c3]
  · change charVal (e6G4Z r a b) (e6F4U • e6F4U • e6F4C • e6F4V) =
      r * charVal (e6G4Z r a b) (e6F4U • e6F4C • e6F4V)
    rw [← mul_smul e6F4U e6F4U, ← sq, c5, c4]
    linear_combination (-b) * hr
  · change charVal (e6G4Z r a b) (e6F4U • (e6F4U ^ 2) • e6F4C • e6F4V) =
      r * charVal (e6G4Z r a b) ((e6F4U ^ 2) • e6F4C • e6F4V)
    rw [e6F4U_cube_cv, charVal_add, charVal_sub, c5, c4, c3]
    ring

theorem eq_e6G4Z_of_dualMatrix_mulVec {r : R} (hr : r ^ 2 + 1 = 0) {z : Fin Tag.E6.rank → R}
    (hz : (dualMatrix R e6F4U).mulVec z = r • z) :
    z = e6G4Z r (charVal z e6F4V) (charVal z (e6F4C • e6F4V)) := by
  have hU : ∀ x, charVal z (e6F4U • x) = r * charVal z x := fun x => by
    rw [← charVal_dualMatrix, hz, charVal_smul_col]
  have hU2 : ∀ x, charVal z ((e6F4U ^ 2) • x) = -charVal z x := fun x => by
    rw [sq, mul_smul, hU, hU, ← mul_assoc, ← sq]
    linear_combination charVal z x * hr
  rw [← sub_eq_zero]
  refine eq_zero_of_charVal_columns e6F4B_mul_inv fun j => ?_
  have hcol : (fun i => toMat Tag.E6.rank e6F4BList i j) = fun i => e6F4B i j := by
    rw [e6F4B_eq]
  rw [hcol, charVal_sub_col, charVal_e6G4Z_col, sub_eq_zero]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · change charVal z (e6F4U • e6F4V) = r * charVal z e6F4V
    rw [hU]
  · change charVal z ((e6F4U ^ 2) • e6F4V) = -charVal z e6F4V
    rw [hU2]
  · rfl
  · change charVal z (e6F4U • e6F4C • e6F4V) = r * charVal z (e6F4C • e6F4V)
    rw [hU]
  · change charVal z ((e6F4U ^ 2) • e6F4C • e6F4V) = -charVal z (e6F4C • e6F4V)
    rw [hU2]

end Ring

section Gauss

variable {R : Type*} [CommRing R]

@[expose] def e6G4Mul (x y : ℤ × ℤ) : ℤ × ℤ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[expose] def e6G4Norm (x : ℤ × ℤ) : ℤ := x.1 ^ 2 + x.2 ^ 2

@[expose] def e6G4Conj (x : ℤ × ℤ) : ℤ × ℤ := (x.1, -x.2)

@[expose] def e6G4Eval (r : R) (x : ℤ × ℤ) : R := x.1 + x.2 * r

theorem e6G4Eval_mul {r : R} (hr : r ^ 2 + 1 = 0) (x y : ℤ × ℤ) :
    e6G4Eval r (e6G4Mul x y) = e6G4Eval r x * e6G4Eval r y := by
  simp only [e6G4Eval, e6G4Mul]
  push_cast
  linear_combination (-((x.2 : R) * y.2)) * hr

theorem e6G4Eval_mul_conj {r : R} (hr : r ^ 2 + 1 = 0) (x : ℤ × ℤ) :
    e6G4Eval r x * e6G4Eval r (e6G4Conj x) = e6G4Norm x := by
  simp only [e6G4Eval, e6G4Conj, e6G4Norm]
  push_cast
  linear_combination (-((x.2 : R) ^ 2)) * hr

theorem e6G4Eval_sub (r : R) (x y : ℤ × ℤ) :
    e6G4Eval r (x - y) = e6G4Eval r x - e6G4Eval r y := by
  simp only [e6G4Eval, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

@[expose] def e6G4Units : List (ℤ × ℤ) :=
  [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]

theorem e6G4Norm_of_mem_e6G4Units : ∀ u ∈ e6G4Units, e6G4Norm u = 1 ∨ e6G4Norm u = 2 := by
  decide

@[expose] def e6G4Line : Fin 6 → (ℤ × ℤ) × (ℤ × ℤ) :=
  ![((0, 0), (1, 0)), ((1, 0), (0, 0)), ((-1, 0), (1, 0)), ((0, -1), (1, 0)),
    ((-1, -1), (1, 0)), ((-1, 0), (1, -1))]

@[expose] def e6G4LineForm (r a b : R) : Fin 6 → R :=
  ![b, a, b - a, b - r * a, b - (1 + r) * a, (1 - r) * b - a]

theorem e6G4LineForm_eq (r a b : R) (k : Fin 6) :
    e6G4LineForm r a b k = e6G4Eval r (e6G4Line k).1 * a + e6G4Eval r (e6G4Line k).2 * b := by
  fin_cases k <;> simp [e6G4LineForm, e6G4Line, e6G4Eval] <;> ring

@[expose] def e6G4LineDet (k k' : Fin 6) : ℤ × ℤ :=
  e6G4Mul (e6G4Line k).1 (e6G4Line k').2 - e6G4Mul (e6G4Line k').1 (e6G4Line k).2

theorem e6G4Norm_e6G4LineDet : ∀ k k' : Fin 6, k ≠ k' →
    e6G4Norm (e6G4LineDet k k') = 1 ∨ e6G4Norm (e6G4LineDet k k') = 2 := by
  decide

end Gauss

section Forms

variable {R : Type*} [CommRing R]

@[expose] def e6G4F (α : Fin Tag.E6.rank → ℤ) : ℤ × ℤ :=
  (-α (e6Index 0) + α (e6Index 1) - α (e6Index 4) + α (e6Index 5),
    -α (e6Index 0) + 2 * α (e6Index 2) - α (e6Index 3))

@[expose] def e6G4G (α : Fin Tag.E6.rank → ℤ) : ℤ × ℤ :=
  (2 * α (e6Index 0) - α (e6Index 2),
    α (e6Index 1) - α (e6Index 2) + α (e6Index 3) - α (e6Index 4))

@[expose] def e6G4BInvMat6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, -1, 1, -1, 1; -1, 0, 2, -1, 0, 0; 1, -1, -1, 1, 0, 0; 1, 0, 0, -1, 1, 0;
    0, 1, -1, 1, -1, 0; -1, 0, 1, -1, 1, 0]

@[expose] def e6G4BInvMat : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := e6G4BInvMat6

theorem toMat_e6F4BInv : toMat Tag.E6.rank e6F4BInv = e6G4BInvMat := by
  decide +kernel

theorem e6G4Z_explicit (r a b : R) : e6G4Z r a b =
    (![-a - r * a + 2 * b, a + r * b, 2 * r * a - r * b - b, r * b - r * a, -a - r * b, a] :
      Fin 6 → R) := by
  rw [e6G4Z_eq, toMat_e6F4BInv]
  funext i
  revert i
  change ∀ i : Fin 6, ((e6G4BInvMat6.map (Int.cast : ℤ → R)).transpose.mulVec
    (![a, r * a, -a, b, r * b, -b] : Fin 6 → R)) i = _
  intro i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, e6G4BInvMat6] <;> ring

theorem charVal_e6G4Z (r a b : R) (α : Fin Tag.E6.rank → ℤ) :
    charVal (e6G4Z r a b) α = e6G4Eval r (e6G4F α) * a + e6G4Eval r (e6G4G α) * b := by
  rw [e6G4Z_explicit]
  simp only [charVal]
  change ∑ i : Fin 6, _ = _
  simp only [Fin.sum_univ_six, e6G4Eval, e6G4F, e6G4G, e6Index]
  simp
  ring

@[expose] def E6G4OnLine (k : Fin 6) (α : Fin Tag.E6.rank → ℤ) : Prop :=
  ∃ u ∈ e6G4Units, e6G4F α = e6G4Mul u (e6G4Line k).1 ∧ e6G4G α = e6G4Mul u (e6G4Line k).2

instance (k : Fin 6) (α : Fin Tag.E6.rank → ℤ) : Decidable (E6G4OnLine k α) :=
  inferInstanceAs (Decidable (∃ u ∈ e6G4Units, _))

theorem exists_e6G4OnLine : ∀ m : Fin 72, ∃ k : Fin 6, E6G4OnLine k (e6RootVec m) := by
  decide +kernel

theorem e6G4OnLine_unique : ∀ m : Fin 72, ∀ k k' : Fin 6,
    E6G4OnLine k (e6RootVec m) → E6G4OnLine k' (e6RootVec m) → k = k' := by
  decide +kernel

theorem exists_e6RootVec_e6G4OnLine : ∀ k : Fin 6, ∃ m : Fin 72, E6G4OnLine k (e6RootVec m) := by
  decide +kernel

end Forms

section Field

variable {p : ℕ} [Fact p.Prime]

theorem e6G4_intCast_ne_zero (hp : 3 < p) {n : ℤ} (hn : n = 1 ∨ n = 2) : (n : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hle : (p : ℤ) ≤ 2 := by
    rcases hn with rfl | rfl <;> exact (Int.le_of_dvd (by norm_num) h).trans (by norm_num)
  omega

theorem e6G4_two_ne_zero (hp : 3 < p) : (2 : ZMod p) ≠ 0 := by
  have h := e6G4_intCast_ne_zero hp (n := 2) (Or.inr rfl)
  rwa [Int.cast_ofNat] at h

theorem e6G4Eval_ne_zero (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0) {x : ℤ × ℤ}
    (hx : e6G4Norm x = 1 ∨ e6G4Norm x = 2) : e6G4Eval r x ≠ 0 := by
  intro h
  have := e6G4Eval_mul_conj hr x
  rw [h, zero_mul] at this
  exact e6G4_intCast_ne_zero hp hx this.symm

theorem charVal_e6G4Z_eq_zero_iff (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0) {k : Fin 6}
    {α : Fin Tag.E6.rank → ℤ} (hα : E6G4OnLine k α) (a b : ZMod p) :
    charVal (e6G4Z r a b) α = 0 ↔ e6G4LineForm r a b k = 0 := by
  obtain ⟨u, hu, hf, hg⟩ := hα
  rw [charVal_e6G4Z, hf, hg, e6G4Eval_mul hr, e6G4Eval_mul hr, e6G4LineForm_eq]
  rw [show e6G4Eval r u * e6G4Eval r (e6G4Line k).1 * a + e6G4Eval r u * e6G4Eval r
    (e6G4Line k).2 * b = e6G4Eval r u * (e6G4Eval r (e6G4Line k).1 * a +
      e6G4Eval r (e6G4Line k).2 * b) by ring]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left
    (e6G4Eval_ne_zero hp hr (e6G4Norm_of_mem_e6G4Units u hu)), fun h => by rw [h, mul_zero]⟩

theorem eq_of_e6G4LineForm_eq_zero (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0)
    {a b : ZMod p} (hab : (a, b) ≠ 0) {k k' : Fin 6} (hk : e6G4LineForm r a b k = 0)
    (hk' : e6G4LineForm r a b k' = 0) : k = k' := by
  by_contra hne
  rw [e6G4LineForm_eq] at hk hk'
  set c := e6G4Eval r (e6G4Line k).1
  set d := e6G4Eval r (e6G4Line k).2
  set c' := e6G4Eval r (e6G4Line k').1
  set d' := e6G4Eval r (e6G4Line k').2
  have hD : e6G4Eval r (e6G4LineDet k k') = c * d' - c' * d := by
    rw [e6G4LineDet, e6G4Eval_sub, e6G4Eval_mul hr, e6G4Eval_mul hr]
  have hD0 : c * d' - c' * d ≠ 0 := by
    rw [← hD]
    exact e6G4Eval_ne_zero hp hr (e6G4Norm_e6G4LineDet k k' hne)
  have ha : (c * d' - c' * d) * a = 0 := by linear_combination d' * hk - d * hk'
  have hb : (c * d' - c' * d) * b = 0 := by linear_combination c * hk' - c' * hk
  have ha0 := (mul_eq_zero.1 ha).resolve_left hD0
  have hb0 := (mul_eq_zero.1 hb).resolve_left hD0
  exact hab (by rw [ha0, hb0]; rfl)

theorem rootKernel_e6G4Z (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0) {a b : ZMod p}
    (hab : (a, b) ≠ 0) {k : Fin 6} (hk : e6G4LineForm r a b k = 0) :
    rootKernel (e6G4Z r a b) = {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α} := by
  ext α
  rw [mem_rootKernel, Set.mem_ofPred_eq]
  refine and_congr_right fun hα => ?_
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
  obtain ⟨k₀, h₀⟩ := exists_e6G4OnLine m
  rw [charVal_e6G4Z_eq_zero_iff hp hr h₀]
  constructor
  · intro h
    rwa [eq_of_e6G4LineForm_eq_zero hp hr hab h hk] at h₀
  · intro h
    rw [e6G4OnLine_unique m k₀ k h₀ h]
    exact hk

theorem exists_e6G4LineForm_eq_zero_iff (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 + 1 = 0)
    (a b : ZMod p) : (∃ k : Fin 6, e6G4LineForm r a b k = 0) ↔
      b = 0 ∨ a = 0 ∨ b = a ∨ b = r * a ∨ b = (1 + r) * a ∨ 2 * b = (1 + r) * a := by
  have h2 := e6G4_two_ne_zero hp
  have h5 : (1 - r) * b - a = 0 ↔ 2 * b = (1 + r) * a := by
    constructor
    · intro h
      linear_combination (1 + r) * h + b * hr
    · intro h
      have h' : 2 * ((1 - r) * b - a) = 0 := by linear_combination (1 - r) * h - a * hr
      exact (mul_eq_zero.1 h').resolve_left h2
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 hk)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.1 hk))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.1 hk)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h5.1 hk)))))
  · rintro (h | h | h | h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, sub_eq_zero.2 h⟩
    · exact ⟨3, sub_eq_zero.2 h⟩
    · exact ⟨4, sub_eq_zero.2 h⟩
    · exact ⟨5, h5.2 h⟩

end Field

theorem e6F4Z_two_one (j : ZMod 5) : e6F4Z 2 1 j = e6G4Z 2 1 j := by
  rw [e6F4Z, e6G4Z_eq]
  congr 1
  revert j
  decide

theorem e6F4Z_two_zero_one : e6F4Z 2 0 1 = e6G4Z (2 : ZMod 5) 0 1 := by
  rw [e6F4Z, e6G4Z_eq]
  congr 1
  decide

theorem e6G4_transporter_of_claims {a b : ZMod 5} (hab : (a, b) ≠ 0) {k : Fin 6}
    (hk : e6G4LineForm (2 : ZMod 5) a b k = 0) (hZ : e6F4Z 2 a b = e6G4Z 2 a b)
    (h : E6F4Claims (e6F4Z 2 a b)) :
    ∃ a₀ : WeylGroup Tag.E6,
      (a₀ • ·) '' {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α} = parabolicRoots Tag.E6 support134 ∧
      (∀ i j, j ∈ support134 → i ∉ support134 → weylMatrix (a₀ * e6F4U * a₀⁻¹) i j = 0) ∧
      ((weylMatrix (a₀ * e6F4U * a₀⁻¹)).submatrix chain134 chain134).charpoly =
        (X - 1) * (X ^ 2 + 1) ∧
      IsNegativeTransition (fun x => (a₀ * e6F4U * a₀⁻¹) • x) chain134 chain134 := by
  obtain ⟨⟨a₀, himg, h1, h2, h3⟩, -, -⟩ := h
  rw [hZ, rootKernel_e6G4Z (by norm_num) (by decide) hab hk] at himg
  exact ⟨a₀, himg, h1, h2, h3⟩

theorem e6G4_transporter (k : Fin 6) : ∃ a₀ : WeylGroup Tag.E6,
    (a₀ • ·) '' {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α} = parabolicRoots Tag.E6 support134 ∧
    (∀ i j, j ∈ support134 → i ∉ support134 → weylMatrix (a₀ * e6F4U * a₀⁻¹) i j = 0) ∧
    ((weylMatrix (a₀ * e6F4U * a₀⁻¹)).submatrix chain134 chain134).charpoly =
      (X - 1) * (X ^ 2 + 1) ∧
    IsNegativeTransition (fun x => (a₀ * e6F4U * a₀⁻¹) • x) chain134 chain134 := by
  fin_cases k
  · exact e6G4_transporter_of_claims (by decide) (by decide) (e6F4Z_two_one 0) e6F4_rep_2_1_0
  · exact e6G4_transporter_of_claims (by decide) (by decide) e6F4Z_two_zero_one e6F4_rep_2_0_1
  · exact e6G4_transporter_of_claims (by decide) (by decide) (e6F4Z_two_one 1) e6F4_rep_2_1_1
  · exact e6G4_transporter_of_claims (by decide) (by decide) (e6F4Z_two_one 2) e6F4_rep_2_1_2
  · exact e6G4_transporter_of_claims (by decide) (by decide) (e6F4Z_two_one 3) e6F4_rep_2_1_3
  · exact e6G4_transporter_of_claims (by decide) (by decide) (e6F4Z_two_one 4) e6F4_rep_2_1_4

theorem ncard_e6G4_rootSet (k : Fin 6) : {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α}.ncard = 12 := by
  obtain ⟨a₀, himg, -⟩ := e6G4_transporter k
  rw [← ncard_parabolicRoots_support134, ← himg,
    Set.ncard_image_of_injective _ (MulAction.injective a₀)]

theorem E6_order_four_six_Gaussian_root_kernel_lines {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {r : ZMod p} (hr : r ^ 2 + 1 = 0) :
    (∀ a b : ZMod p, (a, b) ≠ 0 → e6G4Z r a b ≠ 0 ∧
      (dualMatrix (ZMod p) e6F4U).mulVec (e6G4Z r a b) = r • e6G4Z r a b) ∧
    (∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 → (dualMatrix (ZMod p) e6F4U).mulVec z = r • z →
      ∃! ab : ZMod p × ZMod p, ab ≠ 0 ∧ z = e6G4Z r ab.1 ab.2) ∧
    (∀ k k' : Fin 6, k ≠ k' → ∀ a b : ZMod p, (a, b) ≠ 0 →
      ¬(e6G4LineForm r a b k = 0 ∧ e6G4LineForm r a b k' = 0)) ∧
    (∀ a b : ZMod p, (a, b) ≠ 0 → ((rootKernel (e6G4Z r a b)).Nonempty ↔
      b = 0 ∨ a = 0 ∨ b = a ∨ b = r * a ∨ b = (1 + r) * a ∨ 2 * b = (1 + r) * a)) ∧
    (∀ a b : ZMod p, (a, b) ≠ 0 → ∀ k : Fin 6, e6G4LineForm r a b k = 0 →
      rootKernel (e6G4Z r a b) = {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α} ∧
        (rootKernel (e6G4Z r a b)).ncard = 12) ∧
    (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ∃! k : Fin 6, E6G4OnLine k α) ∧
    ∀ k : Fin 6, {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α}.ncard = 12 ∧
      ∃ a₀ : WeylGroup Tag.E6,
        (a₀ • ·) '' {α | IsRoot Tag.E6 α ∧ E6G4OnLine k α} = parabolicRoots Tag.E6 support134 ∧
        (∀ i j, j ∈ support134 → i ∉ support134 → weylMatrix (a₀ * e6F4U * a₀⁻¹) i j = 0) ∧
        ((weylMatrix (a₀ * e6F4U * a₀⁻¹)).submatrix chain134 chain134).charpoly =
          (X - 1) * (X ^ 2 + 1) ∧
        IsNegativeTransition (fun x => (a₀ * e6F4U * a₀⁻¹) • x) chain134 chain134 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k => ⟨ncard_e6G4_rootSet k, e6G4_transporter k⟩⟩
  ·
    intro a b hab
    refine ⟨fun h => hab ?_, dualMatrix_mulVec_e6G4Z hr a b⟩
    have h1 := charVal_e6G4Z_v r a b
    have h2 := charVal_e6G4Z_cv r a b
    rw [h] at h1 h2
    simp only [charVal, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1 h2
    rw [← h1, ← h2]
    rfl
  ·
    intro z hz hu
    have hz' := eq_e6G4Z_of_dualMatrix_mulVec hr hu
    refine ⟨(charVal z e6F4V, charVal z (e6F4C • e6F4V)), ⟨fun h0 => hz ?_, hz'⟩, ?_⟩
    · rw [hz', show charVal z e6F4V = 0 from congrArg Prod.fst h0,
        show charVal z (e6F4C • e6F4V) = 0 from congrArg Prod.snd h0, e6G4Z_zero]
    · rintro ⟨a, b⟩ ⟨-, hab⟩
      rw [hab, charVal_e6G4Z_v, charVal_e6G4Z_cv]
  ·
    intro k k' hne a b hab h
    exact hne (eq_of_e6G4LineForm_eq_zero hp hr hab h.1 h.2)
  ·
    intro a b hab
    rw [← exists_e6G4LineForm_eq_zero_iff hp hr]
    constructor
    · rintro ⟨α, hα, hα0⟩
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
      obtain ⟨k, hk⟩ := exists_e6G4OnLine m
      exact ⟨k, (charVal_e6G4Z_eq_zero_iff hp hr hk a b).1 hα0⟩
    · rintro ⟨k, hk⟩
      obtain ⟨m, hm⟩ := exists_e6RootVec_e6G4OnLine k
      exact ⟨e6RootVec m, isRoot_e6RootVec m, (charVal_e6G4Z_eq_zero_iff hp hr hm a b).2 hk⟩
  ·
    intro a b hab k hk
    have h := rootKernel_e6G4Z hp hr hab hk
    exact ⟨h, by rw [h, ncard_e6G4_rootSet]⟩
  ·
    intro α hα
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    obtain ⟨k, hk⟩ := exists_e6G4OnLine m
    exact ⟨k, hk, fun k' hk' => e6G4OnLine_unique m k' k hk' hk⟩

end CFSG.RankThree.Lattice
