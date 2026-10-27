module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.B412

open Matrix

variable {n : ℕ}

theorem zmod_two_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

theorem mk_eq_mk_iff_two {v w : Fin n → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk (ZMod 2) v hv = Projectivization.mk (ZMod 2) w hw ↔ v = w := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact hv ha.symm
    rw [zmod_two_eq_one ha0, one_smul] at ha
    exact ha.symm
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem smul_mk_two (s : SpecialLinearGroup (Fin n) (ZMod 2)) {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    ∃ h, s • Projectivization.mk (ZMod 2) v hv =
      Projectivization.mk (ZMod 2) ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) h := by
  rw [Projectivization.matrixSpecialLinearGroup_smul_def, Projectivization.smul_mk]
  exact ⟨_, rfl⟩

theorem mulVec_ne_zero (s : SpecialLinearGroup (Fin n) (ZMod 2)) {v : Fin n → ZMod 2}
    (hv : v ≠ 0) : (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have e : ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    have e1 := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) (inv_mul_cancel s)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using e1
  rw [← one_mulVec v, ← e, ← mulVec_mulVec, h, mulVec_zero]

theorem exists_mulVec_eq {p q : Fin n → ZMod 2} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin n) (ZMod 2), (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p = q := by
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) (ZMod 2))
    (Projectivization.mk (ZMod 2) p hp) (Projectivization.mk (ZMod 2) q hq)
  obtain ⟨h, e⟩ := smul_mk_two s hp
  rw [e, mk_eq_mk_iff_two] at hs
  exact ⟨s, hs⟩

theorem exists_mulVec_pair {p₁ p₂ q₁ q₂ : Fin n → ZMod 2} (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hp : p₁ ≠ p₂) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hq : q₁ ≠ q₂) :
    ∃ s : SpecialLinearGroup (Fin n) (ZMod 2),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p₁ = q₁ ∧
        (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ p₂ = q₂ := by
  have h2 : ∀ {a b c d : Projectivization (ZMod 2) (Fin n → ZMod 2)}, a ≠ b → c ≠ d →
      ∃ g : SpecialLinearGroup (Fin n) (ZMod 2), g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.mp inferInstance
  obtain ⟨s, hs₁, hs₂⟩ := h2 (a := Projectivization.mk (ZMod 2) p₁ hp₁)
    (b := Projectivization.mk (ZMod 2) p₂ hp₂) (c := Projectivization.mk (ZMod 2) q₁ hq₁)
    (d := Projectivization.mk (ZMod 2) q₂ hq₂) (fun h => hp ((mk_eq_mk_iff_two _ _).mp h))
    (fun h => hq ((mk_eq_mk_iff_two _ _).mp h))
  obtain ⟨h₁, e₁⟩ := smul_mk_two s hp₁
  obtain ⟨h₂, e₂⟩ := smul_mk_two s hp₂
  rw [e₁, mk_eq_mk_iff_two] at hs₁
  rw [e₂, mk_eq_mk_iff_two] at hs₂
  exact ⟨s, hs₁, hs₂⟩

theorem card_fix_modEq_end {α : Type*} [Finite α] (p : ℕ) [Fact p.Prime] (f : Function.End α)
    (hf : f ^ p = 1) : Nat.card α ≡ Nat.card {x // f x = x} [MOD p] := by
  classical
  have := Fintype.ofFinite α
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) (f := f) (by rwa [pow_one])
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h using 2
  rfl

@[expose] def endOf (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Function.End (Fin n → ZMod 2) :=
  fun x => M *ᵥ x

theorem endOf_pow (M : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) (x : Fin n → ZMod 2) :
    (endOf M ^ k) x = (M ^ k) *ᵥ x := by
  induction k generalizing x with
  | zero => rw [pow_zero, pow_zero, one_mulVec]; rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mulVec_mulVec, ← ih]
    rfl

@[expose] def restr (M : Matrix (Fin n) (Fin n) (ZMod 2)) {S : Set (Fin n → ZMod 2)}
    (hS : ∀ x ∈ S, M *ᵥ x ∈ S) : Function.End S :=
  fun x => ⟨M *ᵥ (x : Fin n → ZMod 2), hS x x.2⟩

theorem restr_pow (M : Matrix (Fin n) (Fin n) (ZMod 2)) {S : Set (Fin n → ZMod 2)}
    (hS : ∀ x ∈ S, M *ᵥ x ∈ S) (k : ℕ) (x : S) :
    ((restr M hS ^ k) x : Fin n → ZMod 2) = (M ^ k) *ᵥ (x : Fin n → ZMod 2) := by
  induction k generalizing x with
  | zero => rw [pow_zero, pow_zero, one_mulVec]; rfl
  | succ k ih =>
    show ((restr M hS ^ k) (restr M hS x) : Fin n → ZMod 2) = _
    rw [ih, pow_succ, ← mulVec_mulVec]
    rfl

theorem fix_of_invariant (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hM : M ^ 7 = 1)
    {S : Set (Fin n → ZMod 2)} (hS : ∀ x ∈ S, M *ᵥ x ∈ S) (hcard : Nat.card S < 7) :
    ∀ x ∈ S, M *ᵥ x = x := by
  classical
  have hf : restr M hS ^ 7 = 1 := by
    funext x
    apply Subtype.ext
    rw [restr_pow, hM, one_mulVec]
    rfl
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := card_fix_modEq_end 7 (restr M hS) hf
  have hle : Nat.card {x // restr M hS x = x} ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun x => x.1) fun x y h => Subtype.ext h
  have heq : Nat.card {x // restr M hS x = x} = Nat.card S := by
    have h1 := Nat.mod_eq_of_lt hcard
    have h2 := Nat.mod_eq_of_lt (hle.trans_lt hcard)
    unfold Nat.ModEq at h
    omega
  intro x hx
  by_contra hne
  have := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at heq
  have hlt := Fintype.card_subtype_lt (p := fun y : S => restr M hS y = y) (x := ⟨x, hx⟩)
    (fun h => hne (congrArg Subtype.val h))
  omega

@[expose] def fixSub (M : Matrix (Fin n) (Fin n) (ZMod 2)) : AddSubgroup (Fin n → ZMod 2) where
  carrier := {x | M *ᵥ x = x}
  add_mem' {x y} hx hy := by
    show M *ᵥ (x + y) = x + y
    rw [mulVec_add, hx, hy]
  zero_mem' := mulVec_zero M
  neg_mem' {x} hx := by
    show M *ᵥ (-x) = -x
    rw [mulVec_neg, hx]

theorem eq_one_of_mulVec_eq {M : Matrix (Fin n) (Fin n) (ZMod 2)} (h : ∀ x, M *ᵥ x = x) :
    M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  rw [Matrix.one_apply]
  simp only [Matrix.col_apply, Pi.single_apply] at this
  rw [this]

theorem card_fix_eq_two (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M ^ 7 = 1) (hM1 : M ≠ 1) :
    Nat.card {x : Fin 4 → ZMod 2 // M *ᵥ x = x} = 2 := by
  classical
  have hN : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := card_fix_modEq_end 7 (endOf M) (by
    funext x
    rw [endOf_pow, hM, one_mulVec]
    rfl)
  rw [hN] at h1
  have h2 : Nat.card {x : Fin 4 → ZMod 2 // M *ᵥ x = x} ∣ 16 := by
    rw [← hN]
    exact AddSubgroup.card_addSubgroup_dvd_card (fixSub M)
  have h3 : Nat.card {x : Fin 4 → ZMod 2 // M *ᵥ x = x} < 16 := by
    obtain ⟨x, hx⟩ : ∃ x, M *ᵥ x ≠ x := by
      by_contra hc
      push Not at hc
      exact hM1 (eq_one_of_mulVec_eq hc)
    rw [← hN, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt hx
  have h4 : Nat.card {x : Fin 4 → ZMod 2 // endOf M x = x} =
      Nat.card {x : Fin 4 → ZMod 2 // M *ᵥ x = x} := rfl
  rw [h4] at h1
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2 ^ 4 from h2)
  rw [hk'] at h1 h3 ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

theorem even_card_fix {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (σ : P →* SpecialLinearGroup (Fin n) (ZMod 2)) (hn : n ≠ 0) :
    Even (Nat.card {x : Fin n → ZMod 2 //
      ∀ r, (σ r : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x}) := by
  let _ : MulAction P (Fin n → ZMod 2) :=
    { smul := fun r x => (σ r : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x
      one_smul := fun x => by
        show (σ 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x
        rw [map_one, Matrix.SpecialLinearGroup.coe_one, one_mulVec]
      mul_smul := fun r t x => by
        show (σ (r * t) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
          (σ r : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((σ t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
        rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec] }
  have h := hP.card_modEq_card_fixedPoints (Fin n → ZMod 2)
  have hN : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have h3 : Nat.card ↥(MulAction.fixedPoints P (Fin n → ZMod 2)) =
      Nat.card {x : Fin n → ZMod 2 // ∀ r, (σ r : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x} :=
    rfl
  rw [hN, h3] at h
  have h4 : 2 ^ n % 2 = 0 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, hn⟩)
  unfold Nat.ModEq at h
  exact Nat.even_iff.mpr (by omega)

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_dual (W : AddSubgroup (Fin 4 → ZMod 2)) (hW : Nat.card W = 8) :
    ∃ p : Fin 4 → ZMod 2, p ≠ 0 ∧ ∀ x, x ∈ W ↔ p ⬝ᵥ x = 0 := by
  classical
  have hN : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hidx : W.index = 2 := by
    have h := AddSubgroup.card_mul_index W
    rw [hW, hN] at h
    omega
  let f : (Fin 4 → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => if x ∈ W then 0 else 1
      map_zero' := by simp [W.zero_mem]
      map_add' := fun x y => by
        have h := AddSubgroup.add_mem_iff_of_index_two hidx (a := x) (b := y)
        by_cases hx : x ∈ W
        · by_cases hy : y ∈ W
          · have hxy : x + y ∈ W := h.mpr (iff_of_true hx hy)
            simp only [hx, hy, hxy, ↓reduceIte, add_zero]
          · have hxy : x + y ∉ W := fun hxy => hy ((h.mp hxy).mp hx)
            simp only [hx, hy, hxy, ↓reduceIte, zero_add]
        · by_cases hy : y ∈ W
          · have hxy : x + y ∉ W := fun hxy => hx ((h.mp hxy).mpr hy)
            simp only [hx, hy, hxy, ↓reduceIte, add_zero]
          · have hxy : x + y ∈ W := h.mpr (iff_of_false hx hy)
            simp only [hx, hy, hxy, ↓reduceIte]
            decide }
  have hf : ∀ x, f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases zmod_two_cases (x i) with h | h
    · rw [h, Pi.single_zero, map_zero, mul_zero]
    · rw [h, mul_one]
  have hmem : ∀ x, x ∈ W ↔ f x = 0 := by
    intro x
    show x ∈ W ↔ (if x ∈ W then (0 : ZMod 2) else 1) = 0
    by_cases hx : x ∈ W
    · simp [hx]
    · simp only [hx, ↓reduceIte, false_iff]
      decide
  obtain ⟨y, hy⟩ : ∃ y, y ∉ W := by
    by_contra hc
    push Not at hc
    have : W = ⊤ := eq_top_iff.mpr fun y _ => hc y
    rw [this, AddSubgroup.card_top, hN] at hW
    omega
  refine ⟨fun i => f (Pi.single i 1), fun h0 => ?_, fun x => by rw [hmem, hf]⟩
  apply hy
  rw [hmem, hf, h0, zero_dotProduct]

variable {R : Type*} [CommRing R]

@[expose] def invTr : SpecialLinearGroup (Fin n) R →* SpecialLinearGroup (Fin n) R where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  map_one' := Subtype.ext (by
    rw [inv_one]
    exact Matrix.transpose_one)
  map_mul' g h := Subtype.ext (by
    show ((((g * h)⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R))ᵀ =
      (((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R))ᵀ *
        (((h⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R))ᵀ
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

theorem coe_invTr (g : SpecialLinearGroup (Fin n) R) :
    ((invTr g : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R))ᵀ := rfl

theorem invTr_invTr (g : SpecialLinearGroup (Fin n) R) : invTr (invTr g) = g := by
  have e : SpecialLinearGroup.transpose g⁻¹ * SpecialLinearGroup.transpose g = 1 :=
    Subtype.ext (by
      show (((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R))ᵀ *
        ((g : Matrix (Fin n) (Fin n) R))ᵀ = 1
      rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one])
  have e2 : (SpecialLinearGroup.transpose g⁻¹)⁻¹ = SpecialLinearGroup.transpose g :=
    inv_eq_of_mul_eq_one_right e
  apply Subtype.ext
  show ((((SpecialLinearGroup.transpose g⁻¹)⁻¹ : SpecialLinearGroup (Fin n) R) :
    Matrix (Fin n) (Fin n) R))ᵀ = g
  rw [e2]
  exact Matrix.transpose_transpose _

theorem invTr_surjective : Function.Surjective (invTr (n := n) (R := R)) :=
  fun g => ⟨invTr g, invTr_invTr g⟩

theorem invTr_mulVec {g : SpecialLinearGroup (Fin n) R} {p : Fin n → R}
    (h : ∀ x, p ⬝ᵥ ((g : Matrix (Fin n) (Fin n) R) *ᵥ x) = p ⬝ᵥ x) :
    ((invTr g : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ p = p := by
  have h1 : p ᵥ* (g : Matrix (Fin n) (Fin n) R) = p := by
    funext j
    have := h (Pi.single j 1)
    rwa [dotProduct_mulVec, dotProduct_single_one, dotProduct_single_one] at this
  have h2 : (g : Matrix (Fin n) (Fin n) R) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [coe_invTr, mulVec_transpose]
  conv_lhs => rw [← h1]
  rw [vecMul_vecMul, h2, vecMul_one]

end CFSG.Quasithin.B412

end
