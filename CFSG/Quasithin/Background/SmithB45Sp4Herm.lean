module

public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.B45Sp4

open scoped Matrix

section Tw

variable {ι : Type} [Fintype ι] {F : Type} [Field F]

@[expose] def tw (a : ℕ) (g Y : Matrix ι ι F) : Matrix ι ι F := g * Y * (frobPow a g)ᵀ

theorem tw_apply (a : ℕ) (g Y : Matrix ι ι F) : tw a g Y = g * Y * (frobPow a g)ᵀ := rfl

theorem tw_mul [CharP F 2] (a : ℕ) (g h Y : Matrix ι ι F) : tw a (g * h) Y = tw a g (tw a h Y) := by
  simp only [tw, frobPow_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem tw_one [DecidableEq ι] [CharP F 2] (a : ℕ) (Y : Matrix ι ι F) : tw a 1 Y = Y := by
  rw [tw, frobPow_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem tw_add (a : ℕ) (g Y Z : Matrix ι ι F) : tw a g (Y + Z) = tw a g Y + tw a g Z := by
  simp only [tw, Matrix.mul_add, Matrix.add_mul]

theorem tw_smul (a : ℕ) (g Y : Matrix ι ι F) (c : F) : tw a g (c • Y) = c • tw a g Y := by
  simp only [tw, Matrix.mul_smul, Matrix.smul_mul]

theorem tw_zero (a : ℕ) (g : Matrix ι ι F) : tw a g 0 = 0 := by
  simp [tw]

theorem tw_sub (a : ℕ) (g Y Z : Matrix ι ι F) : tw a g (Y - Z) = tw a g Y - tw a g Z := by
  simp only [tw, Matrix.mul_sub, Matrix.sub_mul]

theorem tw_neg (a : ℕ) (g Y : Matrix ι ι F) : tw a g (-Y) = -tw a g Y := by
  simp only [tw, Matrix.mul_neg, Matrix.neg_mul]

@[expose] def twLin (a : ℕ) (g : Matrix ι ι F) : Matrix ι ι F →ₗ[F] Matrix ι ι F where
  toFun := tw a g
  map_add' := tw_add a g
  map_smul' c Y := tw_smul a g Y c

theorem twLin_apply (a : ℕ) (g Y : Matrix ι ι F) : twLin a g Y = tw a g Y := rfl

end Tw

section Frob

variable {F : Type} [Field F] [CharP F 2]

theorem frobPow_add' {ι : Type} (a : ℕ) (X Y : Matrix ι ι F) :
    frobPow a (X + Y) = frobPow a X + frobPow a Y := by
  rw [frobPow_eq_map, frobPow_eq_map, frobPow_eq_map, Matrix.map_add]
  exact map_add _

omit [CharP F 2] in
theorem frobPow_smul' {ι : Type} (a : ℕ) (c : F) (X : Matrix ι ι F) :
    frobPow a (c • X) = c ^ 2 ^ a • frobPow a X := by
  ext i j
  simp [frobPow, mul_pow]

omit [CharP F 2] in
theorem frobPow_zero' {ι : Type} (a : ℕ) : frobPow a (0 : Matrix ι ι F) = 0 := by
  ext i j
  simp [frobPow]

omit [CharP F 2] in
theorem pow_pow_frob [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (x : F) :
    (x ^ 2 ^ a) ^ 2 ^ a = x := by
  have : Fintype F := Fintype.ofFinite F
  rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [CharP F 2] in
theorem card_frobFix_le [Fintype F] [DecidableEq F] {a : ℕ} (ha : 1 ≤ a) :
    (Finset.univ.filter fun x : F => x ^ 2 ^ a = x).card ≤ 2 ^ a := by
  classical
  set p : Polynomial F := Polynomial.X ^ 2 ^ a - Polynomial.X with hp
  have h2a : 1 < 2 ^ a := Nat.one_lt_two_pow (by omega)
  have hdeg : p.natDegree = 2 ^ a := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [h2a]
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  refine le_of_le_of_eq (Polynomial.card_le_degree_of_subset_roots ?_) hdeg
  intro x hx
  rw [Finset.mem_val, Finset.mem_filter] at hx
  rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, hp]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hx.2, sub_self]

omit [CharP F 2] in
theorem exists_ne_frob [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) :
    ∃ θ : F, θ ^ 2 ^ a ≠ θ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have h1 := card_frobFix_le (F := F) ha
  rw [Finset.filter_true_of_mem (fun x _ => h x), Finset.card_univ, ← Nat.card_eq_fintype_card,
    hF] at h1
  have : 2 ^ a < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end Frob

@[expose] def hermA (a : ℕ) (ι : Type) (F : Type) [Field F] [CharP F 2] :
    AddSubgroup (Matrix ι ι F) where
  carrier := {Y | (frobPow a Y)ᵀ = Y}
  add_mem' := fun {X Y} hX hY => by
    show (frobPow a (X + Y))ᵀ = X + Y
    have hX' : (frobPow a X)ᵀ = X := hX
    have hY' : (frobPow a Y)ᵀ = Y := hY
    rw [frobPow_add', Matrix.transpose_add, hX', hY']
  zero_mem' := by
    show (frobPow a (0 : Matrix ι ι F))ᵀ = 0
    rw [frobPow_zero', Matrix.transpose_zero]
  neg_mem' := fun {X} hX => by
    show (frobPow a (-X))ᵀ = -X
    have hX' : (frobPow a X)ᵀ = X := hX
    have hn : -X = X := by
      ext i j
      simp only [Matrix.neg_apply, CharTwo.neg_eq]
    rw [hn, hX']

@[expose] def matFix (a : ℕ) (ι : Type) [Fintype ι] (F : Type) [Field F]
    (E : Set (Matrix ι ι F)) : AddSubgroup (Matrix ι ι F) where
  carrier := {Y | ∀ g ∈ E, tw a g Y = Y}
  add_mem' := fun {Y Z} hY hZ g hg => by rw [tw_add, hY g hg, hZ g hg]
  zero_mem' := fun g _ => tw_zero a g
  neg_mem' := fun {Y} hY g hg => by rw [tw_neg, hY g hg]

@[expose] def hermFix (a : ℕ) (ι : Type) [Fintype ι] (F : Type) [Field F] [CharP F 2]
    (E : Set (Matrix ι ι F)) : AddSubgroup (Matrix ι ι F) :=
  hermA a ι F ⊓ matFix a ι F E

@[expose] def star' {ι : Type} {F : Type} [Field F] (a : ℕ) (Y : Matrix ι ι F) : Matrix ι ι F :=
  (frobPow a Y)ᵀ

section Herm

variable {ι : Type} {F : Type} [Field F] [CharP F 2]

theorem mem_hermA {a : ℕ} {Y : Matrix ι ι F} : Y ∈ hermA a ι F ↔ (frobPow a Y)ᵀ = Y := Iff.rfl

theorem mem_hermA_iff_star' {a : ℕ} {Y : Matrix ι ι F} : Y ∈ hermA a ι F ↔ star' a Y = Y :=
  Iff.rfl

theorem star'_add (a : ℕ) (X Y : Matrix ι ι F) : star' a (X + Y) = star' a X + star' a Y := by
  rw [star', star', star', frobPow_add', Matrix.transpose_add]

omit [CharP F 2] in
theorem star'_smul (a : ℕ) (c : F) (Y : Matrix ι ι F) :
    star' a (c • Y) = c ^ 2 ^ a • star' a Y := by
  rw [star', star', frobPow_smul', Matrix.transpose_smul]

omit [CharP F 2] in
theorem star'_star' [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (Y : Matrix ι ι F) :
    star' a (star' a Y) = Y := by
  rw [star', star', frobPow_transpose, frobPow_frobPow a hF, Matrix.transpose_transpose]

variable [Fintype ι]

theorem ofAdd_mem_hermSub {a : ℕ} {Y : Matrix ι ι F} :
    Multiplicative.ofAdd Y ∈ hermSub a ι F ↔ Y ∈ hermA a ι F := Iff.rfl

theorem tw_mem_hermA [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (g : Matrix ι ι F)
    {Y : Matrix ι ι F} (hY : Y ∈ hermA a ι F) : tw a g Y ∈ hermA a ι F := by
  rw [mem_hermA] at hY ⊢
  rw [tw_apply, frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow a hF,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hY, Matrix.mul_assoc]

theorem star'_tw [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (g Y : Matrix ι ι F) :
    star' a (tw a g Y) = tw a g (star' a Y) := by
  rw [star', star', tw_apply, tw_apply, frobPow_mul, frobPow_mul, frobPow_transpose,
    frobPow_frobPow a hF, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

omit [CharP F 2] in
theorem mem_matFix {a : ℕ} {E : Set (Matrix ι ι F)} {Y : Matrix ι ι F} :
    Y ∈ matFix a ι F E ↔ ∀ g ∈ E, tw a g Y = Y := Iff.rfl

theorem mem_hermFix {a : ℕ} {E : Set (Matrix ι ι F)} {Y : Matrix ι ι F} :
    Y ∈ hermFix a ι F E ↔ Y ∈ hermA a ι F ∧ ∀ g ∈ E, tw a g Y = Y := Iff.rfl

theorem hermFix_empty (a : ℕ) : hermFix a ι F ∅ = hermA a ι F := by
  ext Y
  simp [mem_hermFix]

omit [CharP F 2] in
theorem matFix_empty (a : ℕ) : matFix a ι F ∅ = ⊤ := by
  ext Y
  simp [mem_matFix]

variable [Finite F] {a : ℕ}

omit [Fintype ι] [Finite F] in
theorem add_frob_ne_zero {θ : F} (hθ : θ ^ 2 ^ a ≠ θ) : θ + θ ^ 2 ^ a ≠ 0 := by
  intro h
  apply hθ
  have := eq_neg_of_add_eq_zero_right h
  rw [this, CharTwo.neg_eq]

omit [Fintype ι] in
theorem frob_add_frob (hF : Nat.card F = 2 ^ (2 * a)) (θ : F) :
    (θ + θ ^ 2 ^ a) ^ 2 ^ a = θ + θ ^ 2 ^ a := by
  rw [add_pow_char_pow, pow_pow_frob hF, add_comm]

omit [Fintype ι] in
theorem star'_smul_add (hF : Nat.card F = 2 ^ (2 * a)) (θ : F) (Y : Matrix ι ι F) :
    star' a ((θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y)) = (θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y) := by
  rw [star'_smul, star'_add, star'_star' hF, inv_pow, frob_add_frob hF, add_comm (star' a Y)]

omit [Fintype ι] in
theorem star'_sub_smul (hF : Nat.card F = 2 ^ (2 * a)) {θ : F} (hθ : θ ^ 2 ^ a ≠ θ)
    (Y : Matrix ι ι F) :
    star' a (Y + θ • ((θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y))) =
      Y + θ • ((θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y)) := by
  have hδ0 : θ + θ ^ 2 ^ a ≠ 0 := add_frob_ne_zero hθ
  set H := (θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y) with hH
  have hH' : star' a H = H := star'_smul_add hF θ Y
  have hδH : (θ + θ ^ 2 ^ a) • H = Y + star' a Y := by
    rw [hH, smul_smul, mul_inv_cancel₀ hδ0, one_smul]
  rw [star'_add, star'_smul, hH']
  have h2 : ∀ Z : Matrix ι ι F, Z + Z = 0 := fun Z => by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  have e : star' a Y = Y + (θ + θ ^ 2 ^ a) • H := by
    rw [hδH, ← add_assoc, h2, zero_add]
  rw [e, add_smul]
  have : Y + (θ • H + θ ^ 2 ^ a • H) + θ ^ 2 ^ a • H = Y + θ • H := by
    rw [add_assoc, add_assoc, h2, add_zero]
  exact this

theorem herm₁_mem (hF : Nat.card F = 2 ^ (2 * a)) {θ : F} (hθ : θ ^ 2 ^ a ≠ θ)
    {E : Set (Matrix ι ι F)} {Y : Matrix ι ι F} (hY : Y ∈ matFix a ι F E) :
    Y + θ • ((θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y)) ∈ hermFix a ι F E := by
  refine mem_hermFix.mpr ⟨mem_hermA_iff_star'.mpr (star'_sub_smul hF hθ Y), fun g hg => ?_⟩
  rw [tw_add, tw_smul, tw_smul, tw_add, (mem_matFix.mp hY) g hg, ← star'_tw hF,
    (mem_matFix.mp hY) g hg]

theorem herm₂_mem (hF : Nat.card F = 2 ^ (2 * a)) (θ : F) {E : Set (Matrix ι ι F)}
    {Y : Matrix ι ι F} (hY : Y ∈ matFix a ι F E) :
    (θ + θ ^ 2 ^ a)⁻¹ • (Y + star' a Y) ∈ hermFix a ι F E := by
  refine mem_hermFix.mpr ⟨mem_hermA_iff_star'.mpr (star'_smul_add hF θ Y), fun g hg => ?_⟩
  rw [tw_smul, tw_add, (mem_matFix.mp hY) g hg, ← star'_tw hF, (mem_matFix.mp hY) g hg]

omit [Finite F] in
theorem add_smul_mem_matFix (θ : F) {E : Set (Matrix ι ι F)} {H₁ H₂ : Matrix ι ι F}
    (h₁ : H₁ ∈ hermFix a ι F E) (h₂ : H₂ ∈ hermFix a ι F E) : H₁ + θ • H₂ ∈ matFix a ι F E := by
  intro g hg
  rw [tw_add, tw_smul, (mem_hermFix.mp h₁).2 g hg, (mem_hermFix.mp h₂).2 g hg]

@[expose] noncomputable def matFixEquiv (hF : Nat.card F = 2 ^ (2 * a)) {θ : F}
    (hθ : θ ^ 2 ^ a ≠ θ) (E : Set (Matrix ι ι F)) :
    ↥(hermFix a ι F E) × ↥(hermFix a ι F E) ≃ ↥(matFix a ι F E) where
  toFun p := ⟨(p.1 : Matrix ι ι F) + θ • (p.2 : Matrix ι ι F), add_smul_mem_matFix θ p.1.2 p.2.2⟩
  invFun Y := (⟨_, herm₁_mem hF hθ Y.2⟩, ⟨_, herm₂_mem hF θ Y.2⟩)
  left_inv p := by
    obtain ⟨⟨H₁, hH₁'⟩, ⟨H₂, hH₂'⟩⟩ := p
    have hH₁ := (mem_hermFix.mp hH₁').1
    have hH₂ := (mem_hermFix.mp hH₂').1
    have hδ0 : θ + θ ^ 2 ^ a ≠ 0 := add_frob_ne_zero hθ
    have h2 : ∀ Z : Matrix ι ι F, Z + Z = 0 := fun Z => by
      ext i j
      simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
    have hs : (H₁ + θ • H₂ + star' a (H₁ + θ • H₂)) = (θ + θ ^ 2 ^ a) • H₂ := by
      rw [star'_add, star'_smul, (mem_hermA_iff_star').mp hH₁, (mem_hermA_iff_star').mp hH₂,
        add_smul]
      have : H₁ + θ • H₂ + (H₁ + θ ^ 2 ^ a • H₂) = (H₁ + H₁) + (θ • H₂ + θ ^ 2 ^ a • H₂) := by
        abel
      rw [this, h2, zero_add]
    have hH2 : (θ + θ ^ 2 ^ a)⁻¹ • (H₁ + θ • H₂ + star' a (H₁ + θ • H₂)) = H₂ := by
      rw [hs, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext hH2)
    show H₁ + θ • H₂ + θ • ((θ + θ ^ 2 ^ a)⁻¹ • (H₁ + θ • H₂ + star' a (H₁ + θ • H₂))) = H₁
    rw [hH2, add_assoc, h2, add_zero]
  right_inv Y := by
    apply Subtype.ext
    have h2 : ∀ Z : Matrix ι ι F, Z + Z = 0 := fun Z => by
      ext i j
      simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
    show (Y : Matrix ι ι F) + θ • _ + θ • _ = Y
    rw [add_assoc, h2, add_zero]

theorem card_matFix (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) (E : Set (Matrix ι ι F)) :
    Nat.card ↥(matFix a ι F E) = Nat.card ↥(hermFix a ι F E) ^ 2 := by
  obtain ⟨θ, hθ⟩ := exists_ne_frob ha hF
  rw [← Nat.card_congr (matFixEquiv hF hθ E), Nat.card_prod, sq]

theorem card_hermA_sq (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) :
    Nat.card ↥(hermA a ι F) ^ 2 = Nat.card F ^ (Fintype.card ι * Fintype.card ι) := by
  have h := card_matFix (ι := ι) ha hF ∅
  rw [hermFix_empty, matFix_empty, AddSubgroup.card_top] at h
  rw [← h]
  show Nat.card (ι → ι → F) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ← pow_mul]

end Herm

end CFSG.Quasithin.B45Sp4
