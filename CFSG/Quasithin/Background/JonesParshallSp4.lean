module

public import CFSG.Quasithin.Background.B4ModelsWitness

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit

abbrev Ix : Type := Fin 2 ⊕ Fin 2

variable {F : Type} [Field F]

@[expose] def vec4 (a b c d : F) : Ix → F := Sum.elim ![a, b] ![c, d]

omit [Field F] in
theorem vec4_eta (v : Ix → F) :
    v = vec4 (v (.inl 0)) (v (.inl 1)) (v (.inr 0)) (v (.inr 1)) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

omit [Field F] in
theorem vec4_inj {a b c d a' b' c' d' : F} (h : vec4 a b c d = vec4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  ⟨congrFun h (.inl 0), congrFun h (.inl 1), congrFun h (.inr 0), congrFun h (.inr 1)⟩

theorem vec4_add (a b c d a' b' c' d' : F) :
    vec4 a b c d + vec4 a' b' c' d' = vec4 (a + a') (b + b') (c + c') (d + d') := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem vec4_sub (a b c d a' b' c' d' : F) :
    vec4 a b c d - vec4 a' b' c' d' = vec4 (a - a') (b - b') (c - c') (d - d') := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem vec4_smul (k a b c d : F) : k • vec4 a b c d = vec4 (k * a) (k * b) (k * c) (k * d) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem vec4_zero : vec4 (0 : F) 0 0 0 = 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

@[expose] def bil (x y : Ix → F) : F :=
  x (.inl 0) * y (.inr 0) + x (.inl 1) * y (.inr 1) + x (.inr 0) * y (.inl 0) +
    x (.inr 1) * y (.inl 1)

theorem bil_eq (x y : Ix → F) : bil x y = x ⬝ᵥ (spJ F *ᵥ y) := by
  simp [bil, spJ, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks,
    one_apply]
  ring

theorem bil_vec4 (a b c d a' b' c' d' : F) :
    bil (vec4 a b c d) (vec4 a' b' c' d') = a * c' + b * d' + c * a' + d * b' := rfl

theorem bil_mulVec {M : Matrix Ix Ix F} (hM : Mᵀ * spJ F * M = spJ F) (x y : Ix → F) :
    bil (M *ᵥ x) (M *ᵥ y) = bil x y := by
  rw [bil_eq, bil_eq, mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul,
    ← Matrix.mul_assoc, hM, ← dotProduct_mulVec]

theorem bil_smul {g : GL Ix F} (hg : g ∈ sp4 F) (x y : Ix → F) :
    bil (g • x) (g • y) = bil x y :=
  bil_mulVec hg x y

theorem spJ_mul_spJ : spJ F * spJ F = 1 := by
  rw [spJ, fromBlocks_multiply]
  simp [fromBlocks_one]

@[expose] def spUnit (M : Matrix Ix Ix F) (hM : Mᵀ * spJ F * M = spJ F) : GL Ix F where
  val := M
  inv := spJ F * Mᵀ * spJ F
  val_inv := by
    have h : spJ F * Mᵀ * spJ F * M = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM, spJ_mul_spJ]
    exact (mul_eq_one_comm_of_card_eq Ix Ix F rfl).mp h
  inv_val := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM, spJ_mul_spJ]

@[expose] def spElt (M : Matrix Ix Ix F) (hM : Mᵀ * spJ F * M = spJ F) : ↥(sp4 F) :=
  ⟨spUnit M hM, hM⟩

theorem spElt_coe (M : Matrix Ix Ix F) (hM : Mᵀ * spJ F * M = spJ F) :
    (((spElt M hM : ↥(sp4 F)) : GL Ix F) : Matrix Ix Ix F) = M := rfl

theorem spElt_smul (M : Matrix Ix Ix F) (hM : Mᵀ * spJ F * M = spJ F) (v : Ix → F) :
    ((spElt M hM : ↥(sp4 F)) : GL Ix F) • v = M *ᵥ v := rfl

theorem sp_fromBlocks (A B C D : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks A B C D)ᵀ * spJ F * fromBlocks A B C D =
      fromBlocks (Cᵀ * A + Aᵀ * C) (Cᵀ * B + Aᵀ * D) (Dᵀ * A + Bᵀ * C) (Dᵀ * B + Bᵀ * D) := by
  rw [fromBlocks_transpose, spJ, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem fromBlocks_mulVec_vec4 (A B C D : Matrix (Fin 2) (Fin 2) F) (a b c d : F) :
    fromBlocks A B C D *ᵥ vec4 a b c d =
      vec4 (A 0 0 * a + A 0 1 * b + B 0 0 * c + B 0 1 * d)
        (A 1 0 * a + A 1 1 * b + B 1 0 * c + B 1 1 * d)
        (C 0 0 * a + C 0 1 * b + D 0 0 * c + D 0 1 * d)
        (C 1 0 * a + C 1 1 * b + D 1 0 * c + D 1 1 * d) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [vec4, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

@[expose] def upMat (S : Matrix (Fin 2) (Fin 2) F) : Matrix Ix Ix F := fromBlocks 1 S 0 1

@[expose] def loMat (S : Matrix (Fin 2) (Fin 2) F) : Matrix Ix Ix F := fromBlocks 1 0 S 1

@[expose] def leviMat (A D : Matrix (Fin 2) (Fin 2) F) : Matrix Ix Ix F := fromBlocks A 0 0 D

variable [CharP F 2]

theorem upMat_mem {S : Matrix (Fin 2) (Fin 2) F} (hS : Sᵀ = S) :
    (upMat S)ᵀ * spJ F * upMat S = spJ F := by
  have h2 : S + S = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  rw [upMat, sp_fromBlocks, spJ]
  simp only [transpose_zero, transpose_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero, Matrix.one_mul, Matrix.mul_one, hS, h2]

theorem loMat_mem {S : Matrix (Fin 2) (Fin 2) F} (hS : Sᵀ = S) :
    (loMat S)ᵀ * spJ F * loMat S = spJ F := by
  have h2 : S + S = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  rw [loMat, sp_fromBlocks, spJ]
  simp only [transpose_zero, transpose_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero, Matrix.one_mul, Matrix.mul_one, hS, h2]

omit [CharP F 2] in
theorem leviMat_mem {A D : Matrix (Fin 2) (Fin 2) F} (h : Aᵀ * D = 1) :
    (leviMat A D)ᵀ * spJ F * leviMat A D = spJ F := by
  have h' : Dᵀ * A = 1 := by
    have := congrArg Matrix.transpose h
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  rw [leviMat, sp_fromBlocks, spJ]
  simp [h, h']

@[expose] def spU (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) : ↥(sp4 F) :=
  spElt (upMat S) (upMat_mem hS)

@[expose] def spL (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) : ↥(sp4 F) :=
  spElt (loMat S) (loMat_mem hS)

@[expose] def spLevi (A D : Matrix (Fin 2) (Fin 2) F) (h : Aᵀ * D = 1) : ↥(sp4 F) :=
  spElt (leviMat A D) (leviMat_mem h)

omit [CharP F 2] in
theorem upMat_smul (S : Matrix (Fin 2) (Fin 2) F) (a b c d : F) :
    upMat S *ᵥ vec4 a b c d =
      vec4 (a + S 0 0 * c + S 0 1 * d) (b + S 1 0 * c + S 1 1 * d) c d := by
  rw [upMat, fromBlocks_mulVec_vec4]
  simp [one_apply]

omit [CharP F 2] in
theorem loMat_smul (S : Matrix (Fin 2) (Fin 2) F) (a b c d : F) :
    loMat S *ᵥ vec4 a b c d =
      vec4 a b (S 0 0 * a + S 0 1 * b + c) (S 1 0 * a + S 1 1 * b + d) := by
  rw [loMat, fromBlocks_mulVec_vec4]
  simp [one_apply]

omit [CharP F 2] in
theorem leviMat_smul (A D : Matrix (Fin 2) (Fin 2) F) (a b c d : F) :
    leviMat A D *ᵥ vec4 a b c d =
      vec4 (A 0 0 * a + A 0 1 * b) (A 1 0 * a + A 1 1 * b) (D 0 0 * c + D 0 1 * d)
        (D 1 0 * c + D 1 1 * d) := by
  rw [leviMat, fromBlocks_mulVec_vec4]
  simp

omit [CharP F 2] in
theorem mat_ext_vec4 {M N : Matrix Ix Ix F}
    (h : ∀ a b c d : F, M *ᵥ vec4 a b c d = N *ᵥ vec4 a b c d) : M = N := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [vec4_eta (Pi.single i 1)]
  exact h _ _ _ _

omit [CharP F 2] in
theorem gl_ext_vec4 {g h : GL Ix F}
    (H : ∀ a b c d : F, g • vec4 a b c d = h • vec4 a b c d) : g = h :=
  Units.ext (mat_ext_vec4 H)

omit [CharP F 2] in
theorem sp4_ext {g h : ↥(sp4 F)}
    (H : ∀ a b c d : F, (g : GL Ix F) • vec4 a b c d = (h : GL Ix F) • vec4 a b c d) : g = h :=
  Subtype.ext (gl_ext_vec4 H)

omit [CharP F 2] in
theorem mulVec_vec4 (M : Matrix Ix Ix F) (a b c d : F) :
    M *ᵥ vec4 a b c d = a • (M *ᵥ vec4 1 0 0 0) + b • (M *ᵥ vec4 0 1 0 0) +
      c • (M *ᵥ vec4 0 0 1 0) + d • (M *ᵥ vec4 0 0 0 1) := by
  have h : vec4 a b c d = a • vec4 1 0 0 0 + b • vec4 0 1 0 0 + c • vec4 0 0 1 0 +
      d • vec4 0 0 0 1 := by
    simp only [vec4_smul, vec4_add, mul_one, mul_zero, add_zero, zero_add]
  rw [h, mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
    mulVec_smul]

@[expose] def symMat (a b d : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; b, d]

omit [CharP F 2] in
omit [Field F] in
theorem symMat_transpose (a b d : F) : (symMat a b d)ᵀ = symMat a b d := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def spX (a b d : F) : ↥(sp4 F) := spU (symMat a b d) (symMat_transpose a b d)

@[expose] def spY (a b d : F) : ↥(sp4 F) := spL (symMat a b d) (symMat_transpose a b d)

theorem spX_smul (a b d x y z w : F) :
    (spX a b d : GL Ix F) • vec4 x y z w = vec4 (x + a * z + b * w) (y + b * z + d * w) z w := by
  change upMat (symMat a b d) *ᵥ vec4 x y z w = _
  rw [upMat_smul]
  simp [symMat]

theorem spY_smul (a b d x y z w : F) :
    (spY a b d : GL Ix F) • vec4 x y z w = vec4 x y (a * x + b * y + z) (b * x + d * y + w) := by
  change loMat (symMat a b d) *ᵥ vec4 x y z w = _
  rw [loMat_smul]
  simp [symMat]

theorem levi_one_mul (t : F) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ * !![1, 0; t, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem levi_one_mul' (t : F) :
    (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ * !![1, t; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

@[expose] def spZ (t : F) : ↥(sp4 F) := spLevi !![1, t; 0, 1] !![1, 0; t, 1] (levi_one_mul t)

@[expose] def spZ' (t : F) : ↥(sp4 F) := spLevi !![1, 0; t, 1] !![1, t; 0, 1] (levi_one_mul' t)

theorem spZ_smul (t x y z w : F) :
    (spZ t : GL Ix F) • vec4 x y z w = vec4 (x + t * y) y z (t * z + w) := by
  change leviMat _ _ *ᵥ vec4 x y z w = _
  rw [leviMat_smul]
  simp

theorem spZ'_smul (t x y z w : F) :
    (spZ' t : GL Ix F) • vec4 x y z w = vec4 x (t * x + y) (z + t * w) w := by
  change leviMat _ _ *ᵥ vec4 x y z w = _
  rw [leviMat_smul]
  simp

omit [CharP F 2] in
theorem diag_mul_inv {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    (!![c, 0; 0, d] : Matrix (Fin 2) (Fin 2) F)ᵀ * !![c⁻¹, 0; 0, d⁻¹] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hc, hd]

@[expose] def spH (c d : F) (hc : c ≠ 0) (hd : d ≠ 0) : ↥(sp4 F) :=
  spLevi !![c, 0; 0, d] !![c⁻¹, 0; 0, d⁻¹] (diag_mul_inv hc hd)

omit [CharP F 2] in
theorem spH_smul {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) (x y z w : F) :
    (spH c d hc hd : GL Ix F) • vec4 x y z w = vec4 (c * x) (d * y) (c⁻¹ * z) (d⁻¹ * w) := by
  change leviMat _ _ *ᵥ vec4 x y z w = _
  rw [leviMat_smul]
  simp

@[expose] def iotaMat (a b c d : F) : Matrix Ix Ix F :=
  fromBlocks !![1, 0; 0, a] !![0, 0; 0, b] !![0, 0; 0, c] !![1, 0; 0, d]

theorem iotaMat_mem {a b c d : F} (h : a * d + b * c = 1) :
    (iotaMat a b c d)ᵀ * spJ F * iotaMat a b c d = spJ F := by
  rw [iotaMat, sp_fromBlocks, spJ]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination h
    | linear_combination (c * a) * h2
    | linear_combination (d * b) * h2

omit [CharP F 2] in
theorem iotaMat_smul (a b c d x y z w : F) :
    iotaMat a b c d *ᵥ vec4 x y z w = vec4 x (a * y + b * w) z (c * y + d * w) := by
  rw [iotaMat, fromBlocks_mulVec_vec4]
  simp

@[expose] def fixGens (F : Type) [Field F] [CharP F 2] : Set (GL Ix F) :=
  {g | (∃ a b d : F, g = spX a b d) ∨ (∃ t : F, g = spZ t) ∨ ∃ t : F, g = spY 0 0 t}

@[expose] def rootGens (F : Type) [Field F] [CharP F 2] : Set (GL Ix F) :=
  {g | (∃ a b d : F, g = spX a b d) ∨ (∃ a b d : F, g = spY a b d) ∨ (∃ t : F, g = spZ t) ∨
    ∃ t : F, g = spZ' t}

theorem fixGens_subset : fixGens F ⊆ rootGens F := by
  rintro g (⟨a, b, d, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact Or.inl ⟨a, b, d, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨t, rfl⟩))
  · exact Or.inr (Or.inl ⟨0, 0, t, rfl⟩)

theorem rootGens_subset : rootGens F ⊆ sp4 F := by
  rintro g (⟨a, b, d, rfl⟩ | ⟨a, b, d, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩) <;> exact Subtype.property _

theorem iota_mem_closure {a b c d : F} (h : a * d + b * c = 1) :
    (spElt (iotaMat a b c d) (iotaMat_mem h) : GL Ix F) ∈ Subgroup.closure (fixGens F) := by
  have hX : ∀ s : F, (spX 0 0 s : GL Ix F) ∈ Subgroup.closure (fixGens F) := fun s =>
    Subgroup.subset_closure (Or.inl ⟨0, 0, s, rfl⟩)
  have hY : ∀ s : F, (spY 0 0 s : GL Ix F) ∈ Subgroup.closure (fixGens F) := fun s =>
    Subgroup.subset_closure (Or.inr (Or.inr ⟨s, rfl⟩))
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ {a b c d : F} (h : a * d + b * c = 1), c ≠ 0 → ∃ s₁ s₂ : F,
      (spElt (iotaMat a b c d) (iotaMat_mem h) : GL Ix F) =
        (spX 0 0 s₁ : GL Ix F) * (spY 0 0 c : GL Ix F) * (spX 0 0 s₂ : GL Ix F) := by
    intro a b c d h hc
    obtain ⟨s₁, hs₁⟩ : ∃ s : F, s * c = a - 1 := ⟨(a - 1) / c, div_mul_cancel₀ _ hc⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s : F, s * c = d - 1 := ⟨(d - 1) / c, div_mul_cancel₀ _ hc⟩
    have hb : b = a * s₂ + s₁ := by
      apply mul_left_cancel₀ hc
      linear_combination (-a) * hs₂ - hs₁ - h + (b * c) * h2
    refine ⟨s₁, s₂, gl_ext_vec4 fun x y z w => ?_⟩
    rw [mul_smul, mul_smul, spX_smul, spY_smul, spX_smul]
    change iotaMat a b c d *ᵥ vec4 x y z w = _
    rw [iotaMat_smul]
    congr 1
    · ring
    · linear_combination w * hb - y * hs₁ - (s₂ * w) * hs₁
    · ring
    · linear_combination (-w) * hs₂
  by_cases hc : c = 0
  · subst hc
    have ha : a ≠ 0 := fun ha => by simp [ha] at h
    have h' : a * (b + d) + b * a = 1 := by linear_combination h + (a * b) * h2
    have e : (spElt (iotaMat a b 0 d) (iotaMat_mem h) : GL Ix F) =
        (spY (0 : F) 0 1 : GL Ix F) *
          (spElt (iotaMat a b a (b + d)) (iotaMat_mem h') : GL Ix F) := by
      refine gl_ext_vec4 fun x y z w => ?_
      rw [mul_smul]
      change iotaMat a b 0 d *ᵥ vec4 x y z w =
        (spY (0 : F) 0 1 : GL Ix F) • (iotaMat a b a (b + d) *ᵥ vec4 x y z w)
      rw [iotaMat_smul, iotaMat_smul, spY_smul]
      congr 1
      · ring
      · linear_combination (-(a * y + b * w)) * h2
    obtain ⟨s₁, s₂, hs⟩ := key h' ha
    rw [e, hs]
    exact Subgroup.mul_mem _ (hY 1) (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hX _) (hY a))
      (hX _))
  · obtain ⟨s₁, s₂, hs⟩ := key h hc
    rw [hs]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hX _) (hY c)) (hX _)

omit [CharP F 2] in
theorem bil_e1 (x : Ix → F) : bil x (vec4 1 0 0 0) = x (.inr 0) := by
  rw [vec4_eta x, bil_vec4]
  simp [vec4]

omit [CharP F 2] in
theorem bil_e2 (x : Ix → F) : bil x (vec4 0 1 0 0) = x (.inr 1) := by
  rw [vec4_eta x, bil_vec4]
  simp [vec4]

omit [CharP F 2] in
theorem bil_f1 (x : Ix → F) : bil x (vec4 0 0 1 0) = x (.inl 0) := by
  rw [vec4_eta x, bil_vec4]
  simp [vec4]

omit [CharP F 2] in
theorem bil_f2 (x : Ix → F) : bil x (vec4 0 0 0 1) = x (.inl 1) := by
  rw [vec4_eta x, bil_vec4]
  simp [vec4]

theorem mem_closure_of_fix {g : GL Ix F} (hg : g ∈ sp4 F)
    (h1 : g • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0) : g ∈ Subgroup.closure (fixGens F) := by
  set w := g • vec4 (0 : F) 0 1 0 with hw
  have hw3 : w (.inr 0) = 1 := by
    have h := bil_smul hg (vec4 0 0 1 0) (vec4 1 0 0 0)
    rw [h1, ← hw, bil_e1, bil_e1] at h
    simpa [vec4] using h
  set q : ↥(sp4 F) := spX (w (.inl 0) - w (.inl 1) * w (.inr 1)) (w (.inl 1)) 0 *
    spZ (w (.inr 1)) with hq
  have hq1 : (q : GL Ix F) • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0 := by
    rw [hq, Subgroup.coe_mul, mul_smul, spZ_smul, spX_smul]
    congr 1 <;> ring
  have hqf : (q : GL Ix F) • vec4 (0 : F) 0 1 0 = w := by
    conv_rhs => rw [vec4_eta w, hw3]
    rw [hq, Subgroup.coe_mul, mul_smul, spZ_smul, spX_smul]
    congr 1 <;> ring
  set g' := (q : GL Ix F)⁻¹ * g with hg'def
  have hg' : g' ∈ sp4 F := Subgroup.mul_mem _ (Subgroup.inv_mem _ q.2) hg
  have hg'1 : g' • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0 := by
    rw [hg'def, mul_smul, h1]
    conv_lhs => rw [← hq1]
    rw [inv_smul_smul]
  have hg'2 : g' • vec4 (0 : F) 0 1 0 = vec4 0 0 1 0 := by
    rw [hg'def, mul_smul, ← hw, ← hqf, inv_smul_smul]
  set x := g' • vec4 (0 : F) 1 0 0 with hx
  set y := g' • vec4 (0 : F) 0 0 1 with hy
  have hb : ∀ u u' : Ix → F, bil (g' • u) (g' • u') = bil u u' := bil_smul hg'
  have hx1 : x (.inl 0) = 0 := by
    have h := hb (vec4 0 1 0 0) (vec4 0 0 1 0)
    rw [hg'2, ← hx, bil_f1, bil_f1] at h
    simpa [vec4] using h
  have hx3 : x (.inr 0) = 0 := by
    have h := hb (vec4 0 1 0 0) (vec4 1 0 0 0)
    rw [hg'1, ← hx, bil_e1, bil_e1] at h
    simpa [vec4] using h
  have hy1 : y (.inl 0) = 0 := by
    have h := hb (vec4 0 0 0 1) (vec4 0 0 1 0)
    rw [hg'2, ← hy, bil_f1, bil_f1] at h
    simpa [vec4] using h
  have hy3 : y (.inr 0) = 0 := by
    have h := hb (vec4 0 0 0 1) (vec4 1 0 0 0)
    rw [hg'1, ← hy, bil_e1, bil_e1] at h
    simpa [vec4] using h
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : F, x (.inl 1) = X₂ := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ X₄ : F, x (.inr 1) = X₄ := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : F, y (.inl 1) = Y₂ := ⟨_, rfl⟩
  obtain ⟨Y₄, hY₄⟩ : ∃ Y₄ : F, y (.inr 1) = Y₄ := ⟨_, rfl⟩
  have hxv : x = vec4 0 X₂ 0 X₄ := by rw [vec4_eta x, hx1, hx3, hX₂, hX₄]
  have hyv : y = vec4 0 Y₂ 0 Y₄ := by rw [vec4_eta y, hy1, hy3, hY₂, hY₄]
  have hxy : X₂ * Y₄ + Y₂ * X₄ = 1 := by
    have h := hb (vec4 0 1 0 0) (vec4 0 0 0 1)
    rw [← hx, ← hy, hxv, hyv, bil_vec4, bil_vec4] at h
    linear_combination h
  have e : g' = (spElt (iotaMat X₂ Y₂ X₄ Y₄) (iotaMat_mem hxy) : GL Ix F) := by
    refine gl_ext_vec4 fun a b c d => ?_
    change (g' : Matrix Ix Ix F) *ᵥ vec4 a b c d = iotaMat _ _ _ _ *ᵥ vec4 a b c d
    rw [mulVec_vec4, iotaMat_smul]
    change a • (g' • vec4 (1 : F) 0 0 0) + b • (g' • vec4 (0 : F) 1 0 0) +
      c • (g' • vec4 (0 : F) 0 1 0) + d • (g' • vec4 (0 : F) 0 0 1) = _
    rw [hg'1, hg'2, ← hx, ← hy, hxv, hyv]
    simp only [vec4_smul, vec4_add]
    congr 1 <;> ring
  have hgq : g = (q : GL Ix F) * g' := by rw [hg'def, mul_inv_cancel_left]
  rw [hgq, e]
  refine Subgroup.mul_mem _ ?_ (iota_mem_closure hxy)
  rw [hq, Subgroup.coe_mul]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, _, _, rfl⟩))
    (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, rfl⟩)))

theorem exists_closure_smul_e1_of_ne {c v₂ v₃ v₄ : F} (hc : c ≠ 0) :
    ∃ r ∈ Subgroup.closure (rootGens F), r • vec4 (1 : F) 0 0 0 = vec4 c v₂ v₃ v₄ := by
  obtain ⟨t₁, ht₁⟩ : ∃ t : F, t * c = v₂ := ⟨v₂ / c, div_mul_cancel₀ _ hc⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t : F, t * c = v₄ := ⟨v₄ / c, div_mul_cancel₀ _ hc⟩
  obtain ⟨s, hs⟩ : ∃ t : F, t * c = v₃ - 1 - t₂ * t₁ * c :=
    ⟨(v₃ - 1 - t₂ * t₁ * c) / c, div_mul_cancel₀ _ hc⟩
  have hY : ∀ a b d : F, (spY a b d : GL Ix F) ∈ Subgroup.closure (rootGens F) := fun a b d =>
    Subgroup.subset_closure (Or.inr (Or.inl ⟨a, b, d, rfl⟩))
  have hX : ∀ a b d : F, (spX a b d : GL Ix F) ∈ Subgroup.closure (rootGens F) := fun a b d =>
    Subgroup.subset_closure (Or.inl ⟨a, b, d, rfl⟩)
  have hZ' : ∀ t : F, (spZ' t : GL Ix F) ∈ Subgroup.closure (rootGens F) := fun t =>
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))
  refine ⟨(spY s 0 0 : GL Ix F) * (spY 0 t₂ 0 : GL Ix F) * (spZ' t₁ : GL Ix F) *
      (spX (c - 1) 0 0 : GL Ix F) * (spY (1 : F) 0 0 : GL Ix F),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hY _ _ _)
      (hY _ _ _)) (hZ' _)) (hX _ _ _)) (hY _ _ _), ?_⟩
  rw [mul_smul, mul_smul, mul_smul, mul_smul, spY_smul, spX_smul, spZ'_smul, spY_smul, spY_smul]
  congr 1
  · ring
  · linear_combination ht₁
  · linear_combination hs
  · linear_combination ht₂

theorem exists_closure_smul_e1 {v : Ix → F} (hv : v ≠ 0) :
    ∃ r ∈ Subgroup.closure (rootGens F), r • vec4 (1 : F) 0 0 0 = v := by
  have h2 : ∀ x : F, x + x = 0 := CharTwo.add_self_eq_zero
  rw [vec4_eta v] at hv ⊢
  generalize v (.inl 0) = v₁ at hv ⊢
  generalize v (.inl 1) = v₂ at hv ⊢
  generalize v (.inr 0) = v₃ at hv ⊢
  generalize v (.inr 1) = v₄ at hv ⊢
  by_cases h1 : v₁ = 0
  · subst h1
    by_cases hv₂ : v₂ = 0
    · subst hv₂
      by_cases hv₃ : v₃ = 0
      · subst hv₃
        have hv₄ : v₄ ≠ 0 := fun h => hv (by rw [h, vec4_zero])
        obtain ⟨r, hr, hre⟩ := exists_closure_smul_e1_of_ne (F := F) (v₂ := 0) (v₃ := 0)
          (v₄ := v₄) hv₄
        refine ⟨(spX (0 : F) 1 0 : GL Ix F) * r,
          Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, _, _, rfl⟩)) hr, ?_⟩
        rw [mul_smul, hre, spX_smul]
        congr 1 <;> simp [h2]
      · obtain ⟨r, hr, hre⟩ := exists_closure_smul_e1_of_ne (F := F) (v₂ := 0) (v₃ := v₃)
          (v₄ := v₄) hv₃
        refine ⟨(spX (1 : F) 0 0 : GL Ix F) * r,
          Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, _, _, rfl⟩)) hr, ?_⟩
        rw [mul_smul, hre, spX_smul]
        congr 1 <;> simp [h2]
    · obtain ⟨r, hr, hre⟩ := exists_closure_smul_e1_of_ne (F := F) (v₂ := v₂) (v₃ := v₃)
        (v₄ := v₃ + v₄) hv₂
      refine ⟨(spZ (1 : F) : GL Ix F) * r,
        Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))) hr, ?_⟩
      rw [mul_smul, hre, spZ_smul]
      congr 1
      · simp [h2]
      · rw [one_mul, ← add_assoc, h2, zero_add]
  · exact exists_closure_smul_e1_of_ne h1

theorem sp4_eq_closure : sp4 F = Subgroup.closure (rootGens F) := by
  refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).mpr rootGens_subset)
  have hv : g • vec4 (1 : F) 0 0 0 ≠ 0 := by
    intro h0
    have h := congrArg (fun v => g⁻¹ • v) h0
    simp only [inv_smul_smul, smul_zero] at h
    exact one_ne_zero (congrFun h (.inl 0))
  obtain ⟨r, hr, hre⟩ := exists_closure_smul_e1 hv
  have hrsp : r ∈ sp4 F := (Subgroup.closure_le _).mpr rootGens_subset hr
  have hfix : (r⁻¹ * g) • vec4 (1 : F) 0 0 0 = vec4 1 0 0 0 := by
    rw [mul_smul, ← hre, inv_smul_smul]
  have h' := Subgroup.closure_mono fixGens_subset
    (mem_closure_of_fix (Subgroup.mul_mem _ (Subgroup.inv_mem _ hrsp) hg) hfix)
  have h'' := Subgroup.mul_mem _ hr h'
  rwa [mul_inv_cancel_left] at h''

end CFSG.Quasithin.JonesParshall
