module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem exists_row1_elements {F : Type} [Field F] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ z₀ t₀ : GL (Fin 4) F,
      (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1] ∧
      (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1] := by
  have h0 := ne_zero_of_omega hω
  obtain ⟨z₀, hz⟩ := exists_gl_diagonal ![ω, ω, ω, 1] (by intro i; fin_cases i <;> simp [h0])
  obtain ⟨t₀, ht⟩ := exists_gl_diagonal ![ω, ω ^ 2, 1, 1] (by intro i; fin_cases i <;> simp [h0])
  exact ⟨z₀, t₀, hz, ht⟩

theorem exists_row2_elements {F : Type} [Field F] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F,
      (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]) ∧
      (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1]) := by
  have h0 := ne_zero_of_omega hω
  obtain ⟨z₀, hz⟩ := exists_gl_diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2])
    (by rintro (i | i) <;> fin_cases i <;> simp [h0])
  obtain ⟨t₀, ht⟩ := exists_gl_diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])
    (by rintro (i | i) <;> fin_cases i <;> simp [h0])
  exact ⟨z₀, t₀, hz, ht⟩

theorem exists_row3_elements {F : Type} [Field F] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
      (z₀ : Matrix _ _ F) =
        Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])) ∧
      (t₀ : Matrix _ _ F) =
        Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1])) := by
  have h0 := ne_zero_of_omega hω
  obtain ⟨z₀, hz⟩ := exists_gl_diagonal
    (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]))
    (by rintro (i | i | i) <;> fin_cases i <;> simp [h0])
  obtain ⟨t₀, ht⟩ := exists_gl_diagonal
    (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))
    (by rintro (i | i | i) <;> fin_cases i <;> simp [h0])
  exact ⟨z₀, t₀, hz, ht⟩

private theorem k328xl_exists_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] {F : Type}
    [Field F] (A B : Matrix n n F) (h : A * B = 1) :
    ∃ z : GL n F, (z : Matrix n n F) = A :=
  ⟨⟨A, B, h, mul_eq_one_comm.1 h⟩, rfl⟩

private theorem k328xl_rhoOmega_mul {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    rhoOmega F * !![(-1 : F), 1; 1, 0] = 1 := by
  rw [rhoOmega]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem k328xl_rhoOmega_sq_mul {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    (rhoOmega F) ^ 2 * (!![(-1 : F), 1; 1, 0]) ^ 2 = 1 := by
  rw [pow_two, pow_two]
  calc (rhoOmega F * rhoOmega F) * (!![(-1 : F), 1; 1, 0] * !![(-1 : F), 1; 1, 0])
      = rhoOmega F * (rhoOmega F * !![(-1 : F), 1; 1, 0]) * !![(-1 : F), 1; 1, 0] := by
        noncomm_ring
    _ = 1 := by simp [k328xl_rhoOmega_mul]

private theorem k328xl_blockDiag3_six_mul {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ A₂ B₀ B₁ B₂ : Matrix (Fin 2) (Fin 2) F) :
    blockDiag3 F 6 A₀ A₁ A₂ * blockDiag3 F 6 B₀ B₁ B₂ =
      blockDiag3 F 6 (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag3, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem k328xl_blockDiag3_seven_mul {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ A₂ B₀ B₁ B₂ : Matrix (Fin 2) (Fin 2) F) :
    blockDiag3 F 7 A₀ A₁ A₂ * blockDiag3 F 7 B₀ B₁ B₂ =
      blockDiag3 F 7 (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private theorem k328xl_blockDiag3_six_one {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    blockDiag3 F 6 1 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag3, Matrix.one_apply]

private theorem k328xl_blockDiag3_seven_one {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    blockDiag3 F 7 1 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag3, Matrix.one_apply]

theorem exists_row4_elements {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ z₀ t₀ : GL (Fin 6) F,
      (z₀ : Matrix (Fin 6) (Fin 6) F) = blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) ∧
      (t₀ : Matrix (Fin 6) (Fin 6) F) = blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1 := by
  have hz : blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) *
      blockDiag3 F 6 !![(-1 : F), 1; 1, 0] !![(-1 : F), 1; 1, 0] !![(-1 : F), 1; 1, 0] =
      1 := by
    rw [k328xl_blockDiag3_six_mul, k328xl_rhoOmega_mul]
    exact k328xl_blockDiag3_six_one
  have ht : blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1 *
      blockDiag3 F 6 !![(-1 : F), 1; 1, 0] (!![(-1 : F), 1; 1, 0] ^ 2) 1 = 1 := by
    rw [k328xl_blockDiag3_six_mul, k328xl_rhoOmega_mul, k328xl_rhoOmega_sq_mul, mul_one]
    exact k328xl_blockDiag3_six_one
  obtain ⟨z₀, hz0⟩ := k328xl_exists_of_mul_eq_one _ _ hz
  obtain ⟨t₀, ht0⟩ := k328xl_exists_of_mul_eq_one _ _ ht
  exact ⟨z₀, t₀, hz0, ht0⟩

theorem exists_row5_elements {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ z₀ t₀ : GL (Fin 7) F,
      (z₀ : Matrix (Fin 7) (Fin 7) F) = blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) ∧
      (t₀ : Matrix (Fin 7) (Fin 7) F) = blockDiag3 F 7 (rhoOmega F) (rhoOmega F ^ 2) 1 := by
  have hz : blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) *
      blockDiag3 F 7 !![(-1 : F), 1; 1, 0] !![(-1 : F), 1; 1, 0] !![(-1 : F), 1; 1, 0] =
      1 := by
    rw [k328xl_blockDiag3_seven_mul, k328xl_rhoOmega_mul]
    exact k328xl_blockDiag3_seven_one
  have ht : blockDiag3 F 7 (rhoOmega F) (rhoOmega F ^ 2) 1 *
      blockDiag3 F 7 !![(-1 : F), 1; 1, 0] (!![(-1 : F), 1; 1, 0] ^ 2) 1 = 1 := by
    rw [k328xl_blockDiag3_seven_mul, k328xl_rhoOmega_mul, k328xl_rhoOmega_sq_mul, mul_one]
    exact k328xl_blockDiag3_seven_one
  obtain ⟨z₀, hz0⟩ := k328xl_exists_of_mul_eq_one _ _ hz
  obtain ⟨t₀, ht0⟩ := k328xl_exists_of_mul_eq_one _ _ ht
  exact ⟨z₀, t₀, hz0, ht0⟩

private theorem k328xl_rhoL_mul {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ B₀ B₁ : Matrix (Fin 3) (Fin 3) F) :
    rhoL F A₀ A₁ * rhoL F B₀ B₁ =
      rhoL F (A₀ * B₀ + A₁ * B₁) (A₀ * B₁ + A₁ * B₀ + A₁ * B₁) := by
  simp only [rhoL]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

private theorem k328xl_rhoL_one {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    rhoL F 1 0 = 1 := by
  rw [rhoL, add_zero, Matrix.fromBlocks_one]

private theorem k328xl_rhoL_zero_one_mul {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] :
    rhoL F 0 1 * rhoL F 1 1 = 1 := by
  rw [k328xl_rhoL_mul, ← k328xl_rhoL_one]
  congr 1
  · simp
  · simp only [Matrix.zero_mul, Matrix.one_mul, zero_add]
    rw [CharTwo.add_self_eq_zero]

private theorem k328xl_diag_arg1 {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    Matrix.diagonal (![0, 1, 1] : Fin 3 → F) * Matrix.diagonal (![1, 0, 1] : Fin 3 → F) +
      Matrix.diagonal (![1, 1, 0] : Fin 3 → F) * Matrix.diagonal (![1, 1, 0] : Fin 3 → F) =
      1 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add, ← Matrix.diagonal_one']
  congr 1
  ext i
  fin_cases i <;> norm_num

private theorem k328xl_diag_arg2 {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    Matrix.diagonal (![0, 1, 1] : Fin 3 → F) * Matrix.diagonal (![1, 1, 0] : Fin 3 → F) +
      Matrix.diagonal (![1, 1, 0] : Fin 3 → F) * Matrix.diagonal (![1, 0, 1] : Fin 3 → F) +
      Matrix.diagonal (![1, 1, 0] : Fin 3 → F) * Matrix.diagonal (![1, 1, 0] : Fin 3 → F) =
      0 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_add,
    ← Matrix.diagonal_zero]
  congr 1
  ext i
  fin_cases i <;> simp [CharTwo.add_self_eq_zero]

theorem exists_row7_elements {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    ∃ z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F,
      (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1 ∧
      (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]) := by
  have hz : rhoL F 0 1 * rhoL F 1 1 = 1 := k328xl_rhoL_zero_one_mul
  have ht : rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]) *
      rhoL F (Matrix.diagonal ![1, 0, 1]) (Matrix.diagonal ![1, 1, 0]) = 1 := by
    rw [k328xl_rhoL_mul, k328xl_diag_arg1, k328xl_diag_arg2, k328xl_rhoL_one]
  obtain ⟨z₀, hz0⟩ := k328xl_exists_of_mul_eq_one _ _ hz
  obtain ⟨t₀, ht0⟩ := k328xl_exists_of_mul_eq_one _ _ ht
  exact ⟨z₀, t₀, hz0, ht0⟩

private def k328xa_w {F : Type} [Field F] [CharP F 2] : F →+ F :=
  AddMonoidHom.mk' (fun u => u ^ 2 + u) fun u v => by
    rw [CharTwo.add_sq]
    ring

private theorem k328xa_w_apply {F : Type} [Field F] [CharP F 2] (u : F) :
    k328xa_w (F := F) u = u ^ 2 + u := rfl

private theorem k328xa_ker_mem {F : Type} [Field F] [CharP F 2] (u : F) :
    u ∈ (k328xa_w (F := F)).ker ↔ u = 0 ∨ u = 1 := by
  rw [AddMonoidHom.mem_ker, k328xa_w_apply]
  constructor
  · intro h
    have hmul : u * (u + 1) = 0 := by
      rw [mul_add, mul_one, ← pow_two]
      exact h
    rcases mul_eq_zero.mp hmul with h0 | h1
    · exact Or.inl h0
    · exact Or.inr ((CharTwo.add_eq_zero).mp h1)
  · rintro (rfl | rfl)
    · ring
    · rw [one_pow]
      exact CharTwo.add_self_eq_zero 1

private theorem k328xa_card_ker {F : Type} [Field F] [CharP F 2] :
    Nat.card (k328xa_w (F := F)).ker = 2 := by
  rw [Nat.card_eq_two_iff'
    (⟨0, by rw [k328xa_ker_mem]; exact Or.inl rfl⟩ : (k328xa_w (F := F)).ker)]
  refine ⟨⟨1, ?_⟩, ?_, ?_⟩
  · rw [k328xa_ker_mem]; exact Or.inr rfl
  · intro h
    exact one_ne_zero (congrArg Subtype.val h)
  · intro y hy
    apply Subtype.ext
    have hyv : y.1 ≠ 0 := by
      intro h0
      exact hy (Subtype.ext h0)
    rcases (k328xa_ker_mem y.1).mp y.2 with h0 | h1
    · exact absurd h0 hyv
    · exact h1

private theorem k328xa_b_ne_zero {F : Type} [Field F] [Fintype F] [CharP F 2]
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (R := F) 2) c
  exact hbc s (by rw [hb, zero_mul, add_zero, hs, pow_two, CharTwo.add_self_eq_zero])

private theorem k328xa_range_index {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) : (k328xa_w (F := F)).range.index = 2 := by
  have hcardF : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]
  have hkermul := (k328xa_w (F := F)).ker.card_mul_index
  rw [k328xa_card_ker (F := F), hcardF] at hkermul
  have hkeridx : (k328xa_w (F := F)).ker.index = 4 := by omega
  have hrangecard : Nat.card (k328xa_w (F := F)).range = 4 := by
    rw [← AddSubgroup.index_ker (k328xa_w (F := F)), hkeridx]
  have hrmul := (k328xa_w (F := F)).range.card_mul_index
  rw [hrangecard, hcardF] at hrmul
  omega

private theorem k328xa_one_notMem_range {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) : (1 : F) ∉ (k328xa_w (F := F)).range := by
  classical
  intro h1
  rw [AddMonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  rw [k328xa_w_apply] at hu
  have hu2 : u ^ 2 = 1 + u := by
    rw [← hu, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hu3 : u ^ 3 = 1 := by
    calc u ^ 3 = u ^ 2 * u := by ring
      _ = (1 + u) * u := by rw [hu2]
      _ = u ^ 2 + u := by ring
      _ = 1 := hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, one_pow, CharTwo.add_self_eq_zero] at hu
    exact zero_ne_one hu
  let x : Fˣ := Units.mk0 u hu0
  have hx3 : x ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact hu3
  have hx1 : x ≠ 1 := by
    intro h
    apply hu1
    have hval : (x : F) = 1 := by
      rw [h]
      rfl
    rwa [Units.val_mk0] at hval
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd : orderOf x ∣ Fintype.card Fˣ := orderOf_dvd_card
  rw [Fintype.card_units, hF, hord] at hdvd
  norm_num at hdvd

private theorem k328xa_cb_notMem_range {F : Type} [Field F] [Fintype F] [CharP F 2]
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    c / b ^ 2 ∉ (k328xa_w (F := F)).range := by
  intro hmem
  rw [AddMonoidHom.mem_range] at hmem
  obtain ⟨u, hu⟩ := hmem
  rw [k328xa_w_apply] at hu
  have hb : b ≠ 0 := k328xa_b_ne_zero b c hbc
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  refine hbc (b * u) ?_
  have hbu : b ^ 2 * (u ^ 2 + u) = c := by
    rw [hu]
    field_simp
  calc (b * u) ^ 2 + b * (b * u) + c = b ^ 2 * (u ^ 2 + u) + c := by ring
    _ = c + c := by rw [hbu]
    _ = 0 := CharTwo.add_self_eq_zero c

theorem exists_alpha_of_irreducible {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 8)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : ∃ α : F, α ^ 2 + α = 1 + c / b ^ 2 := by
  classical
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  have h1 : (1 : F) ∉ (k328xa_w (F := F)).range := k328xa_one_notMem_range hF
  have hc : c / b ^ 2 ∉ (k328xa_w (F := F)).range := k328xa_cb_notMem_range b c hbc
  have hidx : (k328xa_w (F := F)).range.index = 2 := k328xa_range_index hF
  obtain ⟨a, ha⟩ :=
    (AddSubgroup.index_eq_two_iff (H := (k328xa_w (F := F)).range)).mp hidx
  have h1a : (1 : F) + a ∈ (k328xa_w (F := F)).range := by
    rcases ha 1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h h1
  have hca : c / b ^ 2 + a ∈ (k328xa_w (F := F)).range := by
    rcases ha (c / b ^ 2) with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hc
  have hsum : (1 + a) + (c / b ^ 2 + a) ∈ (k328xa_w (F := F)).range :=
    (k328xa_w (F := F)).range.add_mem h1a hca
  have heq : (1 + a) + (c / b ^ 2 + a) = 1 + c / b ^ 2 := by
    have haa : a + a = 0 := CharTwo.add_self_eq_zero a
    calc (1 + a) + (c / b ^ 2 + a) = (1 + c / b ^ 2) + (a + a) := by ring
      _ = 1 + c / b ^ 2 := by rw [haa, add_zero]
  rw [heq] at hsum
  rw [AddMonoidHom.mem_range] at hsum
  obtain ⟨α, hα⟩ := hsum
  exact ⟨α, by rw [← k328xa_w_apply]; exact hα⟩

theorem exists_row8_elements {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∃ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) ∧
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) := by
  intro e f u v
  have _ : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := hbc
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  let Zm : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v]))
  let Zi : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    ofColumns F (Sum.elim ![f 1, f 0, e 2]
      (Sum.elim ![e 1 + f 0, e 0 + f 1, f 2]
        ![(α + 1) • u + b⁻¹ • v, (c / b) • u + α • v]))
  let Tm : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v]))
  let Ti : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    ofColumns F (Sum.elim ![e 0 + e 1, e 0, e 2]
      (Sum.elim ![f 1, f 0 + f 1, f 2] ![u, v]))
  have hZ : Zm * Zi = 1 := by
    ext i j
    rcases i with (i | i | i) <;> rcases j with (j | j | j) <;>
      fin_cases i <;> fin_cases j <;>
      simp [Zm, Zi, e, f, u, v, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
        ofColumns, bv, Pi.single_apply]
    all_goals
      first
      | linear_combination h2
      | linear_combination hα + (c / b ^ 2) * h2
      | linear_combination (α * c / b) * h2
      | linear_combination (b⁻¹ * (α + 1)) * h2
  have hT : Tm * Ti = 1 := by
    ext i j
    rcases i with (i | i | i) <;> rcases j with (j | j | j) <;>
      fin_cases i <;> fin_cases j <;>
      simp [Tm, Ti, e, f, u, v, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
        ofColumns, bv, Pi.single_apply]
    all_goals
      first
      | linear_combination h2
      | rw [← Nat.cast_zero (R := F)]
        congr 1
  obtain ⟨z₀, hz₀⟩ := exists_gl_of_mul_eq_one Zm Zi hZ
  obtain ⟨t₀, ht₀⟩ := exists_gl_of_mul_eq_one Tm Ti hT
  exact ⟨z₀, t₀, hz₀, ht₀⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
