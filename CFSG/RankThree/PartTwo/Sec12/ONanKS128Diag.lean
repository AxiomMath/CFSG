module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128Move

open CFSG.RankThree.PartTwo.Sec4 Matrix

variable {K : Type} [Field K]

theorem diagUnits_one : diagUnits (1 : Kˣ) 1 1 = (1 : GL (Fin 3) K) := by
  apply Units.ext
  rw [coe_diagUnits]
  have h : (![((1 : Kˣ) : K), ((1 : Kˣ) : K), ((1 : Kˣ) : K)] : Fin 3 → K) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp
  rw [h, diagonal_one]
  rfl

theorem diagUnits_inv (a b c : Kˣ) :
    (diagUnits a b c : GL (Fin 3) K)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ :=
  inv_eq_of_mul_eq_one_right (by
    rw [diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, diagUnits_one])

theorem diagUnits_pow (a b c : Kˣ) (n : ℕ) :
    (diagUnits a b c : GL (Fin 3) K) ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, diagUnits_one]
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, pow_succ, pow_succ, pow_succ]

theorem diagUnits_eq_iff {a b c a' b' c' : Kˣ} :
    (diagUnits a b c : GL (Fin 3) K) = diagUnits a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    simp only [coe_diagUnits] at h'
    have h0 := congrFun (congrFun h' 0) 0
    have h1 := congrFun (congrFun h' 1) 1
    have h2 := congrFun (congrFun h' 2) 2
    simp at h0 h1 h2
    exact ⟨Units.ext h0, Units.ext h1, Units.ext h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem diagUnits_comm (a b c a' b' c' : Kˣ) :
    (diagUnits a b c : GL (Fin 3) K) * diagUnits a' b' c' =
      diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem scalar_eq_diagUnits (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c = (diagUnits c c c : GL (Fin 3) K) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

@[expose] def unitMap (τ : K ≃+* K) : Kˣ →* Kˣ := Units.map (τ : K →* K)

theorem coe_unitMap (τ : K ≃+* K) (a : Kˣ) : ((unitMap τ a : Kˣ) : K) = τ a := rfl

theorem frobGL_diagUnits (τ : K ≃+* K) (a b c : Kˣ) :
    frobGL τ (diagUnits a b c) = diagUnits (unitMap τ a) (unitMap τ b) (unitMap τ c) := by
  apply Units.ext
  rw [coe_frobGL, coe_diagUnits, coe_diagUnits, Matrix.diagonal_map (map_zero τ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem frobGL_cycThree (τ : K ≃+* K) : frobGL τ (cycThree : GL (Fin 3) K) = cycThree := by
  apply Units.ext
  rw [coe_frobGL, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cocycle_value (τ : K ≃+* K) (c₀ c₁ c₂ α₀ α₁ α₂ : Kˣ) :
    diagUnits c₀ c₁ c₂ * frobGL τ (diagUnits α₀ α₁ α₂ * cycThree) * (diagUnits c₀ c₁ c₂)⁻¹ *
        (diagUnits α₀ α₁ α₂ * cycThree)⁻¹ =
      (diagUnits (c₀ * unitMap τ α₀ * c₂⁻¹ * α₀⁻¹) (c₁ * unitMap τ α₁ * c₀⁻¹ * α₁⁻¹)
        (c₂ * unitMap τ α₂ * c₁⁻¹ * α₂⁻¹) : GL (Fin 3) K) := by
  have h1 : (cycThree : GL (Fin 3) K) * (diagUnits c₀ c₁ c₂)⁻¹ * cycThree⁻¹ =
      diagUnits c₂⁻¹ c₀⁻¹ c₁⁻¹ := by
    rw [diagUnits_inv]
    exact cycThree_conj_diagUnits _ _ _
  calc _ = diagUnits c₀ c₁ c₂ * diagUnits (unitMap τ α₀) (unitMap τ α₁) (unitMap τ α₂) *
        (cycThree * (diagUnits c₀ c₁ c₂)⁻¹ * cycThree⁻¹) * (diagUnits α₀ α₁ α₂)⁻¹ := by
        rw [map_mul, frobGL_diagUnits, frobGL_cycThree, _root_.mul_inv_rev]
        group
    _ = _ := by
        rw [h1, diagUnits_inv, diagUnits_mul, diagUnits_mul, diagUnits_mul]

theorem cycThree_conj_frame {a ω : Kˣ} (hω3 : ω ^ 3 = 1) :
    (cycThree : GL (Fin 3) K) * diagUnits a (a * ω) (a * ω ^ 2) * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * diagUnits a (a * ω) (a * ω ^ 2) := by
  rw [cycThree_conj_diagUnits, scalar_eq_diagUnits, diagUnits_mul]
  have hω3' : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have e1 : a * ω ^ 2 = ω ^ 2 * a := mul_comm _ _
  have e2 : a = ω ^ 2 * (a * ω) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-(a : K)) * hω3'
  have e3 : a * ω = ω ^ 2 * (a * ω ^ 2) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-((a : K) * ω)) * hω3'
  rw [← e1, ← e2, ← e3]

theorem exists_diagUnits_of_commute {a b c : Kˣ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {M : GL (Fin 3) K} (h : M * diagUnits a b c = diagUnits a b c * M) :
    ∃ m₀ m₁ m₂ : Kˣ, M = diagUnits m₀ m₁ m₂ := by
  have h' : (M : Matrix (Fin 3) (Fin 3) K) * diagonal ![(a : K), b, c] =
      diagonal ![(a : K), b, c] * M := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    simpa only [Units.val_mul, coe_diagUnits] using this
  have hab' : (a : K) ≠ b := fun h => hab (Units.ext h)
  have hac' : (a : K) ≠ c := fun h => hac (Units.ext h)
  have hbc' : (b : K) ≠ c := fun h => hbc (Units.ext h)
  have m01 : (M : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 :=
    entry_eq_zero_of_commute_diagonal h' (i := 0) (j := 1) (by simpa using hab')
  have m02 : (M : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 :=
    entry_eq_zero_of_commute_diagonal h' (i := 0) (j := 2) (by simpa using hac')
  have m12 : (M : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 :=
    entry_eq_zero_of_commute_diagonal h' (i := 1) (j := 2) (by simpa using hbc')
  have m10 : (M : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    entry_eq_zero_of_commute_diagonal h' (i := 1) (j := 0) (by simpa using hab'.symm)
  have m20 : (M : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    entry_eq_zero_of_commute_diagonal h' (i := 2) (j := 0) (by simpa using hac'.symm)
  have m21 : (M : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 :=
    entry_eq_zero_of_commute_diagonal h' (i := 2) (j := 1) (by simpa using hbc'.symm)
  have hM : (M : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(M : Matrix (Fin 3) (Fin 3) K) 0 0, (M : Matrix (Fin 3) (Fin 3) K) 1 1,
        (M : Matrix (Fin 3) (Fin 3) K) 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21]
  have hdet : (M : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Units.mul_inv M)
    rw [det_mul, det_one] at h1
    exact left_ne_zero_of_mul_eq_one h1
  rw [hM, det_diagonal, Fin.prod_univ_three] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hdet
  have h00 : (M : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have h11 : (M : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have h22 : (M : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11, Units.mk0 _ h22, Units.ext ?_⟩
  rw [coe_diagUnits]
  simp only [Units.val_mk0]
  exact hM

theorem eq_one_or_eq_or_eq_sq {ω s : Kˣ} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hs : s ^ 3 = 1) :
    s = 1 ∨ s = ω ∨ s = ω ^ 2 := by
  have hω3' : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
  have hs' : (s : K) ^ 3 = 1 := by simpa using congrArg Units.val hs
  have hE : (ω : K) ^ 2 + ω + 1 = 0 := by
    have h1 : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination hω3'
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hω1
    · exact h
  have h : ((s : K) - 1) * ((s : K) - ω) * ((s : K) - ω ^ 2) = 0 := by
    linear_combination hs' + ((s : K) - (s : K) ^ 2) * hE + ((s : K) - 1) * hω3'
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.1 h))
    · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
  · refine Or.inr (Or.inr (Units.ext ?_))
    rw [Units.val_pow_eq_pow_val]
    exact sub_eq_zero.1 h

theorem diagUnits_geometric (a ω t : Kˣ) (e : ℕ) :
    (diagUnits t (ω ^ e * t) (ω ^ (2 * e) * t) : GL (Fin 3) K) =
      diagUnits a (a * ω) (a * ω ^ 2) ^ e *
        GeneralLinearGroup.scalar (Fin 3) (t * (a ^ e)⁻¹) := by
  rw [diagUnits_pow, scalar_eq_diagUnits, diagUnits_mul, diagUnits_eq_iff]
  have ha := a.ne_zero
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    try ring

theorem exists_pow_mul_scalar {a ω t₀ t₁ t₂ : Kˣ} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (ha3 : a ^ 3 = 1) (h0 : t₀ ^ 3 = 1) (h1 : t₁ ^ 3 = 1) (hprod : t₀ * t₁ * t₂ = 1) :
    ∃ (e : ℕ) (ν : Kˣ), ν ^ 3 = 1 ∧
      (diagUnits t₀ t₁ t₂ : GL (Fin 3) K) =
        diagUnits a (a * ω) (a * ω ^ 2) ^ e * GeneralLinearGroup.scalar (Fin 3) ν := by
  have hs3 : (t₁ * t₀⁻¹) ^ 3 = 1 := by
    rw [mul_pow, inv_pow, h1, h0, inv_one, mul_one]
  obtain ⟨e, hse⟩ : ∃ e : ℕ, t₁ * t₀⁻¹ = ω ^ e := by
    rcases eq_one_or_eq_or_eq_sq hω1 hω3 hs3 with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, h⟩
  have ht1 : t₁ = ω ^ e * t₀ := by
    calc t₁ = (t₁ * t₀⁻¹) * t₀ := by group
      _ = ω ^ e * t₀ := by rw [hse]
  have hu3 : ((ω : K) ^ e) ^ 3 = 1 := by
    have : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hv3 : (t₀ : K) ^ 3 = 1 := by simpa using congrArg Units.val h0
  have ht2 : t₂ = ω ^ (2 * e) * t₀ := by
    apply Units.ext
    have hp : (t₀ : K) * (((ω : K) ^ e) * t₀) * t₂ = 1 := by
      have := congrArg Units.val hprod
      rw [ht1] at this
      simpa using this
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [pow_mul']
    linear_combination (-(t₂ : K) * (t₀ : K) ^ 3) * hu3 + (-(t₂ : K)) * hv3 +
      (((ω : K) ^ e) ^ 2 * (t₀ : K)) * hp
  have hν : (t₀ * (a ^ e)⁻¹) ^ 3 = 1 := by
    have : (a ^ e) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    rw [mul_pow, inv_pow, this, inv_one, mul_one, h0]
  refine ⟨e, t₀ * (a ^ e)⁻¹, hν, ?_⟩
  rw [ht1, ht2]
  exact diagUnits_geometric a ω t₀ e

theorem frame_entries_ne {a ω : Kˣ} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    a ≠ a * ω ∧ a ≠ a * ω ^ 2 ∧ a * ω ≠ a * ω ^ 2 := by
  have hω2 : ω ^ 2 ≠ 1 := fun h => hω1 (by
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h, inv_one, mul_one])
  refine ⟨fun h => hω1 ?_, fun h => hω2 ?_, fun h => hω1 ?_⟩
  · exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
  · exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
  · have h1 : ω = ω ^ 2 := mul_left_cancel (a := a) h
    have h2 : ω * 1 = ω * ω := by rw [mul_one, ← sq]; exact h1
    exact (mul_left_cancel h2).symm

end CFSG.RankThree.PartTwo.Sec12.KS128Move
