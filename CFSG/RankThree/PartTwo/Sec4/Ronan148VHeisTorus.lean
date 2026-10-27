module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.RankThree.PartTwo.Sec4

variable {K : Type} [Field K]

theorem eq_diagUnits_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : GL (Fin 3) K} (h : M * diagTau hτ = diagTau hτ * M) :
    ∃ a b e : Kˣ, M = diagUnits a b e := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h2, div_one]
  have hττ : τ ≠ τ ^ 2 := by
    intro h2
    apply hτ1
    have : τ * (τ - 1) = 0 := by linear_combination -h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ0)
  have hM : (M : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
      diagonal ![τ, τ ^ 2, 1] * (M : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    simpa only [Units.val_mul, coe_diagTau_eq_diagonal] using this
  have z : ∀ i j : Fin 3, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    refine entry_eq_zero_of_commute_diagonal hM ?_
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hdet : (M : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := M.isUnit.map Matrix.detMonoidHom |>.ne_zero
  rw [Matrix.det_fin_three, z 0 1 (by decide), z 0 2 (by decide), z 1 0 (by decide),
    z 1 2 (by decide), z 2 0 (by decide), z 2 1 (by decide)] at hdet
  have h0 : (M : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have h1 : (M : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have h2 : (M : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  refine ⟨Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2, Units.ext ?_⟩
  rw [coe_diagUnits]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp
  · rw [z i j hij, diagonal_apply_ne _ hij]

theorem exists_cycThree_pow_mul_of_conj {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : GL (Fin 3) K} {ζ : Kˣ}
    (h : M * diagTau hτ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ) :
    ∃ k : ℕ, k < 3 ∧ (ζ : K) = τ ^ (2 * k) ∧
      ∃ a b e : Kˣ, M = cycThree ^ k * diagUnits a b e := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have := pow_three_eq_one_of_conj_eq_scalar_mul h
    have h' := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
  obtain ⟨k, hk3, hkζ⟩ : ∃ k : ℕ, k < 3 ∧ (ζ : K) = τ ^ (2 * k) := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ3 with h1 | h1 | h1
    · exact ⟨0, by norm_num, by rw [h1, mul_zero, pow_zero]⟩
    · refine ⟨2, by norm_num, ?_⟩
      rw [h1, show 2 * 2 = 3 + 1 by rfl, pow_add, hτ, one_mul, pow_one]
    · exact ⟨1, by norm_num, by rw [h1, mul_one]⟩
  refine ⟨k, hk3, hkζ, ?_⟩
  have hc := cycThree_pow_conj_diagTau hτ hτ0 k
  have hζu : ζ = Units.mk0 τ hτ0 ^ (2 * k) := Units.ext (by
    rw [hkζ, Units.val_pow_eq_pow_val, Units.val_mk0])
  have hN : ((cycThree ^ k)⁻¹ * M) * diagTau hτ = diagTau hτ * ((cycThree ^ k)⁻¹ * M) := by
    have e1 : M * diagTau hτ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ * M := by
      rw [← h]
      group
    have e2 : diagTau hτ * (cycThree ^ k)⁻¹ =
        (cycThree ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ) := by
      rw [hζu, ← hc]
      group
    calc (cycThree ^ k)⁻¹ * M * diagTau hτ
        = (cycThree ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ) * M := by
          rw [mul_assoc, e1, ← mul_assoc]
      _ = diagTau hτ * ((cycThree ^ k)⁻¹ * M) := by rw [← e2, mul_assoc]
  obtain ⟨a, b, e, he⟩ := eq_diagUnits_of_commute_diagTau hτ hτ1 hN
  exact ⟨a, b, e, by rw [← he]; group⟩

theorem cycThree_mul_diagUnits_pow_three (a b e : Kˣ) :
    (cycThree * diagUnits a b e) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (a * b * e) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, coe_cycThree, coe_diagUnits_eq,
    GeneralLinearGroup.coe_scalar, scalar_apply]
  ext i j
  simp only [pow_three, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> ring

theorem cycThree_sq_mul_diagUnits_pow_three (a b e : Kˣ) :
    (cycThree ^ 2 * diagUnits a b e) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (a * b * e) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val, coe_cycThree,
    coe_diagUnits_eq, GeneralLinearGroup.coe_scalar, scalar_apply]
  ext i j
  simp only [pow_three, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> ring

theorem exists_eq_scalar_mul_of_conj_of_conj {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : GL (Fin 3) K} {ζ μ : Kˣ}
    (h1 : M * diagTau hτ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ)
    (h2 : M * cycThree * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * cycThree) :
    ∃ (s : Kˣ) (k l : ℕ), k < 3 ∧ l < 3 ∧
      M = GeneralLinearGroup.scalar (Fin 3) s * cycThree ^ k * diagTau hτ ^ l := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  obtain ⟨k, hk, -, a, b, e, rfl⟩ := exists_cycThree_pow_mul_of_conj hτ hτ1 h1
  have hck : cycThree * cycThree ^ k = cycThree ^ k * (cycThree : GL (Fin 3) K) :=
    (Commute.self_pow cycThree k).eq
  have hs' : (cycThree ^ k)⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * cycThree ^ k =
      GeneralLinearGroup.scalar (Fin 3) μ := by
    rw [mul_assoc, ← hsc μ (cycThree ^ k), inv_mul_cancel_left]
  have h3 : diagUnits a b e * cycThree * (diagUnits a b e)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) μ * cycThree := by
    calc diagUnits a b e * cycThree * (diagUnits a b e)⁻¹ =
        (cycThree ^ k)⁻¹ * (cycThree ^ k * diagUnits a b e * cycThree *
          (cycThree ^ k * diagUnits a b e)⁻¹) * cycThree ^ k := by group
      _ = (cycThree ^ k)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * cycThree) * cycThree ^ k := by
          rw [h2]
      _ = (cycThree ^ k)⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * (cycThree * cycThree ^ k) := by
          group
      _ = ((cycThree ^ k)⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * cycThree ^ k) * cycThree := by
          rw [hck]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) μ * cycThree := by rw [hs']
  have hinv : (diagUnits a b e)⁻¹ = diagUnits a⁻¹ b⁻¹ e⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel]
    apply Units.ext
    rw [coe_diagUnits]
    simp only [Units.val_one]
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  have h4' : cycThree * diagUnits a⁻¹ b⁻¹ e⁻¹ * cycThree⁻¹ = diagUnits e⁻¹ a⁻¹ b⁻¹ :=
    cycThree_conj_diagUnits _ _ _
  have h4 : diagUnits a b e * diagUnits e⁻¹ a⁻¹ b⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ := by
    calc diagUnits a b e * diagUnits e⁻¹ a⁻¹ b⁻¹ =
        diagUnits a b e * (cycThree * (diagUnits a b e)⁻¹ * cycThree⁻¹) := by rw [hinv, h4']
      _ = (diagUnits a b e * cycThree * (diagUnits a b e)⁻¹) * cycThree⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) μ * cycThree * cycThree⁻¹ := by rw [h3]
      _ = GeneralLinearGroup.scalar (Fin 3) μ := by group
  rw [diagUnits_mul] at h4
  have ent := fun i => congrFun (congrFun (congrArg
    (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h4) i) i
  have e0 := ent 0
  have e1 := ent 1
  have e2 := ent 2
  simp [coe_diagUnits, GeneralLinearGroup.coe_scalar, scalar_apply] at e0 e1 e2
  have ha : (a : K) = (μ : K) * (e : K) := by
    have := e0
    field_simp at this
    linear_combination this
  have hb : (b : K) = (μ : K) * (a : K) := by
    have := e1
    field_simp at this
    linear_combination this
  have he : (e : K) = (μ : K) * (b : K) := by
    have := e2
    field_simp at this
    linear_combination this
  have hμ3 : (μ : K) ^ 3 = 1 := by
    have h5 : (e : K) = (μ : K) ^ 3 * e := by
      calc (e : K) = μ * b := he
        _ = μ * (μ * a) := by rw [hb]
        _ = μ * (μ * (μ * e)) := by rw [ha]
        _ = (μ : K) ^ 3 * e := by ring
    exact (mul_right_cancel₀ e.ne_zero (h5.symm.trans (one_mul _).symm))
  obtain ⟨l, hl, hμl⟩ : ∃ l : ℕ, l < 3 ∧ diagUnits a b e =
      GeneralLinearGroup.scalar (Fin 3) e * diagTau hτ ^ l := by
    have hd : ∀ l : ℕ, ((diagTau hτ ^ l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![τ ^ l, τ ^ (2 * l), 1] := by
      intro l
      rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, diagonal_pow]
      congr 1
      funext i
      fin_cases i <;> simp [← pow_mul, mul_comm]
    have key : ∀ l : ℕ, (μ : K) = τ ^ l → diagUnits a b e =
        GeneralLinearGroup.scalar (Fin 3) e * diagTau hτ ^ l := by
      intro l hl
      apply Units.ext
      rw [Units.val_mul, hd, GeneralLinearGroup.coe_scalar, scalar_apply, coe_diagUnits,
        diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i
      · simp [ha, hl, mul_comm]
      · simp [hb, ha, hl, pow_mul]
        ring
      · simp
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hμ3 with h | h | h
    · exact ⟨0, by norm_num, key 0 (by rw [h, pow_zero])⟩
    · exact ⟨1, by norm_num, key 1 (by rw [h, pow_one])⟩
    · exact ⟨2, by norm_num, key 2 h⟩
  refine ⟨e, k, l, hk, hl, ?_⟩
  rw [hμl, ← mul_assoc, hsc]

theorem eq_of_shift_eq_mul {a b e ν : K} {m : ℕ} (hm : Nat.Coprime m 3) (ha : a ^ m = 1)
    (he : e ^ m = 1) (h1 : e = ν * a) (h2 : a = ν * b) (h3 : b = ν * e) : a = b ∧ b = e := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp at hm
    · rw [zero_pow hm0.ne'] at ha
      exact zero_ne_one ha
  have hν3 : ν ^ 3 = 1 := by
    have : a = ν ^ 3 * a := by
      calc a = ν * b := h2
        _ = ν * (ν * e) := by rw [h3]
        _ = ν * (ν * (ν * a)) := by rw [h1]
        _ = ν ^ 3 * a := by ring
    exact mul_right_cancel₀ ha0 (this.symm.trans (one_mul a).symm)
  have hνm : ν ^ m = 1 := by
    have : e ^ m = ν ^ m * a ^ m := by rw [h1, mul_pow]
    rw [he, ha, mul_one] at this
    exact this.symm
  have hν : ν = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hνm, hν3⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  subst hν
  exact ⟨by rw [h2, one_mul], by rw [h3, one_mul]⟩

variable (ρ : K ≃+* K)

theorem not_const_norm_one {lam : K} {m : ℕ} (hm : Nat.Coprime m 3) (hl0 : lam ≠ 0)
    (hlm : lam ^ m = 1) (hρ : ρ lam ≠ lam) :
    ¬ (lam / ρ (ρ lam) = ρ lam / lam ∧ ρ lam / lam = ρ (ρ lam) / ρ lam) := by
  rintro ⟨h1, h2⟩
  have hρ0 : ρ lam ≠ 0 := fun h => hl0 ((map_eq_zero_iff ρ ρ.injective).mp h)
  have hρρ0 : ρ (ρ lam) ≠ 0 := fun h => hρ0 ((map_eq_zero_iff ρ ρ.injective).mp h)
  obtain ⟨ν, hν⟩ : ∃ ν, ν = ρ lam / lam := ⟨_, rfl⟩
  have hνm : ν ^ m = 1 := by
    rw [hν, div_pow, ← map_pow, hlm, map_one, div_one]
  have hν3 : ν ^ 3 = 1 := by
    have e : ν ^ 3 = (lam / ρ (ρ lam)) * (ρ lam / lam) * (ρ (ρ lam) / ρ lam) := by
      rw [h1, ← h2, ← hν]
      ring
    rw [e]
    field_simp
  have hν1 : ν = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hνm, hν3⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  apply hρ
  rw [hν1, eq_comm, div_eq_one_iff_eq hl0] at hν
  exact hν

theorem not_const_norm_two {lam : K} {m : ℕ} (hm : Nat.Coprime m 3) (hl0 : lam ≠ 0)
    (hlm : lam ^ m = 1) (hρ : ρ lam ≠ lam) :
    ¬ (lam / ρ lam = ρ (ρ lam) / lam ∧ ρ (ρ lam) / lam = ρ lam / ρ (ρ lam)) := by
  rintro ⟨h1, h2⟩
  have hρ0 : ρ lam ≠ 0 := fun h => hl0 ((map_eq_zero_iff ρ ρ.injective).mp h)
  have hρρ0 : ρ (ρ lam) ≠ 0 := fun h => hρ0 ((map_eq_zero_iff ρ ρ.injective).mp h)
  obtain ⟨ν, hν⟩ : ∃ ν, ν = lam / ρ lam := ⟨_, rfl⟩
  have hνm : ν ^ m = 1 := by
    rw [hν, div_pow, ← map_pow, hlm, map_one, div_one]
  have hν3 : ν ^ 3 = 1 := by
    have e1 : ρ (ρ lam) / lam = ν := by rw [← h1, hν]
    have e2 : ρ lam / ρ (ρ lam) = ν := by rw [← h2, e1]
    have e3 : (lam / ρ lam) * (ρ (ρ lam) / lam) * (ρ lam / ρ (ρ lam)) = 1 := by field_simp
    rw [← hν, e1, e2] at e3
    rw [← e3]
    ring
  have hν1 : ν = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hνm, hν3⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  apply hρ
  rw [hν1, eq_comm, div_eq_one_iff_eq hρ0] at hν
  exact hν.symm

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
