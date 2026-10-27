module

public import CFSG.Walter.Ree.Thompson2.BaseRel

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}

theorem pp_mul (α β γ ξ η ζ : k) :
    pp σ α β γ * pp σ ξ η ζ = pp σ (α + ξ) (β + η + α * σ ξ - σ α * ξ)
      (ζ + γ + ξ * β + σ α * ξ ^ 2 + α * ξ * σ ξ - α ^ 2 * σ ξ) :=
  ThompsonN.mul_P α β γ ξ η ζ

theorem pp_inv (α β γ : k) : (pp σ α β γ)⁻¹ = pp σ (-α) (-β) (α * β - γ) :=
  ThompsonN.inv_P α β γ

omit [CharP k 3] in
theorem pp_eq_iff {α β γ α' β' γ' : k} :
    pp σ α β γ = pp σ α' β' γ' ↔ α = α' ∧ β = β' ∧ γ = γ' := by
  constructor
  · intro h
    exact ⟨congrArg ThompsonN.α h, congrArg ThompsonN.β h, congrArg ThompsonN.γ h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem pp_zero : pp σ (0 : k) 0 0 = 1 := rfl

theorem pp_mem_P (α β γ : k) : pp σ α β γ ∈ ThompsonN.P σ := rfl

omit [CharP k 3] in
theorem pp_α (α β γ : k) : (pp σ α β γ).α = α := rfl

omit [CharP k 3] in
theorem pp_β (α β γ : k) : (pp σ α β γ).β = β := rfl

omit [CharP k 3] in
theorem pp_γ (α β γ : k) : (pp σ α β γ).γ = γ := rfl

theorem eq_pp_of_mem_P {x : ThompsonN k σ} (hx : x ∈ ThompsonN.P σ) :
    x = pp σ x.α x.β x.γ :=
  ThompsonN.eq_of_mem_P hx

theorem pp_cube (α β γ : k) : pp σ α β γ ^ 3 = pp σ 0 0 (σ α * α ^ 2) := by
  have h3 := ThompsonN.three_eq_zero (K := k)
  rw [pow_three', pp_mul, pp_mul, pp_eq_iff]
  simp only [map_add]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination α * h3
  · linear_combination β * h3
  · linear_combination (γ + α * β) * h3

theorem tT_conj_pp (α β γ : k) : (tT σ)⁻¹ * pp σ α β γ * tT σ = pp σ α β (γ - α) := by
  simp only [tT]
  rw [pp_inv, pp_mul, pp_mul, pp_eq_iff]
  simp only [map_zero, map_neg]
  refine ⟨by ring, by ring, by ring⟩

theorem J_conj_pp (α β γ : k) :
    (ThompsonN.J σ)⁻¹ * pp σ α β γ * ThompsonN.J σ = pp σ (-α) β (-γ) :=
  ThompsonN.J_conj α β γ

theorem torus_conj_pp (κ : kˣ) (α β γ : k) :
    (ThompsonN.torus σ κ)⁻¹ * pp σ α β γ * ThompsonN.torus σ κ =
      pp σ (α * κ) (β * (κ * σ κ)) (γ * (κ ^ 2 * σ κ)) :=
  ThompsonN.torus_conj κ α β γ

theorem J_mul_pp (γ : k) : ThompsonN.J σ * pp σ 0 0 γ = ⟨-1, 0, 0, γ⟩ := by
  ext <;> simp [ThompsonN.J, ThompsonN.torus, pp, ThompsonN.mul_def, thompsonMul]

theorem pp_center_comm (γ ξ η ζ : k) :
    pp σ 0 0 γ * pp σ ξ η ζ = pp σ ξ η ζ * pp σ 0 0 γ := by
  rw [pp_mul, pp_mul, pp_eq_iff]
  simp only [map_zero]
  refine ⟨by ring, by ring, by ring⟩

theorem pp_center_pow (γ : k) (m : ℕ) : pp σ 0 0 γ ^ m = pp σ 0 0 (m * γ) := by
  induction m with
  | zero => simp [pp_zero]
  | succ m ih =>
    rw [pow_succ, ih, pp_mul, pp_eq_iff]
    simp only [map_zero]
    push_cast
    refine ⟨by ring, by ring, by ring⟩

theorem alpha_pow {x : ThompsonN k σ} (hx : x ∈ ThompsonN.P σ) (m : ℕ) :
    (x ^ m).α = m * x.α := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ThompsonN.mul_α, ih, ThompsonN.mem_P.mp hx]
    push_cast
    ring

theorem invol_comm_tT {n : ThompsonN k σ} (h2 : n * n = 1) (h1 : n ≠ 1)
    (hc : n * tT σ = tT σ * n) : ∃ γ : k, n = ThompsonN.J σ * pp σ 0 0 γ := by
  obtain ⟨κ, α, β, γ⟩ := n
  have h2k : (2 : k) ≠ 0 := two_ne_zero_of_charThree
  have hκ : (κ : k) * κ = 1 := by
    have := congrArg (fun x : ThompsonN k σ => (x.κ : k)) h2
    simpa using this
  rcases mul_self_eq_one_iff.mp hκ with hκ1 | hκ1
  ·
    exfalso
    have hκ' : κ = 1 := Units.ext hκ1
    subst hκ'
    apply h1
    have hsq : pp σ α β γ * pp σ α β γ = pp σ 0 0 0 := h2
    rw [pp_mul, pp_eq_iff] at hsq
    obtain ⟨ha, hb, hg⟩ := hsq
    have ha0 : α = 0 :=
      (mul_eq_zero.mp (show 2 * α = 0 by linear_combination ha)).resolve_left h2k
    subst ha0
    simp only [map_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_pow two_ne_zero] at hb hg
    have hb0 : β = 0 :=
      (mul_eq_zero.mp (show 2 * β = 0 by linear_combination hb)).resolve_left h2k
    have hg0 : γ = 0 :=
      (mul_eq_zero.mp (show 2 * γ = 0 by linear_combination hg)).resolve_left h2k
    subst hb0 hg0
    rfl
  · have hκ' : κ = -1 := Units.ext (by simpa using hκ1)
    subst hκ'
    have hb : β = 0 := by
      have := congrArg ThompsonN.β h2
      simp only [ThompsonN.mul_β, ThompsonN.one_β, Units.val_neg, Units.val_one, map_neg,
        map_one] at this
      exact (mul_eq_zero.mp (show 2 * β = 0 by linear_combination this)).resolve_left h2k
    subst hb
    have ha : α = 0 := by
      have := congrArg ThompsonN.γ hc
      simp only [tT, pp, ThompsonN.mul_γ, Units.val_neg, Units.val_one, map_neg, map_one,
        map_zero] at this
      linear_combination -this
    subst ha
    exact ⟨γ, (J_mul_pp γ).symm⟩

theorem mem_P_of_pow_nine [Fintype k] {x : ThompsonN k σ} (hx : x ^ 9 = 1) :
    x ∈ ThompsonN.P σ := by
  classical
  rw [ThompsonN.mem_P]
  have h9 : x.κ ^ 9 = 1 := by
    have := congrArg (ThompsonN.kappaHom σ) hx
    rwa [map_pow, map_one] at this
  have hq : Fintype.card kˣ = Fintype.card k - 1 := Fintype.card_units k
  have h1 : orderOf x.κ ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have h2 : orderOf x.κ ∣ Fintype.card k - 1 := hq ▸ orderOf_dvd_card
  have h3 : ¬ 3 ∣ Fintype.card k - 1 := by
    have hc : (Fintype.card k : k) = 0 := FiniteField.cast_card_eq_zero k
    have h3k : 3 ∣ Fintype.card k := by
      rwa [CharP.cast_eq_zero_iff k 3] at hc
    have hpos : 0 < Fintype.card k := Fintype.card_pos
    omega
  have hcop : Nat.Coprime 9 (Fintype.card k - 1) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end CFSG.Walter.Ree.T2.BaseGrp
