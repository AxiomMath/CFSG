module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix

namespace Z3Field

section NumberTheory

theorem one_le_padicValNat_three {m : ℕ} (hm3 : m % 3 = 0) (hm0 : 0 < m) :
    1 ≤ padicValNat 3 m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact one_le_padicValNat_of_dvd hm0.ne' (Nat.dvd_of_mod_eq_zero hm3)

theorem three_pow_succ_dvd {m : ℕ} (hm3 : m % 3 = 0) :
    3 ^ (padicValNat 3 m + 1) ∣ m * (m ^ 2 + 3 * m + 3) := by
  rw [pow_succ]
  refine mul_dvd_mul pow_padicValNat_dvd ?_
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hm3
  exact ⟨3 * k ^ 2 + 3 * k + 1, by rw [hk]; ring⟩

theorem not_three_pow_succ_dvd {m : ℕ} (hm0 : 0 < m) : ¬ 3 ^ (padicValNat 3 m + 1) ∣ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact pow_succ_padicValNat_not_dvd hm0.ne'

theorem not_three_pow_succ_dvd_mul {m : ℕ} (hm3 : m % 3 = 0) (hm0 : 0 < m) :
    ¬ 3 ^ (padicValNat 3 m + 1) ∣ m * (m + 2) := by
  intro h
  have hc : Nat.Coprime (3 ^ (padicValNat 3 m + 1)) (m + 2) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  exact not_three_pow_succ_dvd hm0 (hc.dvd_of_dvd_mul_right h)

theorem not_three_pow_succ_dvd_add_two {m : ℕ} (hm3 : m % 3 = 0) :
    ¬ 3 ^ (padicValNat 3 m + 1) ∣ m + 2 := fun h => by
  have : 3 ∣ m + 2 := (dvd_pow_self 3 (Nat.succ_ne_zero _)).trans h
  omega

theorem not_three_pow_succ_dvd_sq {m : ℕ} (hm3 : m % 3 = 0) :
    ¬ 3 ^ (padicValNat 3 m + 1) ∣ m ^ 2 + 2 * m + 2 := fun h => by
  have h3 : 3 ∣ m ^ 2 + 2 * m + 2 := (dvd_pow_self 3 (Nat.succ_ne_zero _)).trans h
  have h3m : 3 ∣ m := Nat.dvd_of_mod_eq_zero hm3
  have h4 : 3 ∣ m ^ 2 + 2 * m := dvd_add (dvd_pow h3m two_ne_zero) (dvd_mul_of_dvd_right h3m 2)
  have := (Nat.dvd_add_right h4).mp h3
  omega

theorem three_pow_succ_dvd_cube_add_one (k : ℕ) :
    3 ^ (padicValNat 3 ((3 * k + 1) * (3 * k + 3)) + 1) ∣ (3 * k + 2) ^ 3 + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 3 ^ padicValNat 3 ((3 * k + 1) * (3 * k + 3)) ∣ 3 * k + 3 := by
    have hcop : Nat.Coprime (3 ^ padicValNat 3 ((3 * k + 1) * (3 * k + 3))) (3 * k + 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
    exact hcop.dvd_of_dvd_mul_left pow_padicValNat_dvd
  rw [pow_succ]
  have h2 : (3 * k + 2) ^ 3 + 1 = (3 * k + 3) * (9 * k ^ 2 + 9 * k + 3) := by ring
  rw [h2]
  exact mul_dvd_mul h1 ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩

end NumberTheory

section Zeta

variable {K : Type} [Field K]

theorem exists_unit_orderOf_three_pow [Finite K] {m : ℕ} (hK : Nat.card K = (m + 1) ^ 3)
    (hm3 : m % 3 = 0) (hm0 : 0 < m) : ∃ ζ : Kˣ, orderOf ζ = 3 ^ (padicValNat 3 m + 1) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Kˣ)
  have hcard : Nat.card Kˣ = m * (m ^ 2 + 3 * m + 3) := by
    rw [Nat.card_units, hK]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hdvd : 3 ^ (padicValNat 3 m + 1) ∣ orderOf g := by
    rw [hg, hcard]
    exact three_pow_succ_dvd hm3
  refine ⟨g ^ (orderOf g / 3 ^ (padicValNat 3 m + 1)), orderOf_pow_orderOf_div ?_ hdvd⟩
  rw [hg, hcard]
  exact (Nat.mul_pos hm0 (by positivity)).ne'

theorem pow_three_ne_one {v : ℕ} (hv : 1 ≤ v) {ζ : Kˣ} (hζ : orderOf ζ = 3 ^ (v + 1)) :
    ζ ^ 3 ≠ 1 := by
  intro h
  have h1 : 3 ^ (v + 1) ∣ 3 ^ 1 := by
    rw [← hζ, pow_one]
    exact orderOf_dvd_of_pow_eq_one h
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h1
  omega

theorem eq_one_of_pow_three {v : ℕ} (hv : 1 ≤ v) {ζ c : Kˣ} (hζ : orderOf ζ = 3 ^ (v + 1))
    (hc3 : c ^ 3 = 1) (hc : c = ζ⁻¹ ∨ c = ζ ∨ c = 1) : c = 1 := by
  rcases hc with rfl | rfl | h
  · exfalso
    exact pow_three_ne_one hv hζ (by simpa using hc3)
  · exact absurd hc3 (pow_three_ne_one hv hζ)
  · exact h

theorem frob_moves_zeta [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {m : ℕ} (hm : p ^ (f / 3) = m + 1) (hm3 : m % 3 = 0)
    (hm0 : 0 < m) {ζ : Kˣ} (hζ : orderOf ζ = 3 ^ (padicValNat 3 m + 1)) {τ : K ≃+* K}
    (hτ : orderOf τ = 3) : τ (ζ : K) ≠ ζ ∧ τ (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := by
  obtain ⟨h3f, hfr⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hf hK hτ
  have key : ∀ e : ℕ, (∀ x : K, τ x = x ^ e) → (e = m + 1 ∨ e = (m + 1) ^ 2) →
      τ (ζ : K) ≠ ζ ∧ τ (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := by
    intro e he hee
    have hτζ : τ (ζ : K) = ((ζ ^ e : Kˣ) : K) := by
      rw [he, Units.val_pow_eq_pow_val]
    rw [hτζ]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : ζ ^ e = ζ := Units.ext h
      rcases hee with rfl | rfl
      · have h2 : ζ ^ m = 1 := by
          have : ζ ^ m * ζ = 1 * ζ := by rw [← pow_succ, h1, one_mul]
          exact mul_right_cancel this
        exact not_three_pow_succ_dvd hm0 (hζ ▸ orderOf_dvd_of_pow_eq_one h2)
      · have h2 : ζ ^ (m * (m + 2)) = 1 := by
          have : ζ ^ (m * (m + 2)) * ζ = 1 * ζ := by
            rw [← pow_succ, one_mul, ← h1]
            congr 1
            ring
          exact mul_right_cancel this
        exact not_three_pow_succ_dvd_mul hm3 hm0 (hζ ▸ orderOf_dvd_of_pow_eq_one h2)
    · have h1 : ζ ^ e = ζ⁻¹ := Units.ext h
      rcases hee with rfl | rfl
      · have h2 : ζ ^ (m + 2) = 1 := by
          rw [pow_succ, h1, inv_mul_cancel]
        exact not_three_pow_succ_dvd_add_two hm3 (hζ ▸ orderOf_dvd_of_pow_eq_one h2)
      · have h2 : ζ ^ (m ^ 2 + 2 * m + 2) = 1 := by
          have : m ^ 2 + 2 * m + 2 = (m + 1) ^ 2 + 1 := by ring
          rw [this, pow_succ, h1, inv_mul_cancel]
        exact not_three_pow_succ_dvd_sq hm3 (hζ ▸ orderOf_dvd_of_pow_eq_one h2)
  rcases hfr with hfr | hfr
  · exact key _ hfr (Or.inl hm)
  · refine key _ hfr (Or.inr ?_)
    rw [show 2 * f / 3 = f / 3 * 2 by omega, pow_mul, hm]

end Zeta

section Torus

variable {K : Type} [Field K]

theorem det_diagUnits_inv (ζ : Kˣ) :
    ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_diagUnits, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem diagUnits_pow_eq_one {ζ : Kˣ} {N : ℕ} (h : ζ ^ N = 1) :
    (diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) ^ N = 1 := by
  have h' : (ζ : K) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  apply Units.ext
  show ((diagUnits ζ ζ⁻¹ 1 ^ N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    (1 : Matrix (Fin 3) (Fin 3) K)
  rw [Units.val_pow_eq_pow_val, coe_diagUnits, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [Pi.pow_apply, h']

theorem core_gl (τ : K ≃+* K) (H : GL (Fin 3) K) (ζ c : Kˣ)
    (h : H * frobGL τ (H⁻¹ * diagUnits ζ ζ⁻¹ 1 * H) * H⁻¹ =
      diagUnits ζ ζ⁻¹ 1 * GeneralLinearGroup.scalar (Fin 3) c) :
    (c = ζ⁻¹ ∨ c = ζ ∨ c = 1) ∧
      (c = 1 → τ (ζ : K) = ζ ∨ τ (ζ : K) = ((ζ⁻¹ : Kˣ) : K)) := by
  have hBX : (H * (frobGL τ H)⁻¹) * frobGL τ (diagUnits ζ ζ⁻¹ 1) =
      diagUnits ζ ζ⁻¹ 1 * GeneralLinearGroup.scalar (Fin 3) c * (H * (frobGL τ H)⁻¹) := by
    have h' := congrArg (fun y => y * (H * (frobGL τ H)⁻¹)) h
    simp only [map_mul, map_inv] at h'
    calc (H * (frobGL τ H)⁻¹) * frobGL τ (diagUnits ζ ζ⁻¹ 1)
        = H * ((frobGL τ H)⁻¹ * frobGL τ (diagUnits ζ ζ⁻¹ 1) * frobGL τ H) * H⁻¹ *
            (H * (frobGL τ H)⁻¹) := by group
      _ = _ := h'
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 3) K, B * frobGL τ (diagUnits ζ ζ⁻¹ 1) =
      diagUnits ζ ζ⁻¹ 1 * GeneralLinearGroup.scalar (Fin 3) c * B := ⟨_, hBX⟩
  have hBm : (B : Matrix (Fin 3) (Fin 3) K) *
      ((frobGL τ (diagUnits ζ ζ⁻¹ 1) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (B : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K)) hB
    simpa only [Units.val_mul] using this
  have hXτ : ((frobGL τ (diagUnits ζ ζ⁻¹ 1) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
    rw [coe_frobGL, coe_diagUnits, Matrix.diagonal_map (map_zero τ),
      Matrix.diagonal_mulVec_single]
    simp
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K,
      w = (B : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 1 : Fin 3 → K) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = Pi.single 2 1 := by
      rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have := congrFun h1 2
    simp at this
  have h1 : w = ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ (Pi.single 2 1 : Fin 3 → K)) hBm
    simp only [← Matrix.mulVec_mulVec, hXτ] at this
    rw [← hw] at this
    exact this
  have hkey : ∀ i : Fin 3, w i =
      (![(ζ : K), ((ζ⁻¹ : Kˣ) : K), ((1 : Kˣ) : K)] i) * ((c : K) * w i) := by
    intro i
    have h2 := congrFun h1 i
    rw [coe_diagUnits, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at h2
    exact h2
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  have hci : (![(ζ : K), ((ζ⁻¹ : Kˣ) : K), ((1 : Kˣ) : K)] i) * (c : K) = 1 := by
    have h3 : ((![(ζ : K), ((ζ⁻¹ : Kˣ) : K), ((1 : Kˣ) : K)] i) * (c : K)) * w i = 1 * w i := by
      rw [one_mul, mul_assoc]
      exact (hkey i).symm
    exact mul_right_cancel₀ hi h3
  have hfirst : c = ζ⁻¹ ∨ c = ζ ∨ c = 1 := by
    fin_cases i
    · left
      have : ζ * c = 1 := Units.ext (by simpa using hci)
      exact eq_inv_of_mul_eq_one_right this
    · right; left
      have : ζ⁻¹ * c = 1 := Units.ext (by simpa using hci)
      exact (inv_mul_eq_one.mp this).symm
    · right; right
      exact Units.ext (by simpa using hci)
  refine ⟨hfirst, fun hc1 => ?_⟩
  subst hc1
  have hB1 : B * frobGL τ (diagUnits ζ ζ⁻¹ 1) = diagUnits ζ ζ⁻¹ 1 * B := by
    simpa using hB
  have hconj : (B : Matrix (Fin 3) (Fin 3) K) *
      ((frobGL τ (diagUnits ζ ζ⁻¹ 1) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h5 : B * frobGL τ (diagUnits ζ ζ⁻¹ 1) * B⁻¹ = diagUnits ζ ζ⁻¹ 1 := by
      rw [hB1]
      group
    have h6 := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K)) h5
    simpa only [Units.val_mul] using h6
  have htr := Matrix.trace_units_conj B
    ((frobGL τ (diagUnits ζ ζ⁻¹ 1) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [hconj, coe_frobGL, coe_diagUnits, Matrix.diagonal_map (map_zero τ),
    Matrix.trace_diagonal, Matrix.trace_diagonal] at htr
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have hξ0 : τ (ζ : K) ≠ 0 := (map_ne_zero τ).mpr hζ0
  have hkey2 : (ζ : K) + (ζ : K)⁻¹ = τ (ζ : K) + (τ (ζ : K))⁻¹ := by
    simp [Fin.sum_univ_three, map_inv₀] at htr
    linear_combination htr
  have ha : (ζ : K) * (ζ : K)⁻¹ = 1 := mul_inv_cancel₀ hζ0
  have hx : τ (ζ : K) * (τ (ζ : K))⁻¹ = 1 := mul_inv_cancel₀ hξ0
  have hq : (τ (ζ : K) - ζ) * (τ (ζ : K) - (ζ : K)⁻¹) = 0 := by
    linear_combination (-(τ (ζ : K))) * hkey2 + ha - hx
  rcases mul_eq_zero.mp hq with h7 | h7
  · exact Or.inl (sub_eq_zero.mp h7)
  · exact Or.inr (by rw [Units.val_inv_eq_inv_val]; exact sub_eq_zero.mp h7)

end Torus

theorem isPGroup_zpowers_of_pow_eq_one {S : Type} [Group S] {x : S} {j : ℕ}
    (hx : x ^ (3 ^ j) = 1) : IsPGroup 3 (Subgroup.zpowers x) :=
  IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx)

end Z3Field

end CFSG.RankThree.PartTwo.Sec4.RonanK432
