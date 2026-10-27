module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.KEXC

open Matrix

variable {K : Type*} [Field K]

instance slTwoAct : MulAction (SpecialLinearGroup (Fin 2) K) (Fin 2 → K) where
  smul g v := (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  one_smul v := by
    show ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v
    simp
  mul_smul g h v := by
    show ((g * h : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
    simp [Matrix.mulVec_mulVec]

theorem slTwoAct_def (g : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    g • v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

theorem exists_fixed_vector [Finite K] [CharP K 2] {R : Subgroup (SpecialLinearGroup (Fin 2) K)}
    (hR2 : IsPGroup 2 R) : ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ r ∈ R, r • v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  let _ : MulAction R (Fin 2 → K) := MulAction.compHom _ R.subtype
  have hmod := hR2.card_modEq_card_fixedPoints (Fin 2 → K)
  obtain ⟨n, hn, hc⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hc
  have h2 : 2 ∣ Nat.card (Fin 2 → K) := by
    rw [Nat.card_fun, hcard]
    have : Nat.card (Fin 2) = 2 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 2)
    rw [this, ← pow_mul]
    exact dvd_pow_self 2 (by have := n.pos; omega)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints R (Fin 2 → K)) := by
    have := (Nat.modEq_zero_iff_dvd.2 h2)
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans this)
  have hne : Nonempty (MulAction.fixedPoints R (Fin 2 → K)) :=
    ⟨⟨0, fun r => by
      show ((r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (0 : Fin 2 → K) = 0
      simp⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints R (Fin 2 → K)) := Nat.card_pos
  have h2le : 2 ≤ Nat.card (MulAction.fixedPoints R (Fin 2 → K)) :=
    Nat.le_of_dvd hpos hfix2
  have h1lt : 1 < Nat.card (MulAction.fixedPoints R (Fin 2 → K)) := h2le
  have hnt : Nontrivial (MulAction.fixedPoints R (Fin 2 → K)) :=
    Finite.one_lt_card_iff_nontrivial.1 h1lt
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hnt.exists_pair_ne
  have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
  have hfx : ∀ r ∈ R, r • x = x := fun r hr => by
    have := (MulAction.mem_fixedPoints).1 hx ⟨r, hr⟩
    exact this
  have hfy : ∀ r ∈ R, r • y = y := fun r hr => by
    have := (MulAction.mem_fixedPoints).1 hy ⟨r, hr⟩
    exact this
  by_cases hx0 : x = 0
  · exact ⟨y, fun h => hxy' (hx0.trans h.symm), hfy⟩
  · exact ⟨x, hx0, hfx⟩

theorem slTwo_pow_smul {g : SpecialLinearGroup (Fin 2) K} {v : Fin 2 → K} {c : K}
    (h : g • v = c • v) (n : ℕ) : g ^ n • v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, h]
    show ((g ^ n : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (c • v) = _
    rw [Matrix.mulVec_smul]
    have : ((g ^ n : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = c ^ n • v :=
      ih
    rw [this, smul_smul, pow_succ, mul_comm]

theorem slTwo_sq_eq_one [CharP K 2] {g : SpecialLinearGroup (Fin 2) K} {v : Fin 2 → K}
    (hv : v ≠ 0) (hgv : g • v = v) : g * g = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  have hker : ((g : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := hgv
    rw [this, sub_self]
  have hdet0 : ((g : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hker⟩
  rw [Matrix.det_fin_two] at hdet hdet0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hdet0
  have htr : (g : Matrix (Fin 2) (Fin 2) K) 0 0 + (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
    linear_combination hdet - hdet0 + h2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] <;>
    first
      | linear_combination (-1) * hdet + (g : Matrix (Fin 2) (Fin 2) K) 0 0 * htr - h2
      | linear_combination (-1) * hdet + (g : Matrix (Fin 2) (Fin 2) K) 1 1 * htr - h2
      | linear_combination (g : Matrix (Fin 2) (Fin 2) K) 0 1 * htr
      | linear_combination (g : Matrix (Fin 2) (Fin 2) K) 1 0 * htr

theorem sl2_bt [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K - 1) {R : Subgroup (SpecialLinearGroup (Fin 2) K)}
    (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) {g : SpecialLinearGroup (Fin 2) K} (hg : g ^ p = 1)
    (hgN : g ∈ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 2) K))) : g = 1 := by
  classical
  obtain ⟨v, hv0, hvR⟩ := exists_fixed_vector hR2
  obtain ⟨r₀, hr₀, hr₀1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hR (Subgroup.eq_bot_iff_forall R |>.2 hno)
  have hgv : ∀ r ∈ R, r • (g • v) = g • v := by
    intro r hr
    have h1 : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff''.1 hgN r).1 hr
      exact this
    calc r • (g • v) = g • ((g⁻¹ * r * g) • v) := by
          rw [smul_smul, smul_smul]; simp [mul_assoc]
      _ = g • v := by rw [hvR _ h1]
  obtain ⟨c, hc⟩ : ∃ c : K, g • v = c • v := by
    set w := g • v with hw
    by_cases hdet : v 0 * w 1 - w 0 * v 1 = 0
    · by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := fun h1 => hv0 (by ext i; fin_cases i <;> simp [h0, h1])
        have hw0 : w 0 = 0 := by
          have h' := hdet
          rw [h0, zero_mul, zero_sub, neg_eq_zero] at h'
          exact (mul_eq_zero.1 h').resolve_right h1
        refine ⟨w 1 / v 1, ?_⟩
        ext i
        fin_cases i
        · simp [hw0, h0]
        · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
          exact (div_mul_cancel₀ _ h1).symm
      · refine ⟨w 0 / v 0, ?_⟩
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
          exact (div_mul_cancel₀ _ h0).symm
        · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
          field_simp
          linear_combination hdet
    · exfalso
      set M : Matrix (Fin 2) (Fin 2) K := !![v 0, w 0; v 1, w 1] with hM
      have hMdet : M.det ≠ 0 := by
        rw [hM, Matrix.det_fin_two_of]
        exact hdet
      have hrM : (r₀ : Matrix (Fin 2) (Fin 2) K) * M = M := by
        have hv_0 := congrFun (hvR r₀ hr₀) 0
        have hv_1 := congrFun (hvR r₀ hr₀) 1
        have hw_0 := congrFun (hgv r₀ hr₀) 0
        have hw_1 := congrFun (hgv r₀ hr₀) 1
        simp only [slTwoAct_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv_0 hv_1 hw_0 hw_1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first
            | linear_combination hv_0
            | linear_combination hv_1
            | linear_combination hw_0
            | linear_combination hw_1
      have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hMdet)
      have : (r₀ : Matrix (Fin 2) (Fin 2) K) = 1 :=
        hunit.mul_right_cancel (by rw [one_mul]; exact hrM)
      exact hr₀1 (Subtype.ext this)
  have hcp : c ^ p = 1 := by
    have h1 := slTwo_pow_smul hc p
    rw [hg, one_smul] at h1
    have h2 : (c ^ p - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0
  have : Fact p.Prime := ⟨hp⟩
  have hc0 : c ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  have hc1 : c = 1 := by
    by_contra hne
    let u : Kˣ := Units.mk0 c hc0
    have hu : u ^ p = 1 := by ext; simpa [u] using hcp
    have hu1 : u ≠ 1 := fun h => hne (by simpa [u] using congrArg Units.val h)
    have hord : orderOf u = p := orderOf_eq_prime hu hu1
    have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
    have hcardu : Nat.card Kˣ = Nat.card K - 1 := by
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
    rw [hord, hcardu] at hdvd
    exact hpq hdvd
  have hgv1 : g • v = v := by rw [hc, hc1, one_smul]
  have hsq := slTwo_sq_eq_one hv0 hgv1
  have h2' : g ^ 2 = 1 := by rw [sq]; exact hsq
  have hord : orderOf g ∣ Nat.gcd 2 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2') (orderOf_dvd_of_pow_eq_one hg)
  have hcop : Nat.gcd 2 p = 1 :=
    (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  rw [hcop] at hord
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)

end CFSG.RankThree.PartOne.KEXC
