module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Walter.Ree.Thompson1

open Finset

variable {K : Type*} [Field K] [Fintype K] {G : Type*} [Group G] [Finite G]

theorem exists_eigen_coord [IsCyclic G] (hG : Nat.card G = Fintype.card K - 1) (A : G → K → K)
    (hadd : ∀ g x y, A g (x + y) = A g x + A g y) (hmul : ∀ g h x, A (g * h) x = A g (A h x))
    (hone : ∀ x, A 1 x = x)
    (hirr : ∀ H : AddSubgroup K, (∀ g, ∀ x ∈ H, A g x ∈ H) → H = ⊥ ∨ H = ⊤) :
    ∃ φ : K → K, (∀ x y, φ (x + y) = φ x + φ y) ∧ Function.Bijective φ ∧
      ∃ ρ : G →* Kˣ, ∀ g x, φ (A g x) = ρ g * φ x := by
  classical
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := G)
  set n := Fintype.card K - 1 with hn
  have hpow : ∀ g : G, ∃ k : ℕ, g = g₀ ^ k := fun g => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 (hg₀ g)
    exact ⟨k, hk.symm⟩
  have hg₀n : g₀ ^ n = 1 := by rw [← hG]; exact pow_card_eq_one'
  have hn0 : 0 < n := by rw [← hG]; exact Nat.card_pos
  have hA0 : ∀ g, A g 0 = 0 := fun g => by
    have := hadd g 0 0; rw [add_zero] at this; linear_combination -this
  have hApow : ∀ (k : ℕ) x, A (g₀ ^ (k + 1)) x = A g₀ (A (g₀ ^ k) x) := fun k x => by
    rw [pow_succ', hmul]
  let φ : K → K → K := fun ρ x => ∑ i ∈ range n, ρ⁻¹ ^ i * A (g₀ ^ i) x
  have hφadd : ∀ ρ x y, φ ρ (x + y) = φ ρ x + φ ρ y := fun ρ x y => by
    simp only [φ, hadd, mul_add, Finset.sum_add_distrib]
  have hφT : ∀ ρ : K, ρ ≠ 0 → ∀ x, φ ρ (A g₀ x) = ρ * φ ρ x := by
    intro ρ hρ x
    have hρn : ρ ^ n = 1 := FiniteField.pow_card_sub_one_eq_one ρ hρ
    simp only [φ]
    have e : ∀ i, ρ⁻¹ ^ i * A (g₀ ^ i) (A g₀ x) = ρ * (ρ⁻¹ ^ (i + 1) * A (g₀ ^ (i + 1)) x) := by
      intro i
      rw [← hmul, ← pow_succ, pow_succ ρ⁻¹, ← mul_assoc, mul_comm ρ, mul_assoc (ρ⁻¹ ^ i),
        inv_mul_cancel₀ hρ, mul_one]
    simp only [e, ← Finset.mul_sum]
    congr 1
    set F : ℕ → K := fun i => ρ⁻¹ ^ i * A (g₀ ^ i) x with hF
    have h1 := Finset.sum_range_succ' F n
    have h2 := Finset.sum_range_succ F n
    have h3 : F n = F 0 := by
      simp only [hF, inv_pow, hρn, hg₀n, inv_one, pow_zero]
    linear_combination h2 - h1 + h3
  have hsum : ∀ x, ∑ ρ : Kˣ, φ ρ x = -x := by
    intro x
    simp only [φ]
    rw [Finset.sum_comm]
    have hi : ∀ i ∈ range n, ∑ ρ : Kˣ, (ρ : K)⁻¹ ^ i * A (g₀ ^ i) x =
        if i = 0 then -x else 0 := by
      intro i hi
      rw [← Finset.sum_mul]
      have : ∑ ρ : Kˣ, (ρ : K)⁻¹ ^ i = ∑ ρ : Kˣ, (ρ : K) ^ i := by
        refine Fintype.sum_equiv (Equiv.inv Kˣ) _ _ fun ρ => ?_
        simp
      rw [this, FiniteField.sum_pow_units]
      rw [Finset.mem_range] at hi
      by_cases h0 : i = 0
      · subst h0
        simp [hone]
      · have : ¬ Fintype.card K - 1 ∣ i := fun h => by
          have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h
          omega
        simp [this, h0]
    rw [Finset.sum_congr rfl hi, Finset.sum_ite_eq']
    simp [hn0]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Kˣ, φ ρ 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hsum 1
    rw [Finset.sum_eq_zero fun ρ _ => hcon ρ] at this
    exact one_ne_zero (neg_eq_zero.1 this.symm)
  have hρ0 : (ρ : K) ≠ 0 := ρ.ne_zero
  have heig : ∀ (k : ℕ) x, φ ρ (A (g₀ ^ k) x) = (ρ : K) ^ k * φ ρ x := by
    intro k
    induction k with
    | zero => intro x; simp [hone]
    | succ k ih => intro x; rw [hApow, hφT ρ hρ0, ih, pow_succ]; ring
  let H : AddSubgroup K :=
    { carrier := {x | φ ρ x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at *
        rw [hφadd, hx, hy, add_zero]
      zero_mem' := by
        show φ ρ 0 = 0
        have := hφadd ρ 0 0
        rw [add_zero] at this
        linear_combination -this
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at *
        have := hφadd ρ x (-x)
        rw [add_neg_cancel, hx, zero_add] at this
        have h0 : φ ρ 0 = 0 := by
          have := hφadd ρ 0 0
          rw [add_zero] at this
          linear_combination -this
        rw [h0] at this
        exact this.symm }
  have hH : H = ⊥ := by
    rcases hirr H fun g x hx => by
      obtain ⟨k, rfl⟩ := hpow g
      show φ ρ (A (g₀ ^ k) x) = 0
      rw [heig]
      simp only [H, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_ofPred_eq] at hx
      rw [hx, mul_zero] with h | h
    · exact h
    · exact absurd (h ▸ AddSubgroup.mem_top (1 : K) : (1 : K) ∈ H) hρ
  have hinj : Function.Injective (φ ρ) := by
    intro x y hxy
    have hx : x - y ∈ H := by
      show φ ρ (x - y) = 0
      have := hφadd ρ (x - y) y
      rw [sub_add_cancel, hxy] at this
      linear_combination -this
    rw [hH, AddSubgroup.mem_bot] at hx
    exact sub_eq_zero.1 hx
  refine ⟨φ ρ, hφadd ρ, Finite.injective_iff_bijective.1 hinj, ?_⟩
  have hφ1 : φ ρ 1 ≠ 0 := hρ
  have hchar : ∀ g : G, ∃ c : K, c ≠ 0 ∧ ∀ x, φ ρ (A g x) = c * φ ρ x := fun g => by
    obtain ⟨k, rfl⟩ := hpow g
    exact ⟨(ρ : K) ^ k, pow_ne_zero _ hρ0, heig k⟩
  choose c hc0 hc using hchar
  refine ⟨{ toFun := fun g => Units.mk0 (c g) (hc0 g), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext
    have := hc 1 1
    rw [hone] at this
    simpa using (mul_eq_right₀ hφ1).1 this.symm
  · intro g h
    ext
    have h1 := hc (g * h) 1
    rw [hmul, hc g, hc h, ← mul_assoc] at h1
    simpa using (mul_right_cancel₀ hφ1 h1).symm
  · intro g x
    simp [hc]

end CFSG.Walter.Ree.Thompson1
