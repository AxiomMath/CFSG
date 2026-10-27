module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

namespace F6

namespace GoldAmLab2

theorem card_ge_pow_of_indep {G : Type*} [CommGroup G] [Finite G]
    (hsq : ∀ x : G, x * x = 1) {n : ℕ} (v : Fin n → G)
    (hind : ∀ g : Fin n → Bool, (∏ i, cond (g i) (v i) 1) = 1 → ∀ i, g i = false) :
    2 ^ n ≤ Nat.card G := by
  classical
  let φ : (Fin n → Bool) → G := fun g => ∏ i, cond (g i) (v i) 1
  have hxor : ∀ g g' : Fin n → Bool, φ (fun i => xor (g i) (g' i)) = φ g * φ g' := by
    intro g g'
    simp only [φ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases g i <;> cases g' i <;> simp [hsq (v i)]
  have hinj : Function.Injective φ := by
    intro g g' hgg
    have h1 : φ (fun i => xor (g i) (g' i)) = 1 := by
      rw [hxor, ← hgg]
      exact hsq _
    have h2 := hind _ h1
    funext i
    have h3 := h2 i
    revert h3; cases g i <;> cases g' i <;> simp
  have := Nat.card_le_card_of_injective φ hinj
  simpa [Nat.card_fun] using this

theorem twist_prod {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι] (τ : G →* G)
    (v t : ι → G) (hτ : ∀ i, τ (v i) = v i * t i) (g : ι → Bool)
    (hprod : ∏ i, cond (g i) (v i) 1 = 1) : ∏ i, cond (g i) (t i) 1 = 1 := by
  have h1 : τ (∏ i, cond (g i) (v i) 1) = ∏ i, cond (g i) (v i * t i) 1 := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases g i <;> simp [hτ i]
  have h2 : ∏ i, cond (g i) (v i * t i) 1 =
      (∏ i, cond (g i) (v i) 1) * ∏ i, cond (g i) (t i) 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases g i <;> simp
  rw [h2, hprod, map_one, one_mul] at h1
  exact h1.symm

theorem eq_of_mul_eq_one' {G : Type*} [CommGroup G] (hsq : ∀ x : G, x * x = 1) {a b : G}
    (h : a * b = 1) : a = b := by
  have h1 : b = a⁻¹ := (eq_inv_of_mul_eq_one_right h)
  have h2 : a⁻¹ = a := by
    have := hsq a
    exact (inv_eq_of_mul_eq_one_right this)
  rw [h1, h2]

theorem aux_ne {G : Type*} [CommGroup G] (hsq : ∀ x : G, x * x = 1) {c u w : G}
    (hc : c ≠ 1) (hcu : c ≠ u) (hw : w = 1 ∨ w = u) (b : Bool) (h : c * cond b w 1 = 1) :
    False := by
  rcases hw with rfl | rfl <;> cases b <;> simp at h
  · exact hc h
  · exact hc h
  · exact hc h
  · exact hcu (eq_of_mul_eq_one' hsq h)

theorem card_ge_32 {G : Type*} [CommGroup G] [Finite G] (hsq : ∀ x : G, x * x = 1)
    (c₀ c₁ c₂ d₀ d₁ d₂ : G) (h0 : c₀ ≠ 1) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1)
    (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (h01 : c₀ ≠ c₁)
    (τ₁ τ₂ τ₃ : G →* G)
    (a₁ : τ₁ c₀ = c₀) (b₁ : τ₁ c₁ = c₁) (e₁ : τ₁ d₀ = d₀ * c₀) (f₁ : τ₁ d₁ = d₁)
    (g₁ : τ₁ d₂ = d₂ ∨ τ₁ d₂ = d₂ * c₂)
    (a₂ : τ₂ c₀ = c₀) (b₂ : τ₂ c₁ = c₁) (e₂ : τ₂ d₀ = d₀) (f₂ : τ₂ d₁ = d₁ * c₁)
    (g₂ : τ₂ d₂ = d₂ ∨ τ₂ d₂ = d₂ * c₂)
    (a₃ : τ₃ c₀ = c₀) (b₃ : τ₃ c₁ = c₁) (e₃ : τ₃ d₀ = d₀)
    (g₃ : τ₃ d₂ = d₂ * c₂) : 2 ^ 5 ≤ Nat.card G := by
  refine card_ge_pow_of_indep hsq (n := 5) ![c₀, c₁, d₀, d₁, d₂] ?_
  intro g hg
  have hg' : cond (g 0) c₀ 1 * cond (g 1) c₁ 1 * cond (g 2) d₀ 1 * cond (g 3) d₁ 1 *
      cond (g 4) d₂ 1 = 1 := by
    rw [Fin.prod_univ_five] at hg
    simpa using hg
  have r1 := twist_prod τ₁ ![c₀, c₁, d₀, d₁, d₂] ![1, 1, c₀, 1, d₂⁻¹ * τ₁ d₂]
    (by intro i; fin_cases i <;> simp [a₁, b₁, e₁, f₁]) g hg
  have r2 := twist_prod τ₂ ![c₀, c₁, d₀, d₁, d₂] ![1, 1, 1, c₁, d₂⁻¹ * τ₂ d₂]
    (by intro i; fin_cases i <;> simp [a₂, b₂, e₂, f₂]) g hg
  have r3 := twist_prod τ₃ ![c₀, c₁, d₀, d₁, d₂] ![1, 1, 1, d₁⁻¹ * τ₃ d₁, c₂]
    (by intro i; fin_cases i <;> simp [a₃, b₃, e₃, g₃]) g hg
  rw [Fin.prod_univ_five] at r1 r2 r3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Bool.cond_self,
    one_mul, mul_one] at r1 r2 r3
  have w1 : d₂⁻¹ * τ₁ d₂ = 1 ∨ d₂⁻¹ * τ₁ d₂ = c₂ := by
    rcases g₁ with h | h <;> simp [h]
  have w2 : d₂⁻¹ * τ₂ d₂ = 1 ∨ d₂⁻¹ * τ₂ d₂ = c₂ := by
    rcases g₂ with h | h <;> simp [h]
  have hg2 : g 2 = false := by
    cases h : g 2
    · rfl
    · rw [h] at r1; exact (aux_ne hsq h0 h02 w1 (g 4) (by simpa using r1)).elim
  have hg3 : g 3 = false := by
    cases h : g 3
    · rfl
    · rw [h] at r2; exact (aux_ne hsq h1 h12 w2 (g 4) (by simpa using r2)).elim
  have hg4 : g 4 = false := by
    cases h : g 4
    · rfl
    · rw [h, hg3] at r3; simp at r3; exact (h2 r3).elim
  rw [hg2, hg3, hg4] at hg'
  simp only [Bool.cond_false, mul_one] at hg'
  have hg0 : g 0 = false := by
    cases h : g 0
    · rfl
    · rw [h] at hg'
      exact (aux_ne hsq h0 h01 (Or.inr rfl) (g 1) (by simpa using hg')).elim
  have hg1 : g 1 = false := by
    cases h : g 1
    · rfl
    · rw [h, hg0] at hg'; simp at hg'; exact (h1 hg').elim
  intro i
  fin_cases i <;> simp [hg0, hg1, hg2, hg3, hg4]

theorem indep_three {G : Type*} [CommGroup G] (hsq : ∀ x : G, x * x = 1) {c₀ c₁ c₂ : G}
    (h0 : c₀ ≠ 1) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1) (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂)
    (h12 : c₁ ≠ c₂) (hε : c₀ * c₁ * c₂ ≠ 1) (b₀ b₁ b₂ : Bool)
    (h : cond b₀ c₀ 1 * cond b₁ c₁ 1 * cond b₂ c₂ 1 = 1) :
    b₀ = false ∧ b₁ = false ∧ b₂ = false := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> simp at h ⊢
  · exact h2 h
  · exact h1 h
  · exact h12 (eq_of_mul_eq_one' hsq h)
  · exact h0 h
  · exact h02 (eq_of_mul_eq_one' hsq h)
  · exact h01 (eq_of_mul_eq_one' hsq h)
  · exact hε h

theorem card_ge_64 {G : Type*} [CommGroup G] [Finite G] (hsq : ∀ x : G, x * x = 1)
    (c₀ c₁ c₂ d₀ d₁ d₂ : G) (h0 : c₀ ≠ 1) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1)
    (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (hε : c₀ * c₁ * c₂ ≠ 1)
    (τ : G →* G) (a₀ : τ c₀ = c₀) (a₁ : τ c₁ = c₁) (a₂ : τ c₂ = c₂)
    (e₀ : τ d₀ = d₀ * c₀) (e₁ : τ d₁ = d₁ * c₁) (e₂ : τ d₂ = d₂ * c₂) :
    2 ^ 6 ≤ Nat.card G := by
  refine card_ge_pow_of_indep hsq (n := 6) ![c₀, c₁, c₂, d₀, d₁, d₂] ?_
  intro g hg
  have hg' : cond (g 0) c₀ 1 * cond (g 1) c₁ 1 * cond (g 2) c₂ 1 * cond (g 3) d₀ 1 *
      cond (g 4) d₁ 1 * cond (g 5) d₂ 1 = 1 := by
    rw [Fin.prod_univ_six] at hg
    simpa using hg
  have r := twist_prod τ ![c₀, c₁, c₂, d₀, d₁, d₂] ![1, 1, 1, c₀, c₁, c₂]
    (by intro i; fin_cases i <;> simp [a₀, a₁, a₂, e₀, e₁, e₂]) g hg
  rw [Fin.prod_univ_six] at r
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Bool.cond_self,
    one_mul] at r
  obtain ⟨hg3, hg4, hg5⟩ := indep_three hsq h0 h1 h2 h01 h02 h12 hε (g 3) (g 4) (g 5) (by
    simpa using r)
  rw [hg3, hg4, hg5] at hg'
  simp only [Bool.cond_false, mul_one] at hg'
  obtain ⟨hg0, hg1, hg2⟩ := indep_three hsq h0 h1 h2 h01 h02 h12 hε (g 0) (g 1) (g 2) hg'
  intro i
  fin_cases i <;> simp [hg0, hg1, hg2, hg3, hg4, hg5]

theorem card_ge_32_grp {G : Type*} [Group G] [Finite G] (hcomm : ∀ x y : G, x * y = y * x)
    (hsq : ∀ x : G, x * x = 1)
    (c₀ c₁ c₂ d₀ d₁ d₂ : G) (h0 : c₀ ≠ 1) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1)
    (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (h01 : c₀ ≠ c₁)
    (τ₁ τ₂ τ₃ : G →* G)
    (a₁ : τ₁ c₀ = c₀) (b₁ : τ₁ c₁ = c₁) (e₁ : τ₁ d₀ = d₀ * c₀) (f₁ : τ₁ d₁ = d₁)
    (g₁ : τ₁ d₂ = d₂ ∨ τ₁ d₂ = d₂ * c₂)
    (a₂ : τ₂ c₀ = c₀) (b₂ : τ₂ c₁ = c₁) (e₂ : τ₂ d₀ = d₀) (f₂ : τ₂ d₁ = d₁ * c₁)
    (g₂ : τ₂ d₂ = d₂ ∨ τ₂ d₂ = d₂ * c₂)
    (a₃ : τ₃ c₀ = c₀) (b₃ : τ₃ c₁ = c₁) (e₃ : τ₃ d₀ = d₀)
    (g₃ : τ₃ d₂ = d₂ * c₂) : 2 ^ 5 ≤ Nat.card G := by
  let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  exact card_ge_32 hsq c₀ c₁ c₂ d₀ d₁ d₂ h0 h1 h2 h02 h12 h01 τ₁ τ₂ τ₃ a₁ b₁ e₁ f₁ g₁ a₂ b₂ e₂ f₂
    g₂ a₃ b₃ e₃ g₃

theorem card_ge_64_grp {G : Type*} [Group G] [Finite G] (hcomm : ∀ x y : G, x * y = y * x)
    (hsq : ∀ x : G, x * x = 1)
    (c₀ c₁ c₂ d₀ d₁ d₂ : G) (h0 : c₀ ≠ 1) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1)
    (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (hε : c₀ * c₁ * c₂ ≠ 1)
    (τ : G →* G) (a₀ : τ c₀ = c₀) (a₁ : τ c₁ = c₁) (a₂ : τ c₂ = c₂)
    (e₀ : τ d₀ = d₀ * c₀) (e₁ : τ d₁ = d₁ * c₁) (e₂ : τ d₂ = d₂ * c₂) :
    2 ^ 6 ≤ Nat.card G := by
  let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  exact card_ge_64 hsq c₀ c₁ c₂ d₀ d₁ d₂ h0 h1 h2 h01 h02 h12 hε τ a₀ a₁ a₂ e₀ e₁ e₂

end GoldAmLab2

end F6

end CFSG.Quasithin
