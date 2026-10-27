module

public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim78

open Matrix

theorem eq_zero_of_invariant_quadratic {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {A : Type*} [AddCommGroup A] (hA : ∀ a : A, a + a = 0)
    (ω : (Fin 2 → F) → (Fin 2 → F) → A)
    (hω₁ : ∀ u u' v, ω (u + u') v = ω u v + ω u' v)
    (hω₂ : ∀ u v v', ω u (v + v') = ω u v + ω u v')
    (hωa : ∀ u, ω u u = 0)
    (_hωinv : ∀ (g : SpecialLinearGroup (Fin 2) F) u v,
      ω ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = ω u v)
    (κ : (Fin 2 → F) → A) (hκ : ∀ u v, κ (u + v) = κ u + κ v + ω u v)
    (hκinv : ∀ (g : SpecialLinearGroup (Fin 2) F) u,
      κ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) = κ u) :
    ∀ u v, ω u v = 0 := by
  classical
  have hconst : ∀ u : Fin 2 → F, u ≠ 0 → κ u = κ ![1, 0] := by
    intro u hu
    obtain ⟨g, hg⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq hu
    rw [← hg, hκinv]
  set κ₀ := κ ![1, 0] with hκ₀
  have hωκ : ∀ a b : Fin 2 → F, a ≠ 0 → b ≠ 0 → a ≠ b → ω a b = κ₀ := by
    intro a b ha hb hab
    have hsum : a + b ≠ 0 := by
      intro h
      apply hab
      have : a = -b := eq_neg_of_add_eq_zero_left h
      rw [this]
      ext i
      simp only [Pi.neg_apply]
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have : -b i = b i := by
        have : b i + b i = 0 := by rw [← two_mul, h2, zero_mul]
        exact neg_eq_of_add_eq_zero_right this
      exact this
    have h1 := hκ a b
    rw [hconst _ hsum, hconst a ha, hconst b hb] at h1
    have h3 : κ₀ = κ₀ + κ₀ + ω a b := h1
    rw [hA κ₀, zero_add] at h3
    exact h3.symm
  have hκ0 : κ₀ = 0 := by
    obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsurj : Function.Surjective fun b : Bool => if b then (1 : F) else 0 := fun l => by
        by_cases hl : l = 0
        · exact ⟨false, by simp [hl]⟩
        · exact ⟨true, by simp [hcon l hl]⟩
      have := Fintype.card_le_of_surjective _ hsurj
      rw [Fintype.card_bool] at this
      omega
    have ha : (![1, 0] : Fin 2 → F) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
    have hb : (![0, 1] : Fin 2 → F) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
    have hc : (![0, l] : Fin 2 → F) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
      exact hl0 this
    have hbc : (![0, 1] : Fin 2 → F) + ![0, l] ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have : l = 1 := by
        have h' : (1 : F) + l = 0 := this
        have : l = -1 := eq_neg_of_add_eq_zero_right h'
        rw [this]
        have : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
        exact neg_eq_of_add_eq_zero_right this
      exact hl1 this
    have h1 : ω ![1, 0] ((![0, 1] : Fin 2 → F) + ![0, l]) = κ₀ := by
      refine hωκ _ _ ha hbc ?_
      intro h
      have := congrFun h 0
      simp at this
    have h2 : ω ![1, 0] ![0, 1] = κ₀ := hωκ _ _ ha hb (by
      intro h
      have := congrFun h 0
      simp at this)
    have h3 : ω ![1, 0] ![0, l] = κ₀ := hωκ _ _ ha hc (by
      intro h
      have := congrFun h 0
      simp at this)
    rw [hω₂, h2, h3, hA κ₀] at h1
    exact h1.symm
  intro u v
  by_cases hu : u = 0
  · rw [hu]
    have := hω₁ 0 0 v
    simp only [add_zero] at this
    exact (add_eq_left.mp this.symm)
  by_cases hv : v = 0
  · rw [hv]
    have := hω₂ u 0 0
    simp only [add_zero] at this
    exact (add_eq_left.mp this.symm)
  by_cases huv : u = v
  · rw [huv]; exact hωa v
  rw [hωκ u v hu hv huv, hκ0]

theorem no_invariant_form
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {A : Type*} [AddCommGroup A] (hA : ∀ a : A, a + a = 0)
    {X : Type*} [Group X] (φ : X →* SpecialLinearGroup (Fin 2) F)
    (hφ : Function.Surjective φ)
    {M : Type*} [AddCommGroup M] [DistribMulAction X M]
    (θ : (Fin 2 → F) →+ M) (hθinj : Function.Injective θ)
    (hθ : ∀ (x : X) (v : Fin 2 → F),
      θ ((φ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x • θ v)
    (hsplit : ∀ m : M, ∃ (v : Fin 2 → F) (m₁ : M), (∀ x : X, x • m₁ = m₁) ∧ m = θ v + m₁)
    (D : M →+ M →+ A) (hDalt : ∀ m, D m m = 0)
    (hDinv : ∀ (x : X) (m m' : M), D (x • m) (x • m') = D m m')
    (hDnd : ∀ m' : M, m' ≠ 0 → ∃ m : M, D m m' ≠ 0)
    (κ : M → A) (hκ : ∀ m m' : M, κ (m + m') = κ m + κ m' + D m m')
    (hκinv : ∀ (x : X) (m : M), κ (x • m) = κ m) : False := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hF' : 4 ≤ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hzero : ∀ u v, D (θ u) (θ v) = 0 := by
    refine eq_zero_of_invariant_quadratic hF' hA (fun u v => D (θ u) (θ v)) ?_ ?_ ?_ ?_
      (fun u => κ (θ u)) ?_ ?_
    · intro u u' v
      simp only [map_add, AddMonoidHom.add_apply]
    · intro u v v'
      simp only [map_add]
    · intro u
      exact hDalt _
    · intro g u v
      obtain ⟨x, rfl⟩ := hφ g
      simp only [hθ, hDinv]
    · intro u v
      simp only [map_add]
      exact hκ _ _
    · intro g u
      obtain ⟨x, rfl⟩ := hφ g
      simp only [hθ, hκinv]
  have hdiff_fst : ∀ (m₁ : M), (∀ x : X, x • m₁ = m₁) → ∀ a : F,
      D (θ ![a, 0]) m₁ = 0 ∧ D m₁ (θ ![a, 0]) = 0 := by
    intro m₁ hm₁ a
    obtain ⟨x, hx⟩ := hφ (CFSG.Timmesfeld.RankOne.upperElt F a)
    have hv : (CFSG.Timmesfeld.RankOne.upperElt F a : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 1] =
        ![a, 1] := by
      rw [CFSG.Timmesfeld.ARS.NaturalModule.coe_upperElt]
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h1 : x • θ ![0, 1] = θ ![a, 1] := by rw [← hθ, hx, hv]
    have h2 : θ ![a, 1] = θ ![a, 0] + θ ![0, 1] := by
      rw [← map_add]; congr 1; ext i; fin_cases i <;> simp
    constructor
    · have := hDinv x (θ ![0, 1]) m₁
      rw [hm₁ x, h1, h2, map_add, AddMonoidHom.add_apply] at this
      simpa using this
    · have := hDinv x m₁ (θ ![0, 1])
      rw [hm₁ x, h1, h2, map_add] at this
      simpa using this
  have hdiff_snd : ∀ (m₁ : M), (∀ x : X, x • m₁ = m₁) → ∀ a : F,
      D (θ ![0, a]) m₁ = 0 ∧ D m₁ (θ ![0, a]) = 0 := by
    intro m₁ hm₁ a
    obtain ⟨x, hx⟩ := hφ (CFSG.Timmesfeld.RankOne.lowerElt F a)
    have hv : (CFSG.Timmesfeld.RankOne.lowerElt F a : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] =
        ![1, a] := by
      rw [CFSG.Timmesfeld.ARS.NaturalModule.coe_lowerElt]
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h1 : x • θ ![1, 0] = θ ![1, a] := by rw [← hθ, hx, hv]
    have h2 : θ ![1, a] = θ ![0, a] + θ ![1, 0] := by
      rw [← map_add]; congr 1; ext i; fin_cases i <;> simp [add_comm]
    constructor
    · have := hDinv x (θ ![1, 0]) m₁
      rw [hm₁ x, h1, h2, map_add, AddMonoidHom.add_apply] at this
      simpa using this
    · have := hDinv x m₁ (θ ![1, 0])
      rw [hm₁ x, h1, h2, map_add] at this
      simpa using this
  have hperp : ∀ (m₁ : M), (∀ x : X, x • m₁ = m₁) → ∀ v : Fin 2 → F,
      D (θ v) m₁ = 0 ∧ D m₁ (θ v) = 0 := by
    intro m₁ hm₁ v
    have hv : v = ![v 0, 0] + ![0, v 1] := by
      ext i; fin_cases i <;> simp
    rw [hv, map_add, map_add, AddMonoidHom.add_apply, map_add]
    obtain ⟨a1, a2⟩ := hdiff_fst m₁ hm₁ (v 0)
    obtain ⟨b1, b2⟩ := hdiff_snd m₁ hm₁ (v 1)
    rw [a1, b1, a2, b2]
    simp
  have he1 : θ ![1, 0] ≠ 0 := by
    intro h
    have := hθinj (h.trans (map_zero θ).symm)
    have h0 := congrFun this 0
    simp at h0
  obtain ⟨m, hm⟩ := hDnd _ he1
  obtain ⟨v, m₁, hm₁, rfl⟩ := hsplit m
  apply hm
  rw [map_add, AddMonoidHom.add_apply, hzero, (hperp m₁ hm₁ ![1, 0]).2, add_zero]

theorem no_invariant_form_gf2n (n : ℕ) (hn : 2 ≤ n) {A : Type*} [AddCommGroup A]
    (hA : ∀ a : A, a + a = 0)
    {X : Type*} [Group X] (φ : X →* SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ)
    {M : Type*} [AddCommGroup M] [DistribMulAction X M]
    (θ : (Fin 2 → GaloisField 2 n) →+ M) (hθinj : Function.Injective θ)
    (hθ : ∀ (x : X) (v : Fin 2 → GaloisField 2 n),
      θ ((φ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v) = x • θ v)
    (hsplit : ∀ m : M, ∃ (v : Fin 2 → GaloisField 2 n) (m₁ : M),
      (∀ x : X, x • m₁ = m₁) ∧ m = θ v + m₁)
    (D : M →+ M →+ A) (hDalt : ∀ m, D m m = 0)
    (hDinv : ∀ (x : X) (m m' : M), D (x • m) (x • m') = D m m')
    (hDnd : ∀ m' : M, m' ≠ 0 → ∃ m : M, D m m' ≠ 0)
    (κ : M → A) (hκ : ∀ m m' : M, κ (m + m') = κ m + κ m' + D m m')
    (hκinv : ∀ (x : X) (m : M), κ (x • m) = κ m) : False := by
  have hcard : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact no_invariant_form hcard hA φ hφ θ hθinj hθ hsplit D hDalt hDinv hDnd κ hκ hκinv

end CFSG.RankThree.GF2n.Tim78
