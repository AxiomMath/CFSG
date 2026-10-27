module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.MS93.S37R

variable {F : Type} [Field F]

@[expose] def dot (x a : Fin 2 → F) : F := x 0 * a 0 + x 1 * a 1

theorem dot_add_right (x a b : Fin 2 → F) : dot x (a + b) = dot x a + dot x b := by
  simp only [dot, Pi.add_apply]
  ring

theorem dot_smul_right (x a : Fin 2 → F) (c : F) : dot x (c • a) = c * dot x a := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  ring

theorem dot_zero_right (x : Fin 2 → F) : dot x 0 = 0 := by
  simp [dot]

theorem eq_zero_of_pow_four [Fintype F] (hF : 4 < Fintype.card F) {a b d : F}
    (h : ∀ c : F, a * c ^ 4 + b * c ^ 2 + d * c = 0) : a = 0 ∧ b = 0 ∧ d = 0 := by
  open Polynomial in
  set p : F[X] := C a * X ^ 4 + C b * X ^ 2 + C d * X with hp
  have hdeg : p.natDegree ≤ 4 := by
    rw [hp]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_C_mul_X_pow_le a 4)
    · exact (natDegree_C_mul_X_pow_le b 2).trans (by norm_num)
    · have h1 := natDegree_C_mul_X_pow_le d 1
      rw [pow_one] at h1
      exact h1.trans (by norm_num)
  have h0 : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := id)
      Function.injective_id (fun c => ?_) (lt_of_le_of_lt hdeg hF)
    simp only [hp, id, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    exact h c
  have c4 := congrArg (Polynomial.coeff · 4) h0
  have c2 := congrArg (Polynomial.coeff · 2) h0
  have c1 := congrArg (Polynomial.coeff · 1) h0
  simp only [hp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_zero] at c4 c2 c1
  norm_num at c4 c2 c1
  exact ⟨c4, c2, c1⟩

theorem eq_zero_of_dot {x₁ x₂ v : Fin 2 → F} (hind : x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 ≠ 0)
    (h₁ : dot x₁ v = 0) (h₂ : dot x₂ v = 0) : v = 0 := by
  simp only [dot] at h₁ h₂
  have e0 : (x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0) * v 0 = 0 := by linear_combination x₂ 1 * h₁ - x₁ 1 * h₂
  have e1 : (x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0) * v 1 = 0 := by linear_combination x₁ 0 * h₂ - x₂ 0 * h₁
  funext i
  fin_cases i
  · exact (mul_eq_zero.1 e0).resolve_left hind
  · exact (mul_eq_zero.1 e1).resolve_left hind

theorem exists_dot_eq {x : Fin 2 → F} (hx : x ≠ 0) (s : F) : ∃ a, dot x a = s := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := fun h1 => hx (by funext i; fin_cases i <;> simp [h0, h1])
    refine ⟨![0, s / x 1], ?_⟩
    simp [dot, h0, mul_div_cancel₀ _ h1]
  · refine ⟨![s / x 0, 0], ?_⟩
    simp [dot, mul_div_cancel₀ _ h0]

variable [Finite F] [CharP F 2]

theorem eq_smul_of_comm (hF : 4 < Nat.card F) (T : (Fin 2 → F) × F →+ (Fin 2 → F) × F)
    (hT : ∀ (l : F) (v : (Fin 2 → F) × F),
      T (l • v.1, l ^ 2 * v.2) = (l • (T v).1, l ^ 2 * (T v).2))
    {x₁ x₂ : Fin 2 → F} (hind : x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 ≠ 0)
    (hΓ : ∀ x ∈ ({x₁, x₂} : Set (Fin 2 → F)), ∀ a, (T (a, dot x a)).2 = dot x (T (a, dot x a)).1) :
    ∃ ω : F, ∀ v, T v = (ω • v.1, ω * v.2) := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : 4 < Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hsq : ∀ s : F, ∃ l : F, l ^ 2 = s := fun s => by
    obtain ⟨l, hl⟩ := isSquare_of_charTwo' s
    exact ⟨l, by rw [hl, sq]⟩
  have hsplit : ∀ a s, T (a, s) = T (a, 0) + T (0, s) := fun a s => by
    rw [← map_add]
    simp
  have hτ : ∀ (l : F) a, T (l • a, 0) = (l • (T (a, 0)).1, l ^ 2 * (T (a, 0)).2) := fun l a => by
    have := hT l (a, 0)
    simpa using this
  have ht : ∀ (l s : F), T (0, l ^ 2 * s) = (l • (T (0, s)).1, l ^ 2 * (T (0, s)).2) :=
    fun l s => by
      have := hT l (0, s)
      simpa using this
  set ω := (T (0, 1)).2 with hω
  have hw : ∀ s : F, (T (0, s)).2 = ω * s := fun s => by
    obtain ⟨l, rfl⟩ := hsq s
    have := congrArg Prod.snd (ht l 1)
    rw [mul_one] at this
    rw [this, mul_comm]
  have key : ∀ x ∈ ({x₁, x₂} : Set (Fin 2 → F)), x ≠ 0 → ∀ a,
      (T (a, 0)).2 = 0 ∧ (T (0, dot x a)).2 = dot x (T (a, 0)).1 ∧
        dot x (T (0, dot x a)).1 = 0 := by
    intro x hx _ a
    set A := dot x a
    have hpoly : ∀ d : F, (T (a, 0)).2 * d ^ 4 + ((T (0, A)).2 + dot x (T (a, 0)).1) * d ^ 2 +
        dot x (T (0, A)).1 * d = 0 := by
      intro d
      obtain ⟨c, rfl⟩ := hsq d
      have h := hΓ x hx (c ^ 4 • a)
      rw [dot_smul_right, hsplit, hτ, show c ^ 4 * A = (c ^ 2) ^ 2 * A by ring, ht] at h
      simp only [Prod.fst_add, Prod.snd_add, dot_add_right, dot_smul_right] at h
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h + (c ^ 2 * dot x (T (0, A)).1 + c ^ 4 * dot x (T (a, 0)).1) * h2
    obtain ⟨e1, e2, e3⟩ := eq_zero_of_pow_four hF' hpoly
    refine ⟨e1, ?_, e3⟩
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination e2 - dot x (T (a, 0)).1 * h2
  have hx₁ : x₁ ≠ 0 := fun h => hind (by simp [h])
  have hx₂ : x₂ ≠ 0 := fun h => hind (by simp [h])
  have hm₁ : x₁ ∈ ({x₁, x₂} : Set (Fin 2 → F)) := Set.mem_insert _ _
  have hm₂ : x₂ ∈ ({x₁, x₂} : Set (Fin 2 → F)) := Set.mem_insert_of_mem _ rfl
  have ht0 : ∀ s : F, (T (0, s)).1 = 0 := fun s => by
    obtain ⟨a₁, ha₁⟩ := exists_dot_eq hx₁ s
    obtain ⟨a₂, ha₂⟩ := exists_dot_eq hx₂ s
    have h1 := (key x₁ hm₁ hx₁ a₁).2.2
    have h2 := (key x₂ hm₂ hx₂ a₂).2.2
    rw [ha₁] at h1
    rw [ha₂] at h2
    exact eq_zero_of_dot hind h1 h2
  have hτω : ∀ a, (T (a, 0)).1 = ω • a := fun a => by
    have h1 := (key x₁ hm₁ hx₁ a).2.1
    have h2 := (key x₂ hm₂ hx₂ a).2.1
    rw [hw] at h1 h2
    have := eq_zero_of_dot (v := (T (a, 0)).1 - ω • a) hind
      (by rw [show dot x₁ ((T (a, 0)).1 - ω • a) = dot x₁ (T (a, 0)).1 - ω * dot x₁ a by
            simp only [dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring]
          rw [← h1]; ring)
      (by rw [show dot x₂ ((T (a, 0)).1 - ω • a) = dot x₂ (T (a, 0)).1 - ω * dot x₂ a by
            simp only [dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring]
          rw [← h2]; ring)
    exact sub_eq_zero.1 this
  refine ⟨ω, fun v => ?_⟩
  obtain ⟨a, s⟩ := v
  rw [hsplit]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    rw [hτω, ht0, add_zero]
  · simp only [Prod.snd_add]
    rw [(key x₁ hm₁ hx₁ a).1, hw, zero_add]

omit [Finite F] in
theorem eq_zero_or_one_of_add_sq {a : F} (h : a + a ^ 2 = 0) : a = 0 ∨ a = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : a * (a - 1) = 0 := by linear_combination h - a * h2
  rcases mul_eq_zero.1 e with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

omit [Finite F] in
theorem eq_of_add_eq_zero' {a b : F} (h : a + b = 0) : a = b := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h - b * h2

omit [Finite F] in
theorem eq_one_of_forms {t₀₀ t₀₁ t₁₀ t₁₁ : F} (hdet : t₀₀ * t₁₁ + t₀₁ * t₁₀ ≠ 0)
    {S : Set (F × F × F)}
    (hS : ∀ s ∈ S, t₁₀ * s.1 + (t₀₀ + t₁₁) * s.2.1 + t₀₁ * s.2.2 = 0 ∧
      (t₀₀ + t₀₀ ^ 2) * s.1 + t₀₁ * s.2.1 + t₀₁ ^ 2 * s.2.2 = 0 ∧
      t₁₀ ^ 2 * s.1 + t₁₀ * s.2.1 + (t₁₁ + t₁₁ ^ 2) * s.2.2 = 0)
    (hline : ∀ w : F × F × F, ∃ s ∈ S, ∀ c : F, s ≠ c • w) :
    t₀₀ = 1 ∧ t₀₁ = 0 ∧ t₁₀ = 0 ∧ t₁₁ = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hl : ∀ w : F × F × F, (∀ s ∈ S, ∃ c : F, s = c • w) → False := fun w h => by
    obtain ⟨s, hs, hne⟩ := hline w
    obtain ⟨c, hc⟩ := h s hs
    exact hne c hc
  have ext3 : ∀ {s : F × F × F} {c a b d : F}, s.1 = c * a → s.2.1 = c * b → s.2.2 = c * d →
      s = c • (a, b, d) := fun h1 h2 h3 => Prod.ext h1 (Prod.ext h2 h3)
  by_cases h01 : t₀₁ = 0
  · by_cases h10 : t₁₀ = 0
    ·
      subst h01 h10
      by_cases ha : t₀₀ + t₀₀ ^ 2 = 0
      · by_cases hd : t₁₁ + t₁₁ ^ 2 = 0
        · rcases eq_zero_or_one_of_add_sq ha with ha0 | ha1
          · exact absurd (by rw [ha0]; ring) hdet
          rcases eq_zero_or_one_of_add_sq hd with hd0 | hd1
          · exact absurd (by rw [hd0]; ring) hdet
          exact ⟨ha1, rfl, rfl, hd1⟩
        · exfalso
          have hne : t₀₀ + t₁₁ ≠ 0 := fun h => hd (by
            rw [← eq_of_add_eq_zero' h]; exact ha)
          refine hl (1, 0, 0) fun s hs => ⟨s.1, ext3 (by ring) ?_ ?_⟩
          · obtain ⟨e, -, -⟩ := hS s hs
            have := (mul_eq_zero.1 (by linear_combination e : (t₀₀ + t₁₁) * s.2.1 = 0)).resolve_left
              hne
            rw [this]; ring
          · obtain ⟨-, -, e⟩ := hS s hs
            have := (mul_eq_zero.1 (by linear_combination e : (t₁₁ + t₁₁ ^ 2) * s.2.2 = 0))
              |>.resolve_left hd
            rw [this]; ring
      · exfalso
        by_cases hd : t₁₁ + t₁₁ ^ 2 = 0
        · have hne : t₀₀ + t₁₁ ≠ 0 := fun h => ha (by
            rw [eq_of_add_eq_zero' h]; exact hd)
          refine hl (0, 0, 1) fun s hs => ⟨s.2.2, ext3 ?_ ?_ (by ring)⟩
          · obtain ⟨-, e, -⟩ := hS s hs
            have := (mul_eq_zero.1 (by linear_combination e : (t₀₀ + t₀₀ ^ 2) * s.1 = 0))
              |>.resolve_left ha
            rw [this]; ring
          · obtain ⟨e, -, -⟩ := hS s hs
            have := (mul_eq_zero.1 (by linear_combination e : (t₀₀ + t₁₁) * s.2.1 = 0)).resolve_left
              hne
            rw [this]; ring
        · refine hl (0, 1, 0) fun s hs => ⟨s.2.1, ext3 ?_ (by ring) ?_⟩
          · obtain ⟨-, e, -⟩ := hS s hs
            have := (mul_eq_zero.1 (by linear_combination e : (t₀₀ + t₀₀ ^ 2) * s.1 = 0))
              |>.resolve_left ha
            rw [this]; ring
          · obtain ⟨-, -, e⟩ := hS s hs
            have := (mul_eq_zero.1 (by linear_combination e : (t₁₁ + t₁₁ ^ 2) * s.2.2 = 0))
              |>.resolve_left hd
            rw [this]; ring
    ·
      exfalso
      subst h01
      set γ := t₁₀ * (1 + t₀₀ + t₁₁) with hγ
      set δ := t₁₁ + t₁₁ ^ 2 with hδ
      have hx : ∀ s ∈ S, s.1 = (t₀₀ + t₁₁) / t₁₀ * s.2.1 := fun s hs => by
        obtain ⟨e, -, -⟩ := hS s hs
        field_simp
        linear_combination e - (t₀₀ + t₁₁) * s.2.1 * h2
      have hyz : ∀ s ∈ S, γ * s.2.1 + δ * s.2.2 = 0 := fun s hs => by
        obtain ⟨e, -, e2⟩ := hS s hs
        rw [hγ, hδ]
        linear_combination e2 - t₁₀ * e + t₁₀ * (t₀₀ + t₁₁) * s.2.1 * h2
      by_cases hδ0 : δ = 0
      · by_cases hγ0 : γ = 0
        · have hsum : t₀₀ + t₁₁ = 1 := by
            have := (mul_eq_zero.1 hγ0).resolve_left h10
            linear_combination this - h2
          apply hdet
          rw [show t₀₀ = 1 + t₁₁ by linear_combination hsum - t₁₁ * h2]
          linear_combination hδ0
        · refine hl (0, 0, 1) fun s hs => ⟨s.2.2, ext3 ?_ ?_ (by ring)⟩
          · have hy : s.2.1 = 0 := by
              have := hyz s hs
              rw [hδ0, zero_mul, add_zero] at this
              exact (mul_eq_zero.1 this).resolve_left hγ0
            rw [hx s hs, hy]; ring
          · have := hyz s hs
            rw [hδ0, zero_mul, add_zero] at this
            rw [(mul_eq_zero.1 this).resolve_left hγ0]; ring
      · refine hl ((t₀₀ + t₁₁) / t₁₀, 1, γ / δ) fun s hs => ⟨s.2.1, ext3 ?_ (by ring) ?_⟩
        · rw [hx s hs]; ring
        · have := hyz s hs
          field_simp
          linear_combination this - γ * s.2.1 * h2
  ·
    exfalso
    set α := t₀₀ + t₀₀ ^ 2 + t₀₁ * t₁₀ with hα
    set β := t₀₁ * (1 + t₀₀ + t₁₁) with hβ
    have hz : ∀ s ∈ S, s.2.2 = (t₁₀ * s.1 + (t₀₀ + t₁₁) * s.2.1) / t₀₁ := fun s hs => by
      obtain ⟨e, -, -⟩ := hS s hs
      field_simp
      linear_combination e - (t₁₀ * s.1 + (t₀₀ + t₁₁) * s.2.1) * h2
    have hxy : ∀ s ∈ S, α * s.1 + β * s.2.1 = 0 := fun s hs => by
      obtain ⟨e, e1, -⟩ := hS s hs
      rw [hα, hβ]
      linear_combination e1 - t₀₁ * e + (t₀₁ * t₁₀ * s.1 + t₀₁ * (t₀₀ + t₁₁) * s.2.1) * h2
    by_cases hβ0 : β = 0
    · by_cases hα0 : α = 0
      · have hsum : t₀₀ + t₁₁ = 1 := by
          have := (mul_eq_zero.1 hβ0).resolve_left h01
          linear_combination this - h2
        apply hdet
        rw [show t₁₁ = 1 + t₀₀ by linear_combination hsum - t₀₀ * h2]
        linear_combination hα0
      · refine hl (0, 1, (t₀₀ + t₁₁) / t₀₁) fun s hs => ⟨s.2.1, ext3 ?_ (by ring) ?_⟩
        · have := hxy s hs
          rw [hβ0, zero_mul, add_zero] at this
          rw [(mul_eq_zero.1 this).resolve_left hα0]; ring
        · have hx0 : s.1 = 0 := by
            have := hxy s hs
            rw [hβ0, zero_mul, add_zero] at this
            exact (mul_eq_zero.1 this).resolve_left hα0
          rw [hz s hs, hx0]; ring
    · refine hl (1, α / β, (t₁₀ + (t₀₀ + t₁₁) * (α / β)) / t₀₁)
        fun s hs => ⟨s.1, ext3 (by ring) ?_ ?_⟩
      · have := hxy s hs
        field_simp
        linear_combination this - α * s.1 * h2
      · have hy : s.2.1 = α / β * s.1 := by
          have := hxy s hs
          field_simp
          linear_combination this - α * s.1 * h2
        rw [hz s hs, hy]
        ring

end CFSG.Quasithin.MS93.S37R
