module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Tri
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Ring

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Expand

variable {F : OmegaFrame Q 1 1}

theorem OmegaFrame.expand_perp {v : V} (h₁ : polar Q v (F.e 2) = 0) (h₂ : polar Q v (F.f 2) = 0)
    (h₃ : polar Q v (F.t 0) = 0) (h₄ : polar Q v (F.t 1) = 0) :
    v = polar Q v (F.f 0) • F.e 0 + polar Q v (F.f 1) • F.e 1 + polar Q v (F.e 0) • F.f 0 +
      polar Q v (F.e 1) • F.f 1 := by
  conv_lhs => rw [F.expand v]
  simp only [Fin.sum_univ_three, h₁, h₂, h₃, h₄, mul_zero, zero_smul, add_zero]
  abel

theorem OmegaFrame.Q_four (a₀ a₁ g₀ g₁ : K) :
    Q (a₀ • F.e 0 + a₁ • F.e 1 + g₀ • F.f 0 + g₁ • F.f 1) = a₀ * g₀ + a₁ * g₁ := by
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, polar_add_left,
    polar_smul_left_eq, polar_smul_right_eq, F.Q_e, F.Q_f, F.polar_ee, F.polar_ff, F.polar_ef]
  simp
  ring

theorem OmegaFrame.polar_four (a₀ a₁ g₀ g₁ a₀' a₁' g₀' g₁' : K) :
    polar Q (a₀ • F.e 0 + a₁ • F.e 1 + g₀ • F.f 0 + g₁ • F.f 1)
      (a₀' • F.e 0 + a₁' • F.e 1 + g₀' • F.f 0 + g₁' • F.f 1) =
      a₀ * g₀' + g₀ * a₀' + a₁ * g₁' + g₁ * a₁' := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    F.polar_ee, F.polar_ff, F.polar_ef, F.polar_fe]
  simp
  ring

end Expand

section Algebra

variable [CharP K 2]

theorem exists_lambda_alg {A₀ A₁ G₀ G₁ A₀' A₁' G₀' G₁' : K} (hu : A₀ * G₀ + A₁ * G₁ = 0)
    (hw : A₀' * G₀' + A₁' * G₁' = 0)
    (huw : A₀ * G₀' + G₀ * A₀' + A₁ * G₁' + G₁ * A₁' = 0) (hν : G₀ * G₁' + G₁ * G₀' ≠ 0) :
    ∃ l : K, A₀ = l * G₁ ∧ A₁ = l * G₀ ∧ A₀' = l * G₁' ∧ A₁' = l * G₀' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨l, hl⟩ : ∃ l : K, l = (A₀ * G₀' + A₁ * G₁') / (G₀ * G₁' + G₁ * G₀') := ⟨_, rfl⟩
  have hlν : l * (G₀ * G₁' + G₁ * G₀') = A₀ * G₀' + A₁ * G₁' := by
    rw [hl]
    exact div_mul_cancel₀ _ hν
  refine ⟨l, ?_, ?_, ?_, ?_⟩
  · apply mul_right_cancel₀ hν
    linear_combination G₁' * hu - (A₁ * G₁ * G₁') * h2 - G₁ * hlν
  · apply mul_right_cancel₀ hν
    linear_combination G₀' * hu - (A₀ * G₀ * G₀') * h2 - G₀ * hlν
  · apply mul_right_cancel₀ hν
    linear_combination (-G₁') * huw + G₁ * hw + (A₀' * G₀ * G₁') * h2 - G₁' * hlν
  · apply mul_right_cancel₀ hν
    linear_combination (-G₀') * huw + G₀ * hw + (A₁' * G₁ * G₀') * h2 - G₀' * hlν

end Algebra

section Star

variable {F : OmegaFrame Q 1 1} [CharP K 2]

omit [CharP K 2] in
theorem OmegaFrame.Q_e02 : Q (F.e 0 + F.e 2) = 0 := by
  simp [QuadraticMap.map_add Q, F.Q_e, F.polar_ee]

omit [CharP K 2] in
theorem OmegaFrame.Q_f02 : Q (F.f 0 + F.f 2) = 0 := by
  simp [QuadraticMap.map_add Q, F.Q_f, F.polar_ff]

@[expose] def OmegaFrame.starTriple (F : OmegaFrame Q 1 1) : F2Triple Q where
  x := ![F.e 0 + F.e 2, F.f 0 + F.f 2, F.e 1]
  y := ![F.f 0, F.e 2, F.f 1]
  Q_x i := by fin_cases i <;> simp [F.Q_e02, F.Q_f02, F.Q_e]
  Q_y i := by fin_cases i <;> simp [F.Q_e, F.Q_f]
  polar_xx i j := by
    fin_cases i <;> fin_cases j <;>
      simp [polar_add_left, polar_add_right, F.polar_ee, F.polar_ef, F.polar_fe,
        CharTwo.add_self_eq_zero, F.Q_e02, F.Q_f02]
  polar_xy i j := by
    fin_cases i <;> fin_cases j <;>
      simp [polar_add_left, F.polar_ee, F.polar_ff, F.polar_ef, F.polar_fe]

theorem OmegaFrame.starTriple_isRat {k : Subfield K} : F.starTriple.IsRat F k := by
  intro i
  fin_cases i <;>
    simp [OmegaFrame.starTriple, F.isRat_e, F.isRat_f, OmegaFrame.IsRat.add]

end Star

section Dichotomy

variable {F : OmegaFrame Q 1 1} {k : Subfield K} [CharP K 2]

theorem OmegaFrame.starTriple_generic (hk : ∀ x : K, x ∈ k ↔ x = 0 ∨ x = 1) {u w : V} {l : K}
    (hl : l ∉ k) (hu₂ : polar Q u (F.e 2) = 0) (hu₂' : polar Q u (F.f 2) = 0)
    (hw₂ : polar Q w (F.e 2) = 0) (hw₂' : polar Q w (F.f 2) = 0)
    (hA : polar Q u (F.f 0) = l * polar Q u (F.e 1))
    (hA' : polar Q w (F.f 0) = l * polar Q w (F.e 1))
    (hν : polar Q u (F.e 0) * polar Q w (F.e 1) + polar Q u (F.e 1) * polar Q w (F.e 0) ≠ 0) :
    F.starTriple.Generic u w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hl0 : l ≠ 0 := fun h => hl (h ▸ k.zero_mem)
  have hu0 : polar Q (F.e 0 + F.e 2) u = polar Q u (F.e 0) := by
    rw [polar_add_left, polar_comm Q (F.e 0) u, polar_comm Q (F.e 2) u, hu₂, add_zero]
  have hw0 : polar Q (F.e 0 + F.e 2) w = polar Q w (F.e 0) := by
    rw [polar_add_left, polar_comm Q (F.e 0) w, polar_comm Q (F.e 2) w, hw₂, add_zero]
  have hu1 : polar Q (F.f 0 + F.f 2) u = polar Q u (F.f 0) := by
    rw [polar_add_left, polar_comm Q (F.f 0) u, polar_comm Q (F.f 2) u, hu₂', add_zero]
  have hw1 : polar Q (F.f 0 + F.f 2) w = polar Q w (F.f 0) := by
    rw [polar_add_left, polar_comm Q (F.f 0) w, polar_comm Q (F.f 2) w, hw₂', add_zero]
  have hu2 : polar Q (F.e 1) u = polar Q u (F.e 1) := polar_comm _ _ _
  have hw2 : polar Q (F.e 1) w = polar Q w (F.e 1) := polar_comm _ _ _
  refine ⟨?_, ?_⟩
  · show Phi Q u w (F.e 0 + F.e 2) (F.f 0 + F.f 2) ≠ 0
    unfold Phi
    rw [hu0, hw1, hw0, hu1, hA, hA']
    intro h
    have : l * (polar Q u (F.e 0) * polar Q w (F.e 1) + polar Q u (F.e 1) * polar Q w (F.e 0)) =
        0 := by linear_combination h
    exact (mul_ne_zero hl0 hν) this
  · intro l₀ l₁ hl₀ hl₁ ⟨h₁, h₂⟩
    change polar Q (F.e 1 + l₀ • (F.e 0 + F.e 2) + l₁ • (F.f 0 + F.f 2)) u = 0 at h₁
    change polar Q (F.e 1 + l₀ • (F.e 0 + F.e 2) + l₁ • (F.f 0 + F.f 2)) w = 0 at h₂
    rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hu2, hu0, hu1,
      hA] at h₁
    rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hw2, hw0, hw1,
      hA'] at h₂
    have hc : (1 + l₁ * l) * (polar Q u (F.e 0) * polar Q w (F.e 1) +
        polar Q u (F.e 1) * polar Q w (F.e 0)) = 0 := by
      linear_combination polar Q w (F.e 0) * h₁ - polar Q u (F.e 0) * h₂ +
        ((1 + l₁ * l) * polar Q u (F.e 0) * polar Q w (F.e 1)) * h2
    rcases mul_eq_zero.1 hc with hc | hc
    · rcases hl₁ with rfl | rfl
      · simp at hc
      · apply hl
        rw [hk]
        right
        linear_combination hc - h2
    · exact hν hc

theorem OmegaFrame.exists_lambda {u w : V} (hQu : Q u = 0) (hQw : Q w = 0) (huw : polar Q u w = 0)
    (hu₂ : polar Q u (F.e 2) = 0) (hu₂' : polar Q u (F.f 2) = 0) (hu₃ : polar Q u (F.t 0) = 0)
    (hu₄ : polar Q u (F.t 1) = 0) (hw₂ : polar Q w (F.e 2) = 0) (hw₂' : polar Q w (F.f 2) = 0)
    (hw₃ : polar Q w (F.t 0) = 0) (hw₄ : polar Q w (F.t 1) = 0)
    (hν : polar Q u (F.e 0) * polar Q w (F.e 1) + polar Q u (F.e 1) * polar Q w (F.e 0) ≠ 0) :
    ∃ l : K, polar Q u (F.f 0) = l * polar Q u (F.e 1) ∧
      polar Q u (F.f 1) = l * polar Q u (F.e 0) ∧
      polar Q w (F.f 0) = l * polar Q w (F.e 1) ∧ polar Q w (F.f 1) = l * polar Q w (F.e 0) := by
  have huexp := F.expand_perp hu₂ hu₂' hu₃ hu₄
  have hwexp := F.expand_perp hw₂ hw₂' hw₃ hw₄
  have e1 := F.Q_four (polar Q u (F.f 0)) (polar Q u (F.f 1)) (polar Q u (F.e 0))
    (polar Q u (F.e 1))
  rw [← huexp, hQu] at e1
  have e2 := F.Q_four (polar Q w (F.f 0)) (polar Q w (F.f 1)) (polar Q w (F.e 0))
    (polar Q w (F.e 1))
  rw [← hwexp, hQw] at e2
  have e3 := F.polar_four (polar Q u (F.f 0)) (polar Q u (F.f 1)) (polar Q u (F.e 0))
    (polar Q u (F.e 1)) (polar Q w (F.f 0)) (polar Q w (F.f 1)) (polar Q w (F.e 0))
    (polar Q w (F.e 1))
  rw [← huexp, ← hwexp, huw] at e3
  exact exists_lambda_alg e1.symm e2.symm e3.symm hν

variable {Rat M : Subgroup (V ≃ₗ[K] V)}

theorem hstd_of_lambda [Finite K] {p : ℕ} (hp : p.Prime) (hK : Nat.card K = 2 ^ p)
    (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {l : K} (hl : l ∈ k)
    {G₀ G₁ G₀' G₁' : K} (hν : G₀ * G₁' + G₁ * G₀' ∉ k) {u w : V}
    (hu : u = G₀ • (F.f 0 + l • F.e 1) + G₁ • (F.f 1 + l • F.e 0))
    (hw : w = G₀' • (F.f 0 + l • F.e 1) + G₁' • (F.f 1 + l • F.e 0)) (hM : eichler Q u w ∈ M)
    (t : K) : eichler Q (F.e 0) (t • F.e 1) ∈ M := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQc₀ : Q (F.f 0 + l • F.e 1) = 0 := by
    simp [QuadraticMap.map_add Q, map_smul_eq_sq, F.Q_f, F.Q_e, F.polar_fe]
  have hQc₁ : Q (F.f 1 + l • F.e 0) = 0 := by
    simp [QuadraticMap.map_add Q, map_smul_eq_sq, F.Q_f, F.Q_e, F.polar_fe]
  have hc₀c₁ : polar Q (F.f 0 + l • F.e 1) (F.f 1 + l • F.e 0) = 0 := by
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      F.polar_ff, F.polar_ef, F.polar_fe, F.polar_ee]
    simp
    linear_combination l * h2
  have hE : eichler Q u w = eichler Q (F.f 0 + l • F.e 1) ((G₀ * G₁' + G₁ * G₀') •
      (F.f 1 + l • F.e 0)) := by
    rw [hu, hw]
    exact eichler_change_basis hQc₀ hQc₁ hc₀c₁ G₀ G₁ G₀' G₁'
  have hrat₀ : F.IsRat k (F.f 0 + l • F.e 1) := (F.isRat_f 0).add ((F.isRat_e 1).smul hl)
  have hrat₁ : F.IsRat k (F.f 1 + l • F.e 0) := (F.isRat_f 1).add ((F.isRat_e 0).smul hl)
  have hne₀ : F.f 0 + l • F.e 1 ≠ 0 := fun h => by
    have : polar Q (F.f 0 + l • F.e 1) (F.e 0) = 1 := by
      simp [polar_add_left, F.polar_fe, F.polar_ee]
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hne₁ : ∀ a : K, F.f 1 + l • F.e 0 ≠ a • (F.f 0 + l • F.e 1) := fun a h => by
    have h1 : polar Q (F.f 1 + l • F.e 0) (F.e 1) = 1 := by
      simp [polar_add_left, F.polar_fe, F.polar_ee]
    have h3 : polar Q (a • (F.f 0 + l • F.e 1)) (F.e 1) = 0 := by
      simp [polar_add_left, F.polar_fe, F.polar_ee]
    rw [h, h3] at h1
    exact zero_ne_one h1
  exact std_full_of_irrational hp hK R hRM hrat₀ hrat₁ hQc₀ hQc₁ hc₀c₁ hne₀ hne₁
    (a := G₀ * G₁' + G₁ * G₀') (fun h => hν (by rw [h]; exact k.zero_mem))
    (fun h => hν (by rw [h]; exact k.one_mem)) (by rw [← hE]; exact hM) t

theorem dichotomy [Finite K] (hk : ∀ x : K, x ∈ k ↔ x = 0 ∨ x = 1) {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = 2 ^ p) (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {u w : V}
    (hQu : Q u = 0) (hQw : Q w = 0) (huw : polar Q u w = 0) (hM : eichler Q u w ∈ M)
    (hperp : ∀ v, (v = F.e 2 ∨ v = F.f 2 ∨ v = F.t 0 ∨ v = F.t 1) →
      polar Q u v = 0 ∧ polar Q w v = 0)
    (hν : Phi Q u w (F.e 0) (F.e 1) ∉ k) :
    (∀ t : K, eichler Q (F.e 0) (t • F.e 1) ∈ M) ∨ F.starTriple.Generic u w := by
  obtain ⟨hu₂, hw₂⟩ := hperp _ (Or.inl rfl)
  obtain ⟨hu₂', hw₂'⟩ := hperp _ (Or.inr (Or.inl rfl))
  obtain ⟨hu₃, hw₃⟩ := hperp _ (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hu₄, hw₄⟩ := hperp _ (Or.inr (Or.inr (Or.inr rfl)))
  have hΦ : Phi Q u w (F.e 0) (F.e 1) = polar Q u (F.e 0) * polar Q w (F.e 1) +
      polar Q u (F.e 1) * polar Q w (F.e 0) := by
    unfold Phi
    rw [polar_comm Q (F.e 0) u, polar_comm Q (F.e 1) w, polar_comm Q (F.e 0) w,
      polar_comm Q (F.e 1) u]
    ring
  have hν0 : polar Q u (F.e 0) * polar Q w (F.e 1) + polar Q u (F.e 1) * polar Q w (F.e 0) ≠ 0 :=
    fun h => hν (by rw [hΦ, h]; exact k.zero_mem)
  obtain ⟨l, hA₀, hA₁, hA₀', hA₁'⟩ := F.exists_lambda hQu hQw huw hu₂ hu₂' hu₃ hu₄ hw₂ hw₂' hw₃
    hw₄ hν0
  by_cases hl : l ∈ k
  · left
    have huexp := F.expand_perp hu₂ hu₂' hu₃ hu₄
    have hwexp := F.expand_perp hw₂ hw₂' hw₃ hw₄
    refine hstd_of_lambda hp hK R hRM hl (G₀ := polar Q u (F.e 0)) (G₁ := polar Q u (F.e 1))
      (G₀' := polar Q w (F.e 0)) (G₁' := polar Q w (F.e 1)) (by rw [← hΦ]; exact hν) ?_ ?_ hM
    · calc u = _ := huexp
        _ = _ := by rw [hA₀, hA₁]; module
    · calc w = _ := hwexp
        _ = _ := by rw [hA₀', hA₁']; module
  · right
    exact F.starTriple_generic hk hl hu₂ hu₂' hw₂ hw₂' hA₀ hA₀' hν0

end Dichotomy

end CFSG.RankThree.PartOne.SEITZ2
