module

public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

open SL23

theorem sl3_sqone_central : ∀ b : SL3, b * b = 1 → ∀ n : SL3, b * n = n * b := by decide

theorem sl3_noncomm_conj : ∀ b : SL3, b ^ 4 = 1 → b * b ≠ 1 →
    ∃ y : SL3, b * (y * b * y⁻¹) ≠ (y * b * y⁻¹) * b := by decide

theorem z4StarSL23_noncomm {P : Type*} [Group P] (hP : IsZ4StarSL23 P) {a : P}
    (ha : a * a = 1) (hac : ¬ ∀ g : P, g * a = a * g) :
    ∃ y : P, a * (y * a * y⁻¹) ≠ (y * a * y⁻¹) * a := by
  obtain ⟨-, A, B, ⟨hAB, hsup⟩, hA4, hAcyc, ⟨e⟩⟩ := hP
  have hcom : ∀ c ∈ A, ∀ b ∈ B, c * b = b * c := fun c hc b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAB hc) b hb).symm
  have hdecomp : ∀ y : P, ∃ c ∈ A, ∃ b ∈ B, y = c * b := fun y =>
    CFSG.Quasithin.mem_sup_of_commute hAB (hsup ▸ Subgroup.mem_top y)
  have hAcomm : ∀ c ∈ A, ∀ c' ∈ A, c * c' = c' * c := by
    intro c hc c' hc'
    obtain ⟨g, hg⟩ := hAcyc.exists_generator
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨c, hc⟩)
    obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨c', hc'⟩)
    have h1 : (g : P) ^ m = c := congrArg Subtype.val hm
    have h2 : (g : P) ^ m' = c' := congrArg Subtype.val hm'
    rw [← h1, ← h2]
    exact (Commute.zpow_zpow_self (g : P) m m').eq
  have hAcent : ∀ c ∈ A, ∀ g : P, c * g = g * c := by
    intro c hc g
    obtain ⟨c', hc', b', hb', rfl⟩ := hdecomp g
    calc c * (c' * b') = (c * c') * b' := (mul_assoc _ _ _).symm
      _ = (c' * c) * b' := by rw [hAcomm c hc c' hc']
      _ = c' * (c * b') := mul_assoc _ _ _
      _ = c' * (b' * c) := by rw [hcom c hc b' hb']
      _ = (c' * b') * c := (mul_assoc _ _ _).symm
  have hA4' : ∀ c ∈ A, c ^ 4 = 1 := fun c hc => by
    have := pow_card_eq_one' (G := ↥A) (x := ⟨c, hc⟩)
    rw [hA4] at this
    exact congrArg Subtype.val this
  obtain ⟨c, hc, b, hb, rfl⟩ := hdecomp a
  have hsq : (c * b) * (c * b) = (c * c) * (b * b) := by
    calc (c * b) * (c * b) = c * (b * c) * b := by group
      _ = c * (c * b) * b := by rw [← hcom c hc b hb]
      _ = (c * c) * (b * b) := by group
  have hb2 : b * b = (c * c)⁻¹ := by
    rw [hsq] at ha
    exact eq_inv_of_mul_eq_one_right ha
  by_cases hbb : b * b = 1
  · exfalso
    apply hac
    have hbc : ∀ s ∈ B, b * s = s * b := fun s hs => by
      have := sl3_sqone_central (e ⟨b, hb⟩)
        (by rw [← map_mul]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hbb))
        (e ⟨s, hs⟩)
      have h2 : (⟨b, hb⟩ : ↥B) * ⟨s, hs⟩ = ⟨s, hs⟩ * ⟨b, hb⟩ := by
        apply e.injective
        rw [map_mul, map_mul]
        exact this
      exact congrArg Subtype.val h2
    intro g
    obtain ⟨c', hc', b', hb', rfl⟩ := hdecomp g
    calc c' * b' * (c * b) = c' * (b' * c) * b := by group
      _ = c' * (c * b') * b := by rw [← hcom c hc b' hb']
      _ = (c' * c) * (b' * b) := by group
      _ = (c * c') * (b * b') := by rw [hAcomm c' hc' c hc, hbc b' hb']
      _ = c * (c' * b) * b' := by group
      _ = c * (b * c') * b' := by rw [hcom c' hc' b hb]
      _ = c * b * (c' * b') := by group
  · have hb4 : b ^ 4 = 1 := by
      have h4 : b ^ 4 = (b * b) * (b * b) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [h4, hb2]
      have : (c * c) * (c * c) = 1 := by
        have h := hA4' c hc
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at h
        exact h
      calc (c * c)⁻¹ * (c * c)⁻¹ = ((c * c) * (c * c))⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hβ4 : (e ⟨b, hb⟩) ^ 4 = 1 := by
      rw [← map_pow]
      exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hb4)
    have hβ2 : (e ⟨b, hb⟩) * (e ⟨b, hb⟩) ≠ 1 := fun h => hbb (by
      have : (⟨b, hb⟩ : ↥B) * ⟨b, hb⟩ = 1 := by
        apply e.injective
        rw [map_mul, h, map_one]
      exact congrArg Subtype.val this)
    obtain ⟨γ, hγ⟩ := sl3_noncomm_conj _ hβ4 hβ2
    refine ⟨((e.symm γ : ↥B) : P), fun h => hγ ?_⟩
    set y : P := ((e.symm γ : ↥B) : P) with hy
    have hyB : y ∈ B := (e.symm γ).2
    have hyc : y * c * y⁻¹ = c := by
      rw [← hAcent c hc y]
      group
    have h1 : c * b * (y * (c * b) * y⁻¹) = (c * c) * (b * (y * b * y⁻¹)) := by
      calc c * b * (y * (c * b) * y⁻¹) = c * b * ((y * c * y⁻¹) * (y * b * y⁻¹)) := by group
        _ = c * b * (c * (y * b * y⁻¹)) := by rw [hyc]
        _ = c * (b * c) * (y * b * y⁻¹) := by group
        _ = (c * c) * (b * (y * b * y⁻¹)) := by rw [← hcom c hc b hb]; group
    have h2 : (y * (c * b) * y⁻¹) * (c * b) = (c * c) * ((y * b * y⁻¹) * b) := by
      calc (y * (c * b) * y⁻¹) * (c * b) = ((y * c * y⁻¹) * (y * b * y⁻¹)) * (c * b) := by group
        _ = (c * (y * b * y⁻¹)) * (c * b) := by rw [hyc]
        _ = c * ((y * b * y⁻¹) * c) * b := by group
        _ = (c * c) * ((y * b * y⁻¹) * b) := by
          rw [← hAcent c hc (y * b * y⁻¹)]
          group
    have hEq : b * (y * b * y⁻¹) = (y * b * y⁻¹) * b := by
      have := h
      rw [h1, h2] at this
      exact mul_left_cancel this
    have hEqB : (⟨b, hb⟩ : ↥B) * ((e.symm γ) * ⟨b, hb⟩ * (e.symm γ)⁻¹) =
        ((e.symm γ) * ⟨b, hb⟩ * (e.symm γ)⁻¹) * ⟨b, hb⟩ := Subtype.ext hEq
    have := congrArg e hEqB
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at this
    exact this
end InspW2

end S143

end CFSG.Quasithin
