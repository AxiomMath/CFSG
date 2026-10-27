module

public import CFSG.Permutation.UnitaryThreeRecognition.Torus

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def swapInv (G : Type*) [Group G] [MulAction G Ω] (a b : Ω) (s : G)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁) : Subgroup G where
  carrier := {t | t ∈ pairStab G a b ∧ s * t * s⁻¹ = t⁻¹}
  one_mem' := ⟨(pairStab G a b).one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(pairStab G a b).mul_mem hx hy, ?_⟩
    calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hx', hy']
      _ = (y * x)⁻¹ := by group
      _ = (x * y)⁻¹ := by rw [hcomm y hy x hx]
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨(pairStab G a b).inv_mem hx, ?_⟩
    calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
      _ = x⁻¹⁻¹ := by rw [hx']

theorem card_involutions_mul_le [Finite G] {a b : Ω} {s : G} (hsa : s • a = b)
    (hss : s * s = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hsq : Nat.card {t : G // t ∈ pairStab G a b ∧ t * t = 1} ≤ 2) :
    Nat.card {h : G // h * h = 1 ∧ h • a = b} * Nat.card (swapFix G a b s) ≤
      2 * Nat.card (pairStab G a b) := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hss, one_smul]
  set Tm := swapInv G a b s hcomm
  have hequiv : Nat.card {h : G // h * h = 1 ∧ h • a = b} = Nat.card Tm := by
    refine Nat.card_congr
      { toFun := fun h => ⟨h.1 * s, ?_, ?_⟩
        invFun := fun t => ⟨t.1 * s, ?_, ?_⟩
        left_inv := fun h => Subtype.ext (by simp [mul_assoc, hss])
        right_inv := fun t => Subtype.ext (by simp [mul_assoc, hss]) }
    · refine ⟨?_, ?_⟩
      · change (h.1 * s) • a = a
        rw [mul_smul, hsa]
        have : (h.1 * h.1) • a = a := by rw [h.2.1, one_smul]
        rw [mul_smul, h.2.2] at this
        exact this
      · change (h.1 * s) • b = b
        rw [mul_smul, hsb, h.2.2]
    · have hh : h.1⁻¹ = h.1 := inv_eq_of_mul_eq_one_right h.2.1
      rw [hsinv, mul_inv_rev, hsinv, hh]
      calc s * (h.1 * s) * s = s * h.1 * (s * s) := by group
        _ = s * h.1 := by rw [hss, mul_one]
    · have ht := t.property
      change t.1 ∈ pairStab G a b ∧ s * t.1 * s⁻¹ = t.1⁻¹ at ht
      calc t.1 * s * (t.1 * s) = t.1 * (s * t.1 * s⁻¹) * (s * s) := by group
        _ = 1 := by rw [ht.2, hss]; group
    · have ht := t.property
      change t.1 ∈ pairStab G a b ∧ s * t.1 * s⁻¹ = t.1⁻¹ at ht
      change (t.1 * s) • a = b
      rw [mul_smul, hsa, ht.1.2]
  have hTm : Tm ≤ pairStab G a b := fun t ht => ht.1
  have hTs : swapFix G a b s ≤ pairStab G a b := inf_le_left
  have hle := card_mul_card_le_card_mul_card_inf hTm hTs
  have hinf : Nat.card (Tm ⊓ swapFix G a b s : Subgroup G) ≤ 2 := by
    refine le_trans ?_ hsq
    apply Nat.card_le_card_of_injective
      (fun t => (⟨t.1, (mem_swapFix.mp t.2.2).1, ?_⟩ :
        {t : G // t ∈ pairStab G a b ∧ t * t = 1}))
    · intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext hxy
    · have h1 : s * t.1 * s⁻¹ = t.1⁻¹ := t.2.1.2
      have h2 : s * t.1 = t.1 * s := (mem_swapFix.mp t.2.2).2
      have : t.1 = t.1⁻¹ := by
        rw [← h1]
        calc t.1 = t.1 * s * s⁻¹ := by group
          _ = s * t.1 * s⁻¹ := by rw [h2]
      calc t.1 * t.1 = t.1 * t.1⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel _
  rw [hequiv]
  calc Nat.card Tm * Nat.card (swapFix G a b s)
      ≤ Nat.card (pairStab G a b) * Nat.card (Tm ⊓ swapFix G a b s : Subgroup G) := hle
    _ ≤ Nat.card (pairStab G a b) * 2 := Nat.mul_le_mul_left _ hinf
    _ = 2 * Nat.card (pairStab G a b) := mul_comm _ _

end CFSG.UnitaryThreeRecognition
