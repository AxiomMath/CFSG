module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.E9

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem card_modEq_card_inf_centralizer {p : ℕ} [Fact p.Prime] [Finite G] {W Y : Subgroup G}
    (hY : IsPGroup p Y) (hYW : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) :
    Nat.card W ≡ Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) [MOD p] := by
  let _ : MulAction ↥Y ↥W :=
    { smul := fun y w => ⟨(y : G) * w * (y : G)⁻¹, hYW y y.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : ↥Y) : G) * w * ((1 : ↥Y) : G)⁻¹ = w
        simp)
      mul_smul := fun y₁ y₂ w => Subtype.ext (by
        show ((y₁ * y₂ : ↥Y) : G) * w * ((y₁ * y₂ : ↥Y) : G)⁻¹ =
          (y₁ : G) * ((y₂ : G) * w * (y₂ : G)⁻¹) * (y₁ : G)⁻¹
        simp [mul_assoc]) }
  have h := hY.card_modEq_card_fixedPoints ↥W
  have e : Nat.card (MulAction.fixedPoints ↥Y ↥W) =
      Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : G), w.1.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, fun y => Subtype.ext ?_⟩
        left_inv := fun w => Subtype.ext (Subtype.ext rfl)
        right_inv := fun x => Subtype.ext rfl }
    · have h1 : ((⟨y, hy⟩ : ↥Y) • w.1 : ↥W) = w.1 := w.2 ⟨y, hy⟩
      have h2 : y * (w.1 : G) * y⁻¹ = (w.1 : G) := congrArg Subtype.val h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    · have h2 := Subgroup.mem_centralizer_iff.1 x.2.2 (y : G) y.2
      show (y : G) * (x : G) * (y : G)⁻¹ = (x : G)
      rw [mul_inv_eq_iff_eq_mul]
      exact h2
  rwa [e] at h

theorem inf_centralizer_eq_bot_of_five [Finite G] {V Y : Subgroup G} (hV : Nat.card V = 16)
    (hY : IsPGroup 5 Y) (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hVY : ⁅V, Y⁆ = V) :
    V ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := card_modEq_card_inf_centralizer hY hYV
  rw [hV] at hmod
  have hdvd : Nat.card ↥(V ⊓ Subgroup.centralizer (Y : Set G)) ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ Subgroup.centralizer (Y : Set G) ≤ V)
    rwa [hV] at this
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_contra hne
  have h1 : Nat.card ↥(V ⊓ Subgroup.centralizer (Y : Set G)) ≠ 1 := fun h =>
    hne (Subgroup.card_eq_one.1 h)
  have hi4 : i = 4 := by
    unfold Nat.ModEq at hmod
    generalize Nat.card ↥(V ⊓ Subgroup.centralizer (Y : Set G)) = c at hmod hc h1
    interval_cases i <;> norm_num at hc <;> omega
  subst hi4
  have hVC : V ≤ Subgroup.centralizer (Y : Set G) := by
    have heq : V ⊓ Subgroup.centralizer (Y : Set G) = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hV]; norm_num)
    exact heq ▸ inf_le_right
  have hbot : V = ⊥ := by
    rw [← hVY]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hVC
  rw [hbot, Subgroup.card_bot] at hV
  exact absurd hV (by norm_num)

theorem eq_bot_or_eq_of_five [Finite G] {V Y W : Subgroup G} (hV : Nat.card V = 16)
    (hY : IsPGroup 5 Y) (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hVY : ⁅V, Y⁆ = V)
    (hYW : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) (hWV : W ≤ V) : W = ⊥ ∨ W = V := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hC := inf_centralizer_eq_bot_of_five hV hY hYV hVY
  have hmod := card_modEq_card_inf_centralizer hY hYW
  have h1 : W ⊓ Subgroup.centralizer (Y : Set G) = ⊥ :=
    le_bot_iff.1 (hC ▸ inf_le_inf_right _ hWV)
  rw [h1, Subgroup.card_bot] at hmod
  have hdvd : Nat.card W ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le hWV
    rwa [hV] at this
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  unfold Nat.ModEq at hmod
  have hi' : i = 0 ∨ i = 4 := by
    generalize Nat.card W = c at hmod hc
    interval_cases i <;> norm_num at hc <;> omega
  rcases hi' with rfl | rfl
  · exact Or.inl (Subgroup.card_eq_one.1 (by simpa using hc))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hWV (by rw [hc, hV]; norm_num))

end CFSG.Quasithin.E9
