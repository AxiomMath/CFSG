module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Prod
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace E217R4

variable {Γ : Type*} [Group Γ]

theorem irreducible_of_swap {a₁ a₂ z₁ t' : Γ} {T₀ : Subgroup Γ} (ha₁3 : a₁ ^ 3 = 1)
    (ha₁1 : a₁ ≠ 1) (ha₂3 : a₂ ^ 3 = 1) (ha₂1 : a₂ ≠ 1)
    (hcomm : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₂, x * y = y * x)
    (hz₁T₀ : z₁ ∈ T₀) (ht'T₀ : t' ∈ T₀)
    (hz₁x : ∀ x ∈ Subgroup.zpowers a₁, z₁ * x * z₁⁻¹ = x⁻¹)
    (hz₁y : ∀ y ∈ Subgroup.zpowers a₂, z₁ * y * z₁⁻¹ = y)
    (hP₁t' : (Subgroup.zpowers a₁).map (MulAut.conj t').toMonoidHom = Subgroup.zpowers a₂)
    (hP₂t' : (Subgroup.zpowers a₂).map (MulAut.conj t').toMonoidHom = Subgroup.zpowers a₁)
    {C : Subgroup Γ} (hCĀ : C ≤ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂)
    (hCN : T₀ ≤ Subgroup.normalizer (C : Set Γ)) :
    C = ⊥ ∨ C = Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ := by
  set P₁ := Subgroup.zpowers a₁ with hP₁
  set P₂ := Subgroup.zpowers a₂ with hP₂
  set Ā := P₁ ⊔ P₂ with hĀ
  have hdec : ∀ c ∈ Ā, ∃ x ∈ P₁, ∃ y ∈ P₂, x * y = c := fun c hc' =>
    exists_mul_of_mem_sup hcomm hc'
  have hP₁c : Nat.card P₁ = 3 := by
    rw [hP₁, Nat.card_zpowers]
    exact orderOf_eq_prime ha₁3 ha₁1
  have hP₂c : Nat.card P₂ = 3 := by
    rw [hP₂, Nat.card_zpowers]
    exact orderOf_eq_prime ha₂3 ha₂1
  have hP₁3 : ∀ x ∈ P₁, x ^ 3 = 1 := fun x hx => by
    have := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥P₁))
    rw [hP₁c] at this
    exact congrArg Subtype.val this
  have hP₂3 : ∀ y ∈ P₂, y ^ 3 = 1 := fun y hy => by
    have := pow_card_eq_one' (x := (⟨y, hy⟩ : ↥P₂))
    rw [hP₂c] at this
    exact congrArg Subtype.val this
  have hP₁C : P₁ ≤ C → C = Ā := fun hP => by
    have hP₂C : P₂ ≤ C := by
      intro w hw
      rw [← hP₁t'] at hw
      obtain ⟨p, hp, rfl⟩ := hw
      exact (Subgroup.mem_normalizer_iff.1 (hCN ht'T₀) p).1 (hP hp)
    exact le_antisymm hCĀ (sup_le hP hP₂C)
  have hP₂C : P₂ ≤ C → C = Ā := fun hP => by
    have hP₁C' : P₁ ≤ C := by
      intro w hw
      rw [← hP₂t'] at hw
      obtain ⟨p, hp, rfl⟩ := hw
      exact (Subgroup.mem_normalizer_iff.1 (hCN ht'T₀) p).1 (hP hp)
    exact le_antisymm hCĀ (sup_le hP₁C' hP)
  by_cases hC : C = ⊥
  · exact Or.inl hC
  right
  obtain ⟨⟨c, hcC⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hC
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec c (hCĀ hcC)
  have hconj : z₁ * (x * y) * z₁⁻¹ = x⁻¹ * y := by
    calc z₁ * (x * y) * z₁⁻¹ = (z₁ * x * z₁⁻¹) * (z₁ * y * z₁⁻¹) := by group
      _ = x⁻¹ * y := by rw [hz₁x x hx, hz₁y y hy]
  have hCz : x⁻¹ * y ∈ C := by
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.1 (hCN hz₁T₀) (x * y)).1 hcC
  have hx2 : x * x ∈ C := by
    have h := C.mul_mem hcC (C.inv_mem hCz)
    have e : x * x = (x * y) * (x⁻¹ * y)⁻¹ := by group
    rw [e]
    exact h
  have hxC : x ∈ C := by
    have : x = (x * x) * (x * x) := by
      calc x = x ^ 3 * x := by rw [hP₁3 x hx, one_mul]
        _ = x ^ 4 := (pow_succ x 3).symm
        _ = (x * x) * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [this]
    exact C.mul_mem hx2 hx2
  have hyC : y ∈ C := by
    have := C.mul_mem (C.inv_mem hxC) hcC
    simpa using this
  by_cases hx1 : x = 1
  · subst hx1
    have hy1 : y ≠ 1 := by simpa using hc1'
    refine hP₂C ?_
    have := zpowers_eq_of_mem ha₂3 ha₂1 (hP₂3 y hy) hy1 hy
    rw [hP₂, ← this]
    exact (Subgroup.zpowers_le).2 hyC
  · have := zpowers_eq_of_mem ha₁3 ha₁1 (hP₁3 x hx) hx1 hx
    refine hP₁C ?_
    rw [hP₁, ← this]
    exact (Subgroup.zpowers_le).2 hxC

end E217R4

end CFSG.Quasithin
