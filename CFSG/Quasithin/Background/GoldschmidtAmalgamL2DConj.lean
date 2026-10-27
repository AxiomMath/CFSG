module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DRel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2D

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace Gen

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem conj_a₁_of_x {t t₁ : D} (ht₁ : t₁ ∈ A ⊓ B) (h1 : t * x = x * t₁) :
    t * a₁ * t⁻¹ = a₁ ∨ t * a₁ * t⁻¹ = a₁ * z := by
  have e : t * a₁ * t⁻¹ = x * (t₁ * a * t₁⁻¹) * x⁻¹ := by
    rw [g.a₁_eq]
    calc t * (x * a * x⁻¹) * t⁻¹ = (t * x) * a * (t * x)⁻¹ := by group
      _ = (x * t₁) * a * (x * t₁)⁻¹ := by rw [h1]
      _ = x * (t₁ * a * t₁⁻¹) * x⁻¹ := by group
  rcases g.setup.natural.conj_cases inf_le_left ht₁ g.a_mem with h | h
  · left; rw [e, h, g.a₁_eq]
  · right
    rw [e, h, g.a₁_eq]
    calc x * (a * z) * x⁻¹ = (x * a * x⁻¹) * (x * z * x⁻¹) := by group
      _ = x * a * x⁻¹ * z := by rw [g.conj_z]

theorem conj_a₁_of_xx {t t₁ : D} (ht₁ : t₁ ∈ A ⊓ B) (h1 : t * x = x * x * t₁) :
    t * a₁ * t⁻¹ = a₂ ∨ t * a₁ * t⁻¹ = a₂ * z := by
  have e : t * a₁ * t⁻¹ = x * x * (t₁ * a * t₁⁻¹) * (x * x)⁻¹ := by
    rw [g.a₁_eq]
    calc t * (x * a * x⁻¹) * t⁻¹ = (t * x) * a * (t * x)⁻¹ := by group
      _ = (x * x * t₁) * a * (x * x * t₁)⁻¹ := by rw [h1]
      _ = x * x * (t₁ * a * t₁⁻¹) * (x * x)⁻¹ := by group
  rcases g.setup.natural.conj_cases inf_le_left ht₁ g.a_mem with h | h
  · left; rw [e, h, g.a₂_eq]
  · right
    rw [e, h, g.a₂_eq]
    calc x * x * (a * z) * (x * x)⁻¹ = (x * x * a * (x * x)⁻¹) * (x * x * z * (x * x)⁻¹) := by
          group
      _ = x * x * a * (x * x)⁻¹ * z := by rw [g.conj_z']

theorem conj_a₂_of_x {t t₂ : D} (ht₂ : t₂ ∈ A ⊓ B) (h2 : t * (x * x) = x * t₂) :
    t * a₂ * t⁻¹ = a₁ ∨ t * a₂ * t⁻¹ = a₁ * z := by
  have e : t * a₂ * t⁻¹ = x * (t₂ * a * t₂⁻¹) * x⁻¹ := by
    rw [g.a₂_eq]
    calc t * (x * x * a * (x * x)⁻¹) * t⁻¹ = (t * (x * x)) * a * (t * (x * x))⁻¹ := by group
      _ = (x * t₂) * a * (x * t₂)⁻¹ := by rw [h2]
      _ = x * (t₂ * a * t₂⁻¹) * x⁻¹ := by group
  rcases g.setup.natural.conj_cases inf_le_left ht₂ g.a_mem with h | h
  · left; rw [e, h, g.a₁_eq]
  · right
    rw [e, h, g.a₁_eq]
    calc x * (a * z) * x⁻¹ = (x * a * x⁻¹) * (x * z * x⁻¹) := by group
      _ = x * a * x⁻¹ * z := by rw [g.conj_z]

theorem conj_a₂_of_xx {t t₂ : D} (ht₂ : t₂ ∈ A ⊓ B) (h2 : t * (x * x) = x * x * t₂) :
    t * a₂ * t⁻¹ = a₂ ∨ t * a₂ * t⁻¹ = a₂ * z := by
  have e : t * a₂ * t⁻¹ = x * x * (t₂ * a * t₂⁻¹) * (x * x)⁻¹ := by
    rw [g.a₂_eq]
    calc t * (x * x * a * (x * x)⁻¹) * t⁻¹ = (t * (x * x)) * a * (t * (x * x))⁻¹ := by group
      _ = (x * x * t₂) * a * (x * x * t₂)⁻¹ := by rw [h2]
      _ = x * x * (t₂ * a * t₂⁻¹) * (x * x)⁻¹ := by group
  rcases g.setup.natural.conj_cases inf_le_left ht₂ g.a_mem with h | h
  · left; rw [e, h, g.a₂_eq]
  · right
    rw [e, h, g.a₂_eq]
    calc x * x * (a * z) * (x * x)⁻¹ = (x * x * a * (x * x)⁻¹) * (x * x * z * (x * x)⁻¹) := by
          group
      _ = x * x * a * (x * x)⁻¹ * z := by rw [g.conj_z']

variable [Finite D] in
theorem conj_u {t : D} (ht : t ∈ A ⊓ B) :
    t * (a₁ * a₂) * t⁻¹ = a₁ * a₂ ∨ t * (a₁ * a₂) * t⁻¹ = z * (a₁ * a₂) := by
  have htB : t ∈ B := ht.2
  have hB := g.setup.gold.relIndex_right
  have hexp : t * (a₁ * a₂) * t⁻¹ = (t * a₁ * t⁻¹) * (t * a₂ * t⁻¹) := by group
  have hz1 := g.z_comm_a₁
  have hz2 := g.z_comm_a₂
  have hzz := g.setup.z_mul_z
  have hr12 := g.r12
  have hzu : z * (a₁ * a₂) = (a₁ * a₂) * z := by
    calc z * (a₁ * a₂) = (z * a₁) * a₂ := by group
      _ = (a₁ * z) * a₂ := by rw [hz1]
      _ = a₁ * (z * a₂) := by group
      _ = a₁ * (a₂ * z) := by rw [hz2]
      _ = (a₁ * a₂) * z := by group
  have c1 : a₁ * (a₂ * z) = z * (a₁ * a₂) := by rw [hzu]; group
  have c2 : a₁ * z * a₂ = z * (a₁ * a₂) := by
    calc a₁ * z * a₂ = (z * a₁) * a₂ := by rw [hz1]
      _ = z * (a₁ * a₂) := by group
  have c3 : a₁ * z * (a₂ * z) = a₁ * a₂ := by
    calc a₁ * z * (a₂ * z) = a₁ * (z * a₂) * z := by group
      _ = a₁ * (a₂ * z) * z := by rw [hz2]
      _ = a₁ * a₂ * (z * z) := by group
      _ = a₁ * a₂ := by rw [hzz, mul_one]
  have d1 : a₂ * a₁ = z * (a₁ * a₂) := by
    calc a₂ * a₁ = (z * z) * (a₂ * a₁) := by rw [hzz, one_mul]
      _ = z * (z * (a₂ * a₁)) := by group
      _ = z * (a₁ * a₂) := by rw [← hr12]
  have d2 : a₂ * (a₁ * z) = a₁ * a₂ := by
    calc a₂ * (a₁ * z) = (a₂ * a₁) * z := by group
      _ = (z * (a₁ * a₂)) * z := by rw [d1]
      _ = ((a₁ * a₂) * z) * z := by rw [hzu]
      _ = (a₁ * a₂) * (z * z) := by group
      _ = a₁ * a₂ := by rw [hzz, mul_one]
  have d3 : a₂ * z * a₁ = a₁ * a₂ := by
    calc a₂ * z * a₁ = a₂ * (z * a₁) := by group
      _ = a₂ * (a₁ * z) := by rw [hz1]
      _ = a₁ * a₂ := d2
  have d4 : a₂ * z * (a₁ * z) = z * (a₁ * a₂) := by
    calc a₂ * z * (a₁ * z) = a₂ * (z * a₁) * z := by group
      _ = a₂ * (a₁ * z) * z := by rw [hz1]
      _ = a₂ * a₁ * (z * z) := by group
      _ = a₂ * a₁ := by rw [hzz, mul_one]
      _ = z * (a₁ * a₂) := d1
  rcases coset_decomp hB g.x_mem g.x_not g.x2_not (B.mul_mem htB g.x_mem) with
    h1 | ⟨t₁, ht₁, h1⟩ | ⟨t₁, ht₁, h1⟩
  · exfalso
    apply g.x_not
    have := (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) h1
    simpa using this
  ·
    rcases coset_decomp hB g.x_mem g.x_not g.x2_not (B.mul_mem htB g.x2_mem) with
      h2 | ⟨t₂, ht₂, h2⟩ | ⟨t₂, ht₂, h2⟩
    · exfalso
      apply g.x2_not
      have := (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) h2
      simpa using this
    · exfalso
      apply g.x_not
      have h3 : x * (t₁ * x) = x * t₂ := by
        calc x * (t₁ * x) = (x * t₁) * x := by group
          _ = (t * x) * x := by rw [h1]
          _ = t * (x * x) := by group
          _ = x * t₂ := h2
      have h4 : t₁ * x = t₂ := mul_left_cancel h3
      have h5 : x = t₁⁻¹ * t₂ := by rw [← h4]; group
      rw [h5]
      exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht₁) ht₂
    · rcases g.conj_a₁_of_x ht₁ h1 with p | p <;> rcases g.conj_a₂_of_xx ht₂ h2 with q | q <;>
        rw [hexp, p, q]
      · exact Or.inl rfl
      · exact Or.inr c1
      · exact Or.inr c2
      · exact Or.inl c3
  ·
    rcases coset_decomp hB g.x_mem g.x_not g.x2_not (B.mul_mem htB g.x2_mem) with
      h2 | ⟨t₂, ht₂, h2⟩ | ⟨t₂, ht₂, h2⟩
    · exfalso
      apply g.x2_not
      have := (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) h2
      simpa using this
    · rcases g.conj_a₁_of_xx ht₁ h1 with p | p <;> rcases g.conj_a₂_of_x ht₂ h2 with q | q <;>
        rw [hexp, p, q]
      · exact Or.inr d1
      · exact Or.inl d2
      · exact Or.inl d3
      · exact Or.inr d4
    · exfalso
      apply g.x_not
      have h3 : x * x * (t₁ * x) = x * x * t₂ := by
        calc x * x * (t₁ * x) = (x * x * t₁) * x := by group
          _ = (t * x) * x := by rw [h1]
          _ = t * (x * x) := by group
          _ = x * x * t₂ := h2
      have h4 : t₁ * x = t₂ := mul_left_cancel h3
      have h5 : x = t₁⁻¹ * t₂ := by rw [← h4]; group
      rw [h5]
      exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht₁) ht₂

end Gen

end GoldAmL2D

end F6

end CFSG.Quasithin
