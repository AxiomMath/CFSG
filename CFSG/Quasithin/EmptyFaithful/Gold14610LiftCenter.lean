module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace Gold14610

@[expose] def centerInvolutions {D : Type*} [Group D] (B : Subgroup D) : Subgroup D where
  carrier := {w | ∃ b : ↥B, b ∈ Subgroup.center ↥B ∧ b ^ 2 = 1 ∧ (b : D) = w}
  one_mem' := ⟨1, Subgroup.one_mem _, one_pow _, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨b₁, h₁, e₁, rfl⟩ ⟨b₂, h₂, e₂, rfl⟩
    refine ⟨b₁ * b₂, Subgroup.mul_mem _ h₁ h₂, ?_, rfl⟩
    have hc : Commute b₁ b₂ := (Subgroup.mem_center_iff.mp h₁ b₂).symm
    rw [hc.mul_pow, e₁, e₂, one_mul]
  inv_mem' := by
    rintro _ ⟨b, h, e, rfl⟩
    exact ⟨b⁻¹, Subgroup.inv_mem _ h, by rw [inv_pow, e, inv_one], rfl⟩

theorem centerInvolutions_normal {D : Type*} [Group D] {B : Subgroup D} (hB : B.Normal) :
    (centerInvolutions B).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨b, h, e, rfl⟩ d
  have hd : d * (b : D) * d⁻¹ ∈ B := hB.conj_mem b b.2 d
  refine ⟨⟨d * b * d⁻¹, hd⟩, ?_, ?_, rfl⟩
  · rw [Subgroup.mem_center_iff]
    intro c
    have hc' : d⁻¹ * (c : D) * d ∈ B := by
      simpa using hB.conj_mem c c.2 d⁻¹
    have h1 := Subgroup.mem_center_iff.mp h ⟨d⁻¹ * c * d, hc'⟩
    have h2 : (d⁻¹ * c * d) * (b : D) = (b : D) * (d⁻¹ * c * d) := congrArg Subtype.val h1
    apply Subtype.ext
    show (c : D) * (d * b * d⁻¹) = d * b * d⁻¹ * c
    calc (c : D) * (d * b * d⁻¹) = d * ((d⁻¹ * c * d) * b) * d⁻¹ := by group
      _ = d * (b * (d⁻¹ * c * d)) * d⁻¹ := by rw [h2]
      _ = d * b * d⁻¹ * c := by group
  · apply Subtype.ext
    show (d * b * d⁻¹) ^ 2 = 1
    have : (b : D) ^ 2 = 1 := congrArg Subtype.val e
    calc (d * b * d⁻¹) ^ 2 = d * ((b : D) * b) * d⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [← pow_two, this]; group

theorem not_even_orderOf_of_mem_center {D : Type*} [Group D] [Finite D]
    (hD : Open.pCore 2 D = ⊥) {B : Subgroup D} (hB : B.Normal) {z : ↥B}
    (hz : z ∈ Subgroup.center ↥B) : ¬ Even (orderOf z) := by
  intro he
  have hne : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨r, hr⟩ := he
  have h2 : 2 ∣ orderOf z := ⟨r, by omega⟩
  have hto : orderOf (z ^ (orderOf z / 2)) = 2 := orderOf_pow_orderOf_div hne h2
  have hsq : (z ^ (orderOf z / 2)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (z ^ (orderOf z / 2))
    rwa [hto] at this
  have hp : IsPGroup 2 (centerInvolutions B) := fun w => by
    obtain ⟨b, -, hb, hw⟩ := w.2
    refine ⟨1, Subtype.ext ?_⟩
    have : (b : D) ^ 2 = 1 := congrArg Subtype.val hb
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hw]
    exact this
  have hle := le_pCore 2 (centerInvolutions_normal hB) hp
  rw [hD] at hle
  have hmem : ((z ^ (orderOf z / 2) : ↥B) : D) ∈ centerInvolutions B :=
    ⟨_, Subgroup.pow_mem _ hz _, hsq, rfl⟩
  have h1 : z ^ (orderOf z / 2) = 1 := Subtype.ext (by simpa using hle hmem)
  rw [h1, orderOf_one] at hto
  omega

end Gold14610

end CFSG.Quasithin
