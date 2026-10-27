module

public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.F6.GoldAmL4

open CFSG.Quasithin.F6

theorem mem_sup_of_commute {R : Type*} [Group R] {A B : Subgroup R}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ r ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, r = a * b := by
  intro r hr
  have e : A ⊔ B = Subgroup.closure ((A : Set R) ∪ (B : Set R)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [e] at hr
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihy
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hcomm a₂ ha₂ b₁ hb₁]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv x hx ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ih
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have h1 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
      have := congrArg Inv.inv (hcomm a ha b hb)
      simpa [mul_inv_rev] using this
    rw [mul_inv_rev, h1]

theorem IsCentralProduct₂.pow_four {R : Type*} [Group R]
    (h : IsCentralProduct₂ R (Multiplicative (ZMod 4)) (QuaternionGroup 2)) (r : R) :
    r ^ 4 = 1 := by
  obtain ⟨A', B', hsup, hcomm, ⟨eA⟩, ⟨eB⟩, -⟩ := h
  have hr : r ∈ A' ⊔ B' := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm r hr
  have hab : Commute a b := hcomm a ha b hb
  have hA4 : ∀ z : Multiplicative (ZMod 4), z ^ 4 = 1 := by decide
  have hB4 : ∀ z : QuaternionGroup 2, z ^ 4 = 1 := by decide
  have ha4 : a ^ 4 = 1 := by
    have : (⟨a, ha⟩ : ↥A') ^ 4 = 1 := eA.injective (by rw [map_pow, hA4, map_one])
    simpa using congrArg Subtype.val this
  have hb4 : b ^ 4 = 1 := by
    have : (⟨b, hb⟩ : ↥B') ^ 4 = 1 := eB.injective (by rw [map_pow, hB4, map_one])
    simpa using congrArg Subtype.val this
  rw [hab.mul_pow, ha4, hb4, one_mul]

theorem IsCentralProduct₂.not_comm {R : Type*} [Group R]
    (h : IsCentralProduct₂ R (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    ∃ x y : R, x * y ≠ y * x := by
  obtain ⟨A', B', -, -, ⟨eA⟩, ⟨eB⟩, -⟩ := h
  obtain ⟨u, v, huv⟩ : ∃ u v : QuaternionGroup 2, u * v ≠ v * u := by decide
  refine ⟨(eB.symm u : R), (eB.symm v : R), fun hc => huv ?_⟩
  have : eB.symm u * eB.symm v = eB.symm v * eB.symm u := Subtype.ext hc
  have := congrArg eB this
  simpa using this

end CFSG.Quasithin.F6.GoldAmL4
