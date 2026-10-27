module

public import CFSG.Quasithin.Background.B1Transvection
public import CFSG.Quasithin.H13.L32NSet14

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin CFSG.Quasithin.B1

variable {V : Type} [CommGroup V]

theorem false_of_inv_five [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : IsTransvection t) {x : MulAut V} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (htx : t * x * t⁻¹ = x⁻¹) : False := by
  obtain ⟨ht1, w, hw⟩ := ht
  have h3 := (inverted_by_transvection hV hw ht1 (r := 5) (by decide) hx5 hx1 htx).2.2.2
  apply hx1
  calc x = x ^ 6 * (x ^ 5)⁻¹ := by group
    _ = 1 := by rw [show x ^ 6 = (x ^ 3) ^ 2 by group, h3, hx5]; group

theorem card_sup_of_inf_eq_bot [Finite V] {C M : Subgroup V} (h : C ⊓ M = ⊥) :
    Nat.card ↥(C ⊔ M) = Nat.card C * Nat.card M := by
  have hN : C ≤ Subgroup.normalizer (M : Set V) := fun c _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    rw [mul_comm c m, mul_assoc, mul_inv_cancel, mul_one]
  have := L32NSet14.card_sup_mul_card_inf hN
  rw [h, Subgroup.card_bot, mul_one] at this
  exact this

theorem eq_bot_of_same_action (hV : ∀ v : V, v ^ 2 = 1) {A B P : Subgroup V} {y₁ y₂ : MulAut V}
    (hy3 : y₁ ^ 3 = 1) (hB : ∀ b ∈ B, y₂ b ∈ B)
    (h1B : ∀ b ∈ B, y₁ b = b) (h2A : ∀ a ∈ A, y₂ a = a) (hPAB : P ≤ A ⊔ B)
    (hsame : ∀ v ∈ P, y₁ v = y₂ v)
    (hfpf : ∀ v ∈ P, y₁ v = v → v = 1) : P = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hPAB hv)
  have e1 : y₁ (a * b) = y₁ a * b := by rw [map_mul, h1B b hb]
  have e2 : y₂ (a * b) = a * y₂ b := by rw [map_mul, h2A a ha]
  have hδ : y₁ a * a⁻¹ = y₂ b * b⁻¹ := by
    have := hsame _ hv
    rw [e1, e2] at this
    calc y₁ a * a⁻¹ = (y₁ a * b) * (a * b)⁻¹ * (b * b⁻¹) * (a * a⁻¹)⁻¹ * (a * a⁻¹) := by
          rw [mul_inv_cancel, mul_inv_cancel, inv_one, mul_one, mul_one, mul_one]
          rw [mul_inv_rev, ← mul_assoc, mul_assoc (y₁ a) b b⁻¹, mul_inv_cancel, mul_one]
      _ = (a * y₂ b) * (a * b)⁻¹ := by
          rw [this, mul_inv_cancel, mul_inv_cancel, inv_one, mul_one, mul_one, mul_one]
      _ = y₂ b * b⁻¹ := by
          rw [mul_inv_rev, mul_comm a (y₂ b), mul_assoc, ← mul_assoc a b⁻¹ a⁻¹,
            mul_comm a b⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  set δ := y₁ a * a⁻¹ with hδdef
  have hδB : δ ∈ B := by rw [hδ]; exact B.mul_mem (hB b hb) (B.inv_mem hb)
  have hy1v : y₁ (a * b) = δ * (a * b) := by
    rw [e1, hδdef]
    group
  have hy1δ : y₁ δ = δ := h1B δ hδB
  have hsq : y₁ (y₁ (a * b)) = a * b := by
    rw [hy1v, map_mul, hy1δ, hy1v, ← mul_assoc, ← sq, hV δ, one_mul]
  have hcube : y₁ (y₁ (y₁ (a * b))) = a * b := by
    have := DFunLike.congr_fun hy3 (a * b)
    simpa [pow_succ, MulAut.mul_apply] using this
  apply hfpf _ hv
  calc y₁ (a * b) = y₁ (y₁ (y₁ (a * b))) := by rw [hsq]
    _ = a * b := hcube

end CFSG.Quasithin.H13.L32A.L2
