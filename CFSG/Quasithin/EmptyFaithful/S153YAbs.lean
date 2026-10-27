module

public import CFSG.Quasithin.Background.A1cA132Struct

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

section Abstract

variable {Q : Type*} [Group Q] {A : Type*} [Group A]

theorem exists_inverted_mul_central (ψ : Q →* A) (Ys Rs : Subgroup Q) (ρ₀ : Q)
    (hRY : Rs ≤ Subgroup.normalizer (Ys : Set Q)) (hρ₀ : ρ₀ ∈ Rs)
    (hZodd : ∀ y ∈ Ys, ψ y = 1 → Odd (orderOf y))
    (hZc : ∀ y ∈ Ys, ψ y = 1 → ∀ y' ∈ Ys, y' * y = y * y')
    (hZR : ∀ y ∈ Ys, ψ y = 1 → ∀ ρ ∈ Rs, ρ * y = y * ρ)
    (hP3 : ∀ y ∈ Ys, ψ y ^ 3 = 1)
    (hinv : ∀ y ∈ Ys, ψ ρ₀ * ψ y * (ψ ρ₀)⁻¹ = (ψ y)⁻¹) {y : Q} (hy : y ∈ Ys) :
    ∃ y₀ ∈ Ys, ∃ w ∈ Ys, ψ w = 1 ∧ y = y₀ * w ∧ y₀ ^ 3 = 1 := by
  have hcY : ρ₀ * y * ρ₀⁻¹ ∈ Ys := (Subgroup.mem_normalizer_iff.mp (hRY hρ₀) y).mp hy
  have hz₁Y : y * (ρ₀ * y * ρ₀⁻¹) ∈ Ys := Ys.mul_mem hy hcY
  have hz₁ψ : ψ (y * (ρ₀ * y * ρ₀⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hinv y hy, mul_inv_cancel]
  obtain ⟨m, hm⟩ := hZodd _ hz₁Y hz₁ψ
  set z₁ : Q := y * (ρ₀ * y * ρ₀⁻¹) with hz₁
  set z : Q := (z₁⁻¹) ^ (m + 1) with hz
  have hzY : z ∈ Ys := Ys.pow_mem (Ys.inv_mem hz₁Y) _
  have hzψ : ψ z = 1 := by rw [hz, map_pow, map_inv, hz₁ψ, inv_one, one_pow]
  have hzsq : z * z = z₁⁻¹ := by
    have h1 : (z₁⁻¹) ^ (orderOf z₁) = 1 := by
      rw [inv_pow, pow_orderOf_eq_one, inv_one]
    calc z * z = (z₁⁻¹) ^ (m + 1) * (z₁⁻¹) ^ (m + 1) := rfl
      _ = (z₁⁻¹) ^ (orderOf z₁ + 1) := by rw [← pow_add, hm]; congr 1; ring
      _ = z₁⁻¹ := by rw [pow_succ, h1, one_mul]
  have hzc : ∀ y' ∈ Ys, y' * z = z * y' := fun y' hy' => hZc z hzY hzψ y' hy'
  have hzρ : ρ₀ * z = z * ρ₀ := hZR z hzY hzψ ρ₀ hρ₀
  have hy₀Y : y * z ∈ Ys := Ys.mul_mem hy hzY
  have hyz : (y * z)⁻¹ = y⁻¹ * z⁻¹ := by rw [hzc y hy, mul_inv_rev]
  have hinvy₀ : ρ₀ * (y * z) * ρ₀⁻¹ = (y * z)⁻¹ := by
    have e1 : ρ₀ * (y * z) * ρ₀⁻¹ = (ρ₀ * y * ρ₀⁻¹) * (ρ₀ * z * ρ₀⁻¹) := by group
    have e2 : ρ₀ * z * ρ₀⁻¹ = z := by rw [hzρ]; group
    have e3 : ρ₀ * y * ρ₀⁻¹ = y⁻¹ * z₁ := by rw [hz₁]; group
    have e4 : z₁ = z⁻¹ * z⁻¹ := by rw [← mul_inv_rev, hzsq, inv_inv]
    rw [e1, e2, e3, e4, hyz]
    group
  have hy₀3 : (y * z) ^ 3 = 1 := by
    set u : Q := (y * z) ^ 3 with hu
    have huY : u ∈ Ys := Ys.pow_mem hy₀Y 3
    have huψ : ψ u = 1 := by rw [hu, map_pow]; exact hP3 _ hy₀Y
    have hu1 : ρ₀ * u * ρ₀⁻¹ = u := by
      rw [hZR u huY huψ ρ₀ hρ₀]; group
    have hu2 : ρ₀ * u * ρ₀⁻¹ = u⁻¹ := by
      have e : ρ₀ * (y * z) ^ 3 * ρ₀⁻¹ = (ρ₀ * (y * z) * ρ₀⁻¹) ^ 3 := conj_pow.symm
      rw [hu, e, hinvy₀, inv_pow]
    have hsq : u * u = 1 := by
      have h' : u = u⁻¹ := hu1.symm.trans hu2
      calc u * u = u * u⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel u
    have hodd := hZodd u huY huψ
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hodd) (by decide)
  refine ⟨y * z, hy₀Y, z⁻¹, Ys.inv_mem hzY, ?_, ?_, hy₀3⟩
  · rw [map_inv, hzψ, inv_one]
  · group

theorem three_group_of_inv (ψ : Q →* A) (Ys Rs : Subgroup Q) (ρ₀ : Q)
    (hRY : Rs ≤ Subgroup.normalizer (Ys : Set Q)) (hρ₀ : ρ₀ ∈ Rs)
    (hZodd : ∀ y ∈ Ys, ψ y = 1 → Odd (orderOf y))
    (hZc : ∀ y ∈ Ys, ψ y = 1 → ∀ y' ∈ Ys, y' * y = y * y')
    (hZR : ∀ y ∈ Ys, ψ y = 1 → ∀ ρ ∈ Rs, ρ * y = y * ρ)
    (hP3 : ∀ y ∈ Ys, ψ y ^ 3 = 1)
    (hPab : ∀ y ∈ Ys, ∀ y' ∈ Ys, ψ y * ψ y' = ψ y' * ψ y)
    (hinv : ∀ y ∈ Ys, ψ ρ₀ * ψ y * (ψ ρ₀)⁻¹ = (ψ y)⁻¹) (hgen : Ys ≤ ⁅Ys, Rs⁆) :
    ClassLeTwo (⊤ : Subgroup ↥Ys) ∧ Subgroup.closure {x : ↥Ys | x ^ 3 = 1} = ⊤ ∧
      ∀ x : ↥Ys, x ^ 3 = 1 := by
  have hΩ : Subgroup.closure {x : Q | x ∈ Ys ∧ x ^ 3 = 1} = Ys := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
    · intro y hy
      refine (?_ : ⁅Ys, Rs⁆ ≤ Subgroup.closure {x : Q | x ∈ Ys ∧ x ^ 3 = 1}) (hgen hy)
      rw [Subgroup.commutator_le]
      intro y₁ hy₁ ρ hρ
      obtain ⟨y₀, hy₀, w, hwY, hwψ, rfl, hy₀3⟩ :=
        exists_inverted_mul_central ψ Ys Rs ρ₀ hRY hρ₀ hZodd hZc hZR hP3 hinv hy₁
      have hρw : ρ * w = w * ρ := hZR w hwY hwψ ρ hρ
      have hwρ : w * ρ * w⁻¹ = ρ := by rw [← hρw]; group
      have e : ⁅y₀ * w, ρ⁆ = y₀ * (ρ * y₀ * ρ⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        calc y₀ * w * ρ * (y₀ * w)⁻¹ * ρ⁻¹ = y₀ * (w * ρ * w⁻¹) * y₀⁻¹ * ρ⁻¹ := by group
          _ = y₀ * ρ * y₀⁻¹ * ρ⁻¹ := by rw [hwρ]
          _ = y₀ * (ρ * y₀ * ρ⁻¹)⁻¹ := by group
      rw [e]
      have hρy₀ : ρ * y₀ * ρ⁻¹ ∈ Ys := (Subgroup.mem_normalizer_iff.mp (hRY hρ) y₀).mp hy₀
      have hρy₀3 : (ρ * y₀ * ρ⁻¹) ^ 3 = 1 := by
        have e3 : (ρ * y₀ * ρ⁻¹) ^ 3 = ρ * y₀ ^ 3 * ρ⁻¹ := conj_pow
        rw [e3, hy₀3]
        group
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hy₀, hy₀3⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨hρy₀, hρy₀3⟩))
  have hcl : ClassLeTwo (⊤ : Subgroup ↥Ys) := by
    unfold ClassLeTwo
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    have hψ : ψ (((⁅a, b⁆ : ↥Ys)) : Q) = 1 := by
      have e : (((⁅a, b⁆ : ↥Ys)) : Q) = ⁅(a : Q), (b : Q)⁆ := rfl
      rw [e, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h1 := hPab a a.2 b b.2
      calc ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = (ψ b * ψ a) * (ψ a)⁻¹ * (ψ b)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hmem : (((⁅a, b⁆ : ↥Ys)) : Q) ∈ Ys := (⁅a, b⁆ : ↥Ys).2
    exact Subtype.ext (hZc _ hmem hψ (g : Q) g.2)
  have hΩtop := A1c.closure_pow_eq_top_of_closure_eq (p := 3) hΩ
  exact ⟨hcl, hΩtop, pow_eq_one_of_classLeTwo (by norm_num) hcl hΩtop⟩

end Abstract

end CFSG.Quasithin
