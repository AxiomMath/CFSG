module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am4

theorem eq_on_of_uniserial {P : Type*} [Group P] [Finite P] {G' : Type*} [Group G']
    (φ₁ φ₂ : P →* G') (hφ₁ : Function.Injective φ₁) (Q S : Subgroup P) (τ : P) (hτQ : τ ∈ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQS : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q)
    (hS : ∀ s ∈ S, φ₁ s = φ₂ s) (hτ : φ₁ τ = φ₂ τ)
    (hQ2 : ∀ q ∈ Q, ∃ q' ∈ Q, φ₁ q' = φ₂ q)
    (hcard : Nat.card Q = 32) (hτ1 : τ ≠ 1) (hτo : τ * τ = 1)
    (hdich : ∀ D : Subgroup P, D ≤ Q → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) →
      D ≤ Subgroup.zpowers τ ∨ D = Q) :
    ∀ q ∈ Q, φ₁ q = φ₂ q := by
  classical
  have hτ2 : Nat.card (Subgroup.zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hτo) hτ1
  let e : ↥Q ≃* ↥(Q.map φ₁) := Q.equivMapOfInjective φ₁ hφ₁
  let φ₂' : ↥Q →* ↥(Q.map φ₁) := (φ₂.comp Q.subtype).codRestrict (Q.map φ₁) fun q => by
    obtain ⟨q', hq', h⟩ := hQ2 q.1 q.2
    exact ⟨q', hq', h⟩
  let χ : ↥Q →* ↥Q := e.symm.toMonoidHom.comp φ₂'
  have hχ : ∀ q : ↥Q, φ₁ (χ q : P) = φ₂ (q : P) := by
    intro q
    have h1 : e (χ q) = φ₂' q := e.apply_symm_apply (φ₂' q)
    have h2 := congrArg Subtype.val h1
    exact h2
  have hcomm : ∀ a b : ↥Q, a * b = b * a := fun a b => Subtype.ext (hQab a a.2 b b.2)
  let δ : ↥Q →* ↥Q := MonoidHom.mk' (fun q => χ q * q⁻¹) fun a b => by
    rw [map_mul, mul_inv_rev]
    calc χ a * χ b * (b⁻¹ * a⁻¹) = χ a * (χ b * b⁻¹) * a⁻¹ := by group
      _ = χ a * (a⁻¹ * (χ b * b⁻¹)) := by
        rw [mul_assoc, ← hcomm (a⁻¹) (χ b * b⁻¹)]
      _ = χ a * a⁻¹ * (χ b * b⁻¹) := by group
  have hδ : ∀ q : ↥Q, δ q = 1 ↔ φ₁ (q : P) = φ₂ (q : P) := by
    intro q
    show χ q * q⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    constructor
    · intro h; rw [← hχ q, h]
    · intro h
      apply Subtype.ext
      apply hφ₁
      rw [hχ q, h]
  have hδequi : ∀ s (hs : s ∈ S) (q : ↥Q),
      ((δ ⟨s * (q : P) * s⁻¹, hQS s hs q q.2⟩ : ↥Q) : P) = s * (δ q : P) * s⁻¹ := by
    intro s hs q
    have hχs : ((χ ⟨s * (q : P) * s⁻¹, hQS s hs q q.2⟩ : ↥Q) : P) = s * (χ q : P) * s⁻¹ := by
      apply hφ₁
      rw [hχ]
      show φ₂ (s * (q : P) * s⁻¹) = φ₁ (s * (χ q : P) * s⁻¹)
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hχ q, hS s hs]
    show ((χ ⟨s * (q : P) * s⁻¹, hQS s hs q q.2⟩ * (⟨s * (q : P) * s⁻¹, _⟩ : ↥Q)⁻¹ : ↥Q) : P) =
      s * ((χ q * q⁻¹ : ↥Q) : P) * s⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hχs]
    simp only [Subgroup.coe_inv]
    group
  set K : Subgroup P := δ.ker.map Q.subtype with hK
  set E : Subgroup P := δ.range.map Q.subtype with hE
  have hKQ : K ≤ Q := Subgroup.map_subtype_le _
  have hEQ : E ≤ Q := Subgroup.map_subtype_le _
  have hKS : ∀ s ∈ S, ∀ d ∈ K, s * d * s⁻¹ ∈ K := by
    intro s hs d hd
    obtain ⟨q, hq, rfl⟩ := hd
    refine ⟨⟨s * (q : P) * s⁻¹, hQS s hs q q.2⟩, ?_, rfl⟩
    show δ ⟨s * (q : P) * s⁻¹, hQS s hs q q.2⟩ = 1
    apply Subtype.ext
    rw [hδequi s hs q, MonoidHom.mem_ker.mp hq]
    simp
  have hES : ∀ s ∈ S, ∀ d ∈ E, s * d * s⁻¹ ∈ E := by
    intro s hs d hd
    obtain ⟨e', ⟨q, rfl⟩, rfl⟩ := hd
    exact ⟨_, ⟨⟨s * (q : P) * s⁻¹, hQS s hs q q.2⟩, rfl⟩, hδequi s hs q⟩
  have hKcard : Nat.card K * Nat.card E = 32 := by
    have h := Subgroup.card_ker_mul_card_range δ
    rw [Subgroup.card_map_of_injective Q.subtype_injective,
      Subgroup.card_map_of_injective Q.subtype_injective, h]
    exact hcard
  have hτK : τ ∈ K := ⟨⟨τ, hτQ⟩, (hδ ⟨τ, hτQ⟩).2 hτ, rfl⟩
  rcases hdich K hKQ hKS with hKle | hKeq
  · exfalso
    have hK2 : Nat.card K ≤ 2 := hτ2 ▸ Subgroup.card_le_of_le hKle
    rcases hdich E hEQ hES with hEle | hEeq
    · have hE2 : Nat.card E ≤ 2 := hτ2 ▸ Subgroup.card_le_of_le hEle
      have := Nat.mul_le_mul hK2 hE2
      omega
    · have hEc : Nat.card E = 32 := by rw [hEeq]; exact hcard
      have hK1 : Nat.card K = 1 := by
        rw [hEc] at hKcard; omega
      have hbot : K = ⊥ := (Subgroup.card_eq_one).mp hK1
      rw [hbot] at hτK
      exact hτ1 (Subgroup.mem_bot.mp hτK)
  · intro q hq
    have hqK : q ∈ K := hKeq ▸ hq
    obtain ⟨q', hq', hq'q⟩ := hqK
    have := (hδ q').1 (MonoidHom.mem_ker.mp hq')
    rw [← hq'q]
    exact this

end CFSG.RankThree.PartTwo.Sec21.FF81.Am4
