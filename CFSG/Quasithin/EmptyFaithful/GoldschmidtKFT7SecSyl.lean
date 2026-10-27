module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived

public section

namespace CFSG.Quasithin.SBd19F

section Sylow

open scoped commutatorElement Pointwise

variable {E : Type*} [Group E]

private theorem commutator_mul_central {p q a b : E} (ha : a ∈ Subgroup.center E)
    (hb : b ∈ Subgroup.center E) : ⁅p * a, q * b⁆ = ⁅p, q⁆ := by
  have ha' : ∀ g, g * a = a * g := Subgroup.mem_center_iff.1 ha
  have hb' : ∀ g, g * b = b * g := Subgroup.mem_center_iff.1 hb
  simp only [commutatorElement_def]
  calc p * a * (q * b) * (p * a)⁻¹ * (q * b)⁻¹
      = p * (a * (q * b) * a⁻¹) * p⁻¹ * (q * b)⁻¹ := by group
    _ = p * q * (b * (p⁻¹ * b⁻¹)) * q⁻¹ := by rw [← ha', mul_inv_cancel_right]; group
    _ = p * q * p⁻¹ * q⁻¹ := by rw [← hb']; group

private theorem commutator_sup_central_le {A P : Subgroup E} (hAZ : A ≤ Subgroup.center E) :
    ⁅P ⊔ A, P ⊔ A⁆ ≤ P := by
  have hAN : A.Normal := Subgroup.normal_of_le_center hAZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : x ∈ (P : Set E) * (A : Set E) := by rw [← Subgroup.mul_normal]; exact hx
  have hy' : y ∈ (P : Set E) * (A : Set E) := by rw [← Subgroup.mul_normal]; exact hy
  obtain ⟨p, hp, a, ha, rfl⟩ := hx'
  obtain ⟨q, hq, b, hb, rfl⟩ := hy'
  rw [commutator_mul_central (hAZ ha) (hAZ hb), commutatorElement_def]
  exact P.mul_mem (P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp)) (P.inv_mem hq)

theorem eq_bot_of_central_two_complement [Finite E] [Group.IsPerfect E] {A P : Subgroup E}
    (hAZ : A ≤ Subgroup.center E) (hA : IsPGroup 2 A) (hE : Nat.card E = 168 * Nat.card A)
    (hP : Nat.card P = 8) (hPA : P ⊓ A = ⊥) : A = ⊥ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A.Normal := Subgroup.normal_of_le_center hAZ
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  obtain ⟨Q, hTQ⟩ := (hP2.to_sup_of_normal_right hA).exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hQ : Nat.card Q = 8 * Nat.card A := by
    rw [Sylow.card_eq_multiplicity, hE, hk, show 168 * 2 ^ k = 2 ^ (k + 3) * 21 by
      rw [pow_add]; ring, Nat.factorization_mul (by positivity) (by norm_num),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero, pow_add]
    ring
  have hcard : Nat.card P * Nat.card A ≤ Nat.card ↥(P ⊔ A) := by
    let f : P × A → ↥(P ⊔ A) := fun x => ⟨x.1 * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨p, hp⟩, ⟨a, ha⟩⟩ ⟨⟨q, hq⟩, ⟨b, hb⟩⟩ h
      have h' : p * a = q * b := congrArg Subtype.val h
      have hmem : q⁻¹ * p ∈ P ⊓ A := by
        refine ⟨P.mul_mem (P.inv_mem hq) hp, ?_⟩
        have : q⁻¹ * p = b * a⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc]
          exact eq_mul_inv_of_mul_eq h'
        rw [this]
        exact A.mul_mem hb (A.inv_mem ha)
      rw [hPA, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      subst hmem
      have : a = b := mul_left_cancel h'
      subst this
      rfl
    simpa [Nat.card_prod] using Nat.card_le_card_of_injective f hf
  have hTQ' : P ⊔ A = Q :=
    Subgroup.eq_of_le_of_card_ge hTQ (by rw [hQ, ← hP]; exact hcard)
  have hA' := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived Q A hAZ
    hA).1
  have hle : ⁅(Q : Subgroup E), (Q : Subgroup E)⁆ ≤ P := by
    rw [← hTQ']
    exact commutator_sup_central_le hAZ
  rw [eq_bot_iff, ← hPA]
  exact le_inf (hA'.trans hle) le_rfl

end Sylow

end CFSG.Quasithin.SBd19F
