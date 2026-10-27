module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem m_le_of_autInner {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) : m ≤ r := by
  obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
    (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have hq := isQuasisimple_toMulSub h.L_comp.2.2
  have e' := cqEquiv_toMulSub_comp e
  have hAL := le_of_autInner hW hq.1 hirr hAN hAel e' hAut
  have hc := card_le_two_pow_of_le hW hirr hAL hAel e' hr
  rw [hAcard] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hc

theorem orderOf_two_le_finrank_of_dvd_card_quotient {L : Subgroup (GLV V)} {S : Type} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpS : p ∣ Nat.card S) : orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  apply orderOf_two_le_finrank_of_dvd_card L hp2
  have h1 : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Nat.card_congr e.toEquiv]; exact hpS
  exact h1.trans (Subgroup.card_quotient_dvd_card _)

theorem false_of_autInner_prime {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S)
    (hlt : 2 * (r + 1) < orderOf (2 : ZMod p)) : False := by
  have hm := m_le_of_autInner h e hAut hr
  have hd := orderOf_two_le_finrank_of_dvd_card_quotient e hp2 hpS
  have hb := h.bound
  omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
