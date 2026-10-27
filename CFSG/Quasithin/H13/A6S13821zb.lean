module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD
import CFSG.Quasithin.H13.A6S13821zbPack

public section

namespace CFSG.Quasithin.H13.A6.A6L24

open Equiv

@[expose] def IsV4 (p : Fin 5) (σ : Perm (Fin 5)) : Prop :=
  σ p = p ∧ Perm.sign σ = 1 ∧ σ * σ = 1

instance (p : Fin 5) : DecidablePred (IsV4 p) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem isV4_conj {p : Fin 5} {x : Perm (Fin 5)} (h : IsV4 p x) (σ : Perm (Fin 5)) :
    IsV4 (σ p) (σ * x * σ⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp [Perm.mul_apply, h1]
  · rw [Perm.sign_mul, Perm.sign_mul, h2, Perm.sign_inv]
    simp
  · calc σ * x * σ⁻¹ * (σ * x * σ⁻¹) = σ * (x * x) * σ⁻¹ := by group
      _ = 1 := by rw [h3, mul_one, mul_inv_cancel]

theorem v4_gen : ∀ p : Fin 5, ∃ a b : Perm (Fin 5), IsV4 p a ∧ IsV4 p b ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b
  | 0 => ⟨swap 1 2 * swap 3 4, swap 1 3 * swap 2 4, by decide⟩
  | 1 => ⟨swap 0 2 * swap 3 4, swap 0 3 * swap 2 4, by decide⟩
  | 2 => ⟨swap 0 1 * swap 3 4, swap 0 3 * swap 1 4, by decide⟩
  | 3 => ⟨swap 0 1 * swap 2 4, swap 0 2 * swap 1 4, by decide⟩
  | 4 => ⟨swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, by decide⟩

theorem eq_of_fix : ∀ p : Fin 5, ∀ a : Perm (Fin 5), (IsV4 p a ∧ a ≠ 1) →
    ∀ q : Fin 5, a q = q → q = p := by
  decide +kernel

theorem fix_of_normalizes {p : Fin 5} {σ : Perm (Fin 5)}
    (h : ∀ x, IsV4 p x → IsV4 p (σ * x * σ⁻¹)) : σ p = p := by
  obtain ⟨a, -, ha, -, ha1, -, -⟩ := v4_gen p
  have h1 := (h a ha).1
  have h2 : a (σ⁻¹ p) = σ⁻¹ p := by
    have := congrArg (fun y => σ⁻¹ y) h1
    simpa [Perm.mul_apply] using this
  have h3 := eq_of_fix p a ⟨ha, ha1⟩ _ h2
  have := congrArg σ h3
  simpa using this.symm

theorem mem_of_isV4 : ∀ p : Fin 5, ∀ a : Perm (Fin 5), (IsV4 p a ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (IsV4 p b ∧ b ≠ 1 ∧ a ≠ b) →
    ∀ τ : Perm (Fin 5), IsV4 p τ → τ = 1 ∨ τ = a ∨ τ = b ∨ τ = a * b := by
  decide +kernel

theorem card_isV4 : ∀ p : Fin 5, (Finset.univ.filter (IsV4 p)).card = 4 := by
  decide +kernel

theorem isV4_of_comm : ∀ p : Fin 5, ∀ a : Perm (Fin 5), (IsV4 p a ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (IsV4 p b ∧ b ≠ 1 ∧ a ≠ b) →
    ∀ x : Perm (Fin 5), (x * a = a * x ∧ x * b = b * x) → IsV4 p x := by
  rintro p a ⟨⟨hap, hsa, ha⟩, ha1⟩ b ⟨⟨hbp, hsb, hb⟩, hb1, hab⟩ x ⟨hxa, hxb⟩
  exact ZbPack.v4_of_comm hap hsa ha ha1 hbp hsb hb hb1 hab hxa hxb

theorem exists_isV4 : ∀ x : Perm (Fin 5), (Perm.sign x = 1 ∧ x * x = 1 ∧ x ≠ 1) →
    ∀ y : Perm (Fin 5), (Perm.sign y = 1 ∧ y * y = 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * y = y * x) →
    ∃ p : Fin 5, IsV4 p x ∧ IsV4 p y := by
  decide +kernel

theorem mul_self_of_pow_four : ∀ σ : Perm (Fin 5), (Perm.sign σ = 1 ∧ σ ^ 4 = 1) → σ * σ = 1 := by
  decide +kernel

theorem pow_four_of_pow_eight : ∀ σ : Perm (Fin 5), σ ^ 8 = 1 → σ ^ 4 = 1 :=
  fun _ h => ZbPack.pow4_of_pow8 h

private def TwoNormal (c r : Perm (Fin 5)) : Prop :=
  r ^ 4 = 1 ∧ (r * (c * r * c⁻¹)) ^ 4 = 1 ∧ (r * (c⁻¹ * r * c)) ^ 4 = 1 ∧
    ((c * r * c⁻¹) * (c⁻¹ * r * c)) ^ 4 = 1

private instance (c r : Perm (Fin 5)) : Decidable (TwoNormal c r) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem isV4_of_twoNormal : ∀ p : Fin 5, ∀ c : Perm (Fin 5), (c p = p ∧ c ^ 3 = 1 ∧ c ≠ 1) →
    ∀ r : Perm (Fin 5), (r p = p ∧ TwoNormal c r) → IsV4 p r := by
  rintro p c ⟨hcp, hc3, hc1⟩ r ⟨hrp, h1, h2, h3, h4⟩
  rw [pow_three'] at hc3
  exact ⟨hrp, ZbPack.v4_of_tn hcp hc3 hc1 hrp h1 h2 h3 h4⟩

theorem isV4_of_normal : ∀ p : Fin 5, ∀ c : Perm (Fin 5), (c p = p ∧ c ^ 3 = 1 ∧ c ≠ 1) →
    ∀ r : Perm (Fin 5), (r p = p ∧ r ^ 4 = 1 ∧ (r * (c * r * c⁻¹)) ^ 4 = 1 ∧
      (r * (c⁻¹ * r * c)) ^ 4 = 1 ∧ ((c * r * c⁻¹) * (c⁻¹ * r * c)) ^ 4 = 1) → IsV4 p r :=
  isV4_of_twoNormal

theorem comm_pow_four_ne : ∀ p : Fin 5, ∀ c : Perm (Fin 5), (c p = p ∧ c ^ 3 = 1 ∧ c ≠ 1) →
    ∀ σ : Perm (Fin 5), (σ p = p ∧ Perm.sign σ = -1) → (σ * c * σ⁻¹ * c⁻¹) ^ 4 ≠ 1 := by
  rintro p c ⟨hcp, hc3, hc1⟩ σ ⟨hsp, hs⟩
  rw [pow_three'] at hc3
  exact ZbPack.comm_ne hcp hc3 hc1 hsp hs

private def OrbitProp (p : Fin 5) (a b : Perm (Fin 5)) (q : Fin 5) : Prop :=
  (q ≠ a q ∧ q ≠ b q ∧ q ≠ b (a q) ∧ a q ≠ b q ∧ a q ≠ b (a q) ∧ b q ≠ b (a q)) ∧
    (Finset.univ.erase p : Finset (Fin 5)) = {q, a q, b q, b (a q)}

private instance (p : Fin 5) (a b : Perm (Fin 5)) (q : Fin 5) : Decidable (OrbitProp p a b q) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem orbitProp : ∀ p : Fin 5, ∀ a : Perm (Fin 5), (IsV4 p a ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (IsV4 p b ∧ b ≠ 1 ∧ a ≠ b) → ∀ q : Fin 5, q ≠ p → OrbitProp p a b q := by
  decide +kernel

theorem orbit : ∀ p : Fin 5, ∀ a : Perm (Fin 5), (IsV4 p a ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (IsV4 p b ∧ b ≠ 1 ∧ a ≠ b) → ∀ q : Fin 5, q ≠ p →
    (q ≠ a q ∧ q ≠ b q ∧ q ≠ b (a q) ∧ a q ≠ b q ∧ a q ≠ b (a q) ∧ b q ≠ b (a q)) ∧
      (Finset.univ.erase p : Finset (Fin 5)) = {q, a q, b q, b (a q)} :=
  orbitProp

theorem exists_three : ∀ p : Fin 5, ∃ c : Perm (Fin 5), c p = p ∧ Perm.sign c = 1 ∧ c ^ 3 = 1 ∧
    c ≠ 1 := by
  decide +kernel

theorem exists_even_map : ∀ p q : Fin 5, ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p = q := by
  decide +kernel

theorem exists_conj_pow : ∀ τ : Perm (Fin 5), (Perm.sign τ = 1 ∧ τ * τ = 1 ∧ τ ≠ 1) →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ (τ * (σ * τ * σ⁻¹)) ^ 24 ≠ 1 := by
  rintro τ ⟨hs, h2, h1⟩
  exact ZbPack.conj_pow hs h2 h1

theorem eq_one_of_comm : Perm.sign (swap (0 : Fin 5) 1 * swap 1 2) = 1 ∧
    Perm.sign (swap (2 : Fin 5) 3 * swap 3 4) = 1 ∧
    ∀ σ : Perm (Fin 5), (σ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * σ ∧
      σ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * σ) → σ = 1 := by
  decide +kernel

end CFSG.Quasithin.H13.A6.A6L24
