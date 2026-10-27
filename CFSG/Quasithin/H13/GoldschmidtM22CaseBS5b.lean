module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.GM22

open Equiv

theorem perm5_exists_conj_ref :
    ∀ σ : Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
      ∃ π : Perm (Fin 5), π * σ * π⁻¹ =
        (if Perm.sign σ = 1 then swap 0 1 * swap 2 3 else swap 0 1) := by
  decide +kernel

theorem perm5_isConj_of_involution {σ τ : Perm (Fin 5)} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (h1 : σ ≠ 1) (h2 : τ ≠ 1) (hs : Perm.sign σ = Perm.sign τ) :
    ∃ π : Perm (Fin 5), π * σ * π⁻¹ = τ := by
  obtain ⟨a, ha⟩ := perm5_exists_conj_ref σ hσ h1
  obtain ⟨b, hb⟩ := perm5_exists_conj_ref τ hτ h2
  rw [← hs] at hb
  refine ⟨b⁻¹ * a, ?_⟩
  calc b⁻¹ * a * σ * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * σ * a⁻¹) * b := by group
    _ = b⁻¹ * (b * τ * b⁻¹) * b := by rw [ha, hb]
    _ = τ := by group

theorem perm5_sq_eq_one_of_sign_one {σ : Perm (Fin 5)} (hs : Perm.sign σ = 1)
    (h8 : σ ^ 8 = 1) : σ * σ = 1 := by
  have key : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ^ 8 = 1 → σ * σ = 1 := by
    decide +kernel
  exact key σ hs h8

theorem perm5_pow_eight_of_two_power {σ : Perm (Fin 5)} {k : ℕ} (h : σ ^ 2 ^ k = 1) :
    σ ^ 8 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  have h120 : orderOf σ ∣ 120 := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
  rw [hj] at h120
  have hj3 : j ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 (by omega)).trans h120
    norm_num at h16
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact pow_dvd_pow 2 hj3

theorem card_centralizer_swap (x y : Fin 5) (hxy : x ≠ y) :
    Nat.card (Subgroup.centralizer ({swap x y} : Set (Perm (Fin 5)))) = 12 := by
  classical
  have key : ∀ x y : Fin 5, x ≠ y →
      (Finset.univ.filter (fun σ : Perm (Fin 5) => swap x y * σ = σ * swap x y)).card = 12 := by
    decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert key x y hxy using 2
  ext σ
  simp [Subgroup.mem_centralizer_iff]

end CFSG.Quasithin.H13.GM22
