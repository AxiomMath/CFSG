module

public import Mathlib.GroupTheory.OrderOfElement
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.Invol

open CFSG.RankThree.PartOne.Torsion37

variable {M : Type*} [CommGroup M]

@[expose] def fixS (σ : MulAut M) : Subgroup M where
  carrier := {x | σ x = x}
  one_mem' := map_one σ
  mul_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
    show σ (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : σ a = a) => by
    show σ a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[expose] def invS (σ : MulAut M) : Subgroup M where
  carrier := {x | σ x = x⁻¹}
  one_mem' := by
    show σ 1 = 1⁻¹
    simp
  mul_mem' := fun {a b} (ha : σ a = a⁻¹) (hb : σ b = b⁻¹) => by
    show σ (a * b) = (a * b)⁻¹
    rw [map_mul, ha, hb, mul_inv]
  inv_mem' := fun {a} (ha : σ a = a⁻¹) => by
    show σ a⁻¹ = a⁻¹⁻¹
    rw [map_inv, ha]

theorem apply_apply_of_mul_self {σ : MulAut M} (hσ : σ * σ = 1) (x : M) : σ (σ x) = x := by
  simpa using congrArg (fun φ : MulAut M => φ x) hσ

section Involution

variable {p : ℕ} {σ : MulAut M}

theorem fixS_inf_invS (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1) :
    fixS σ ⊓ invS σ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxf, hxi⟩
  have h1 : x = x⁻¹ := (hxf : σ x = x).symm.trans hxi
  have h2 : x ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 h1
  have h4 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h5 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hpow x)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h6 : orderOf x ∣ 1 := hcop ▸ Nat.dvd_gcd h4 h5
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)

theorem exists_mul_of_involution (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1)
    (hσ : σ * σ = 1) (x : M) : ∃ a ∈ fixS σ, ∃ b ∈ invS σ, x = a * b := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hx2 : x ^ (2 * (k + 1)) = x := by
    have : 2 * (k + 1) = p + 1 := by omega
    rw [this, pow_succ, hpow x, one_mul]
  have hσσ := apply_apply_of_mul_self hσ x
  refine ⟨(x * σ x) ^ (k + 1), ?_, (x * (σ x)⁻¹) ^ (k + 1), ?_, ?_⟩
  · show σ ((x * σ x) ^ (k + 1)) = (x * σ x) ^ (k + 1)
    rw [map_pow, map_mul, hσσ, mul_comm]
  · show σ ((x * (σ x)⁻¹) ^ (k + 1)) = ((x * (σ x)⁻¹) ^ (k + 1))⁻¹
    rw [map_pow, map_mul, map_inv, hσσ, ← inv_pow, mul_inv_rev, inv_inv, mul_comm]
  · rw [← mul_pow, mul_mul_mul_comm, mul_inv_cancel, mul_one, ← sq, ← pow_mul]
    exact hx2.symm

theorem fixS_sup_invS (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1)
    (hσ : σ * σ = 1) : fixS σ ⊔ invS σ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_involution hp hp2 hpow hσ x
  exact Subgroup.mul_mem_sup ha hb

theorem card_eq_mul [Finite M] (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1)
    (hσ : σ * σ = 1) : Nat.card M = Nat.card (fixS σ) * Nat.card (invS σ) := by
  have hdisj : Disjoint (fixS σ) (invS σ) := disjoint_iff.2 (fixS_inf_invS hp hp2 hpow)
  have hcard := card_sup_of_commute_disjoint (fun k _ l _ => mul_comm k l) hdisj
  rw [fixS_sup_invS hp hp2 hpow hσ, Subgroup.card_top] at hcard
  exact hcard

theorem eq_of_fixS_eq {τ : MulAut M} (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1)
    (hσ : σ * σ = 1) (hf : fixS σ = fixS τ) (hi : invS σ = invS τ) : σ = τ := by
  ext x
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_involution hp hp2 hpow hσ x
  have ha' : τ a = a := (hf ▸ ha : a ∈ fixS τ)
  have hb' : τ b = b⁻¹ := (hi ▸ hb : b ∈ invS τ)
  rw [map_mul, map_mul, (ha : σ a = a), ha', (hb : σ b = b⁻¹), hb']

theorem fixS_conj (φ σ : MulAut M) :
    fixS (φ * σ * φ⁻¹) = (fixS σ).map φ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  show φ (σ (φ⁻¹ x)) = x ↔ σ (φ.symm x) = φ.symm x
  constructor
  · intro h
    have h1 := congrArg φ.symm h
    rwa [MulEquiv.symm_apply_apply] at h1
  · intro h
    have h1 : σ (φ⁻¹ x) = φ⁻¹ x := h
    rw [h1]
    exact MulEquiv.apply_symm_apply φ x

theorem invS_conj (φ σ : MulAut M) :
    invS (φ * σ * φ⁻¹) = (invS σ).map φ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  show φ (σ (φ⁻¹ x)) = x⁻¹ ↔ σ (φ.symm x) = (φ.symm x)⁻¹
  constructor
  · intro h
    have h1 := congrArg φ.symm h
    rwa [MulEquiv.symm_apply_apply, map_inv] at h1
  · intro h
    have h1 : σ (φ⁻¹ x) = (φ⁻¹ x)⁻¹ := h
    rw [h1, map_inv]
    congr 1
    exact MulEquiv.apply_symm_apply φ x

theorem apply_mem_fixS_of_commute {τ : MulAut M} (h : σ * τ = τ * σ) {x : M}
    (hx : x ∈ fixS σ) : τ x ∈ fixS σ := by
  have h1 := congrArg (fun φ : MulAut M => φ x) h
  show σ (τ x) = τ x
  have : σ (τ x) = τ (σ x) := h1
  rw [this, (hx : σ x = x)]

theorem apply_mem_invS_of_commute {τ : MulAut M} (h : σ * τ = τ * σ) {x : M}
    (hx : x ∈ invS σ) : τ x ∈ invS σ := by
  have h1 := congrArg (fun φ : MulAut M => φ x) h
  show σ (τ x) = (τ x)⁻¹
  have : σ (τ x) = τ (σ x) := h1
  rw [this, (hx : σ x = x⁻¹), map_inv]

@[expose] def movedS (σ : MulAut M) : Subgroup M :=
  Subgroup.closure (Set.range fun x : M => σ x * x⁻¹)

theorem movedS_eq_invS (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x : M, x ^ p = 1)
    (hσ : σ * σ = 1) : movedS σ = invS σ := by
  apply le_antisymm
  · rw [movedS, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    show σ (σ x * x⁻¹) = (σ x * x⁻¹)⁻¹
    rw [map_mul, map_inv, apply_apply_of_mul_self hσ, mul_inv_rev, inv_inv, mul_comm]
  · intro y hy
    have hy' : σ y = y⁻¹ := hy
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have h1 : σ y * y⁻¹ ∈ movedS σ := Subgroup.subset_closure ⟨y, rfl⟩
    rw [hy'] at h1
    have h2 : y * y ∈ movedS σ := by
      have := (movedS σ).inv_mem h1
      rwa [mul_inv_rev, inv_inv] at this
    have h3 : y = (y * y) ^ (k + 1) := by
      rw [← sq, ← pow_mul]
      have : 2 * (k + 1) = p + 1 := by omega
      rw [this, pow_succ, hpow y, one_mul]
    rw [h3]
    exact (movedS σ).pow_mem h2 _

end Involution

end CFSG.RankThree.PartOne.Invol
