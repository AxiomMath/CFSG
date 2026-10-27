module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKGen

public section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.QuasithinUnique

section Defs

variable {X H : Type} [Group X] [Group H]

@[expose] noncomputable def invol (ψ : H) : H := psi2 ψ ^ 2 ^ (twoExp ψ - 1)

@[expose] noncomputable def involAut (ψ : H) (α : MulAut X) : MulAut X :=
  α ^ (oddPart ψ * 2 ^ (twoExp ψ - 1))

@[expose] def fixSub (δ : MulAut X) (U : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ U ∧ δ x = x}
  mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨U.one_mem, map_one δ⟩
  inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by rw [map_inv, ha.2]⟩

@[expose] def twistFix (δ : MulAut X) (U : Subgroup X) (u : X) : Set X :=
  {x | x ∈ U ∧ u * δ x * u⁻¹ = x}

theorem pow_apply_comm (α : MulAut X) (s k : ℕ) (x : X) :
    (α ^ s) ((α ^ k) x) = (α ^ k) ((α ^ s) x) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem pow_apply_of_fixed {α : MulAut X} {y : X} (hy : α y = y) (k : ℕ) : (α ^ k) y = y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hy, ih]

theorem fixSub_stable {α : MulAut X} {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) (s k : ℕ) (x : X) :
    (α ^ k) x ∈ fixSub (α ^ s) U ↔ x ∈ fixSub (α ^ s) U := by
  show ((α ^ k) x ∈ U ∧ (α ^ s) ((α ^ k) x) = (α ^ k) x) ↔ (x ∈ U ∧ (α ^ s) x = x)
  rw [hU, pow_apply_comm]
  exact and_congr_right fun _ => (α ^ k).injective.eq_iff

end Defs

section Basic

variable {X H : Type} [Group X] [Group H] {Φ : X →* H} {ψ : H} {α : MulAut X}

theorem invol_eq : invol ψ = ψ ^ (oddPart ψ * 2 ^ (twoExp ψ - 1)) := by
  rw [invol, psi2_pow_eq]

theorem OutProps.invol_act (P : OutProps Φ ψ α) (x : X) :
    invol ψ * Φ x * (invol ψ)⁻¹ = Φ (involAut ψ α x) := by
  rw [invol_eq]
  exact P.act_pow _ x

theorem OutProps.invol_mul_comm (P : OutProps Φ ψ α) (x : X) (hx : involAut ψ α x = x) :
    invol ψ * Φ x = Φ x * invol ψ := by
  have h := P.invol_act x
  rw [hx] at h
  calc invol ψ * Φ x = invol ψ * Φ x * (invol ψ)⁻¹ * invol ψ := by group
    _ = Φ x * invol ψ := by rw [h]

theorem invol_mem_zpowers : invol ψ ∈ Subgroup.zpowers (psi2 ψ) :=
  Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem invol_mem_spT (U : Subgroup X) : invol ψ ∈ spT Φ ψ U :=
  Subgroup.mem_sup_right invol_mem_zpowers

theorem psi2_pow_comm_invol (s : ℕ) : invol ψ * psi2 ψ ^ s = psi2 ψ ^ s * invol ψ := by
  rw [invol, ← pow_add, ← pow_add, add_comm]

variable [Finite H]

theorem invol_sq (ha : 1 ≤ twoExp ψ) : invol ψ ^ 2 = 1 := by
  rw [invol, ← pow_mul]
  have : 2 ^ (twoExp ψ - 1) * 2 = 2 ^ twoExp ψ := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this]
  exact psi2_pow_two_exp ψ

theorem invol_ne_one (ha : 1 ≤ twoExp ψ) : invol ψ ≠ 1 := by
  rw [invol]
  refine pow_ne_one_of_lt_orderOf (by positivity) ?_
  rw [orderOf_psi2]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem OutProps.invol_not_mem_range (P : OutProps Φ ψ α) (ha : 1 ≤ twoExp ψ) :
    invol ψ ∉ Φ.range := fun h => invol_ne_one ha ((P.psi2_pow_mem_range_iff _).1 h)

end Basic

end CFSG.Quasithin.H13.F431.G2.OutK
