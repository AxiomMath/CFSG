module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Permutation

/-!
# Checked permutation tables for `A₇` certificates

A permutation `σ` of `Fin 7` is encoded as the table `[σ 0, …, σ 6] : List ℕ`.
Multiplication, powers and equality are transported to these tables, and every
table lies in `(List.range 7).permutations'`. A statement quantified over
`Perm (Fin 7)` (or over `alternatingGroup (Fin 7)`) can then be decided by the
kernel over 5040 small lists, instead of enumerating `Perm (Fin 7)` through its
`Fintype` instance and evaluating chains of swaps.
-/

public section

namespace CFSG.GorensteinWalter.PermTable

open Equiv

/-- Table of the product: `(σ * τ) i = σ (τ i)`. -/
@[expose] def cmp (σ τ : List ℕ) : List ℕ := τ.map fun i => σ.getD i 0

/-- Table of the identity. -/
@[expose] def idl : List ℕ := List.range 7

/-- Table of a power, following `pow_succ`. -/
@[expose] def powl (σ : List ℕ) : ℕ → List ℕ
  | 0 => idl
  | k + 1 => cmp (powl σ k) σ

/-- The table of a permutation of `Fin 7`. -/
@[expose] def enc (σ : Perm (Fin 7)) : List ℕ := (List.finRange 7).map fun i => (σ i : ℕ)

theorem enc_getD (σ : Perm (Fin 7)) (i : Fin 7) : (enc σ).getD i 0 = (σ i : ℕ) := by
  simp [enc, List.getD_eq_getElem?_getD]

theorem enc_mul (σ τ : Perm (Fin 7)) : enc (σ * τ) = cmp (enc σ) (enc τ) := by
  simp only [enc, cmp, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Perm.coe_mul]
  rw [← enc_getD σ (τ i)]
  rfl

theorem enc_one : enc 1 = idl := by
  simp [enc, idl, List.map_coe_finRange_eq_range]

theorem enc_pow (σ : Perm (Fin 7)) (k : ℕ) : enc (σ ^ k) = powl (enc σ) k := by
  induction k with
  | zero => simp only [pow_zero, enc_one, powl]
  | succ k ih => simp only [pow_succ, enc_mul, ih, powl]

theorem enc_injective : Function.Injective enc := by
  intro σ τ h
  ext i
  have h1 := enc_getD σ i
  have h2 := enc_getD τ i
  rw [h] at h1
  exact h1.symm.trans h2

theorem enc_inj {σ τ : Perm (Fin 7)} : enc σ = enc τ ↔ σ = τ :=
  enc_injective.eq_iff

theorem enc_mem_permutations (σ : Perm (Fin 7)) :
    enc σ ∈ (List.range 7).permutations' := by
  rw [List.mem_permutations']
  have h := (Equiv.Perm.map_finRange_perm σ).map (fun i : Fin 7 => (i : ℕ))
  rw [List.map_map, List.map_coe_finRange_eq_range] at h
  exact h

/-- Route a bounded quantifier through `List.all`, which the kernel evaluates
iteratively rather than through nested `Decidable` instances. -/
theorem forall_mem_of_all {L : List (List ℕ)} {P : List ℕ → Prop} [DecidablePred P]
    (h : (L.all fun l => decide (P l)) = true) : ∀ l ∈ L, P l := fun l hl =>
  of_decide_eq_true (List.all_eq_true.mp h l hl)

/-! Tables of the fixed elements used by the `A₇` certificates. -/

theorem enc_a7t : enc (a7t : Perm (Fin 7)) = [1, 0, 3, 2, 4, 5, 6] := by decide +kernel

theorem enc_a7t_inv : enc ((a7t : Perm (Fin 7))⁻¹) = [1, 0, 3, 2, 4, 5, 6] := by
  decide +kernel

theorem enc_a7a : enc (a7a : Perm (Fin 7)) = [0, 1, 2, 3, 5, 6, 4] := by decide +kernel

theorem enc_a7a_inv : enc ((a7a : Perm (Fin 7))⁻¹) = [0, 1, 2, 3, 6, 4, 5] := by
  decide +kernel

theorem enc_a7u : enc (a7u : Perm (Fin 7)) = [2, 3, 0, 1, 4, 5, 6] := by decide +kernel

end CFSG.GorensteinWalter.PermTable
