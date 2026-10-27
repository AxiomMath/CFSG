module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.H.A5W

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5
open scoped Pointwise

@[expose] def kleinSet : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kleinSet_one : (1 : Perm (Fin 5)) ∈ kleinSet := by decide +kernel

theorem kleinSet_mul : ∀ a ∈ kleinSet, ∀ b ∈ kleinSet, a * b ∈ kleinSet := by decide +kernel

theorem kleinSet_inv : ∀ a ∈ kleinSet, a⁻¹ ∈ kleinSet := by decide +kernel

theorem kleinSet_alt : ∀ a ∈ kleinSet, Equiv.Perm.sign a = 1 := by decide +kernel

@[expose] def kleinStd : Subgroup Alt5 where
  carrier := {x | (x : Perm (Fin 5)) ∈ kleinSet}
  mul_mem' := fun {a b} ha hb => kleinSet_mul a ha b hb
  one_mem' := kleinSet_one
  inv_mem' := fun {a} ha => kleinSet_inv a ha

theorem mem_kleinStd {x : Alt5} : x ∈ kleinStd ↔ (x : Perm (Fin 5)) ∈ kleinSet := Iff.rfl

theorem card_kleinStd : Nat.card kleinStd = 4 := by
  show Nat.card {x : Alt5 // (x : Perm (Fin 5)) ∈ kleinSet} = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem exists_conj_kleinStd (Q : Subgroup Alt5) (hQ : Nat.card Q = 4) :
    ∃ g : Alt5, ∀ x : Alt5, x ∈ Q ↔ g⁻¹ * x * g ∈ kleinStd := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (Nat.card Alt5).factorization 2 = 2 := by
    rw [a5_card]; decide +kernel
  let PQ : Sylow 2 Alt5 := Sylow.ofCard Q (by rw [hQ, hf]; norm_num)
  let PV : Sylow 2 Alt5 := Sylow.ofCard kleinStd (by rw [card_kleinStd, hf]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Alt5 PV PQ
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • PV : Sylow 2 Alt5) : Subgroup Alt5) = (PQ : Subgroup Alt5) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have e : (x ∈ (PQ : Subgroup Alt5)) ↔ x ∈ MulAut.conj g • (PV : Subgroup Alt5) := by rw [← h1]
  have hPQ : (PQ : Subgroup Alt5) = Q := Sylow.coe_ofCard _ _
  have hPV : (PV : Subgroup Alt5) = kleinStd := Sylow.coe_ofCard _ _
  rw [hPQ, hPV, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at e
  rw [e]
  simp [mul_assoc]

@[expose] def y5 : Perm (Fin 5) := c[0, 1, 2]

@[expose] def w5 : Perm (Fin 5) := swap 0 1 * swap 3 4

theorem y5_alt : y5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem w5_alt : w5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem y5_norm : ∀ x ∈ kleinSet, y5 * x * y5⁻¹ ∈ kleinSet := by decide +kernel

theorem w5_not_norm : ∃ x ∈ kleinSet, w5 * x * w5⁻¹ ∉ kleinSet := by decide +kernel

theorem w5_inv : w5 * y5 * w5⁻¹ = y5⁻¹ := by decide +kernel

theorem y5_pow_three : y5 ^ 3 = 1 := by decide +kernel

theorem y5_ne_one : y5 ≠ 1 := by decide +kernel

theorem card_evenWeight5 : Nat.card (evenWeight 5) = 16 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 5 → ZMod 2 => mem_evenWeight_iff x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

end CFSG.Quasithin.H.A5W
