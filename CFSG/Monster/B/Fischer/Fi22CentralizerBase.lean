
module

public import CFSG.Certificates.NativeSetOrbit
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRealization
public import CFSG.Monster.B.Fischer.Fi22Order

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem centralizer_mk_eq {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    Subgroup.centralizer {(⟨x, hx⟩ : H)} = (Subgroup.centralizer {x}).subgroupOf H := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem card_inf_eq_card_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H ⊓ K : Subgroup G) = Nat.card (K.subgroupOf H) := by
  rw [← Subgroup.inf_subgroupOf_left]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem fi22OrigArrs_size : fi22OrigArrs.size = 2 := by
  simp [fi22OrigArrs]

theorem rep_fi22OrigArrs_nat : ∀ k < fi22OrigArrs.size,
    Rep 3510 fi22OrigArrs[k]! (fi22GenPerm k) := by
  intro k hk
  rw [fi22OrigArrs_size] at hk
  rw [fi22OrigArrs_get hk]
  exact rep_fi22Gen hk

theorem fi22GenPerm_mem : ∀ k < fi22OrigArrs.size, fi22GenPerm k ∈ fi22P := by
  intro k hk
  rw [fi22OrigArrs_size] at hk
  rw [fi22P_eq]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem le_ncard_orbit_fixedSet
    {t : Array ℕ} {x : Equiv.Perm (Fin 3510)} (ht : Rep 3510 t x)
    (hx : x ∈ fi22P) {sets : Array (List ℕ)} {par lab : Array ℕ}
    (hok : translatesOK fi22OrigArrs (fixedList 3510 t) sets par lab = true)
    (hnd : sets.toList.Nodup) :
    sets.size ≤ (MulAction.orbit fi22P
      {p : Fin 3510 | (⟨x, hx⟩ : fi22P) • p = p}).ncard := by
  have h := le_ncard_orbit_of_translatesOK (H := fi22P) rep_fi22OrigArrs_nat fi22GenPerm_mem
    (pointList_fixedList t) hok hnd
  rw [finSet_fixedList ht] at h
  exact h

theorem card_centralizer_lt_of_orbit
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ fi22P)
    (horb : 3511 ≤ (MulAction.orbit fi22P {p : Fin 3510 | (⟨x, hx⟩ : fi22P) • p = p}).ncard) :
    Nat.card (Subgroup.centralizer {(⟨x, hx⟩ : fi22P)}) < 18393661440 := by
  set Δ : Set (Fin 3510) := {p | (⟨x, hx⟩ : fi22P) • p = p}
  have hCS : Subgroup.centralizer {(⟨x, hx⟩ : fi22P)} ≤ MulAction.stabilizer fi22P Δ :=
    fun g hg => MulAction.mem_stabilizer_iff.2 (smul_fixedSet_of_mem_centralizer hg)
  have hidx := MulAction.index_stabilizer fi22P Δ
  have hmul := (MulAction.stabilizer fi22P Δ).card_mul_index
  rw [card_fi22P, hidx] at hmul
  have hle := Subgroup.card_le_of_le hCS
  have h1 : Nat.card (Subgroup.centralizer {(⟨x, hx⟩ : fi22P)}) * 3511 ≤ 64561751654400 := by
    rw [← hmul]
    exact Nat.mul_le_mul hle horb
  exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 (by norm_num))

end CFSG.Monster.B.Fischer
