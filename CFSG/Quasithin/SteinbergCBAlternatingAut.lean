module

public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup (eq_one_of_forall_commute_alternating)

@[expose] noncomputable def conjPerm (n : ℕ) : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) :=
  MulAut.conjNormal

theorem conjPerm_apply (n : ℕ) (σ : Perm (Fin n)) (g : alternatingGroup (Fin n)) :
    ((conjPerm n σ g : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * g * σ⁻¹ :=
  MulAut.conjNormal_apply σ g

theorem conjPerm_surjective {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) : Function.Surjective (conjPerm n) := by
  intro f
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hn f
  exact ⟨σ, MulEquiv.ext fun g => Subtype.ext (by rw [conjPerm_apply, hσ])⟩

theorem conjPerm_injective {n : ℕ} (hn : 4 ≤ n) : Function.Injective (conjPerm n) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine eq_one_of_forall_commute_alternating (by simpa using hn) fun g hg => ?_
  have h := congrArg (fun f : MulAut (alternatingGroup (Fin n)) =>
    ((f ⟨g, hg⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) hσ
  simp only [conjPerm_apply, MulAut.one_apply] at h
  calc σ * g = σ * g * σ⁻¹ * σ := by group
    _ = g * σ := by rw [h]

theorem map_conjPerm_alternatingGroup (n : ℕ) :
    (alternatingGroup (Fin n)).map (conjPerm n) = inner (alternatingGroup (Fin n)) := by
  ext f
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, MulEquiv.ext fun g => Subtype.ext (by
      rw [conjPerm_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv])⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, MulEquiv.ext fun h => Subtype.ext (by
      rw [conjPerm_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv])⟩

theorem index_inner_dvd_two {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    (inner (alternatingGroup (Fin n))).index ∣ 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [← map_conjPerm_alternatingGroup, ← alternatingGroup.index_eq_two (α := Fin n)]
  exact Subgroup.index_map_dvd _ (conjPerm_surjective hn)

theorem isSolvable_of_card_dvd_two {H : Type*} [Group H] (h : Nat.card H ∣ 2) :
    Group.IsSolvable H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · have := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card h2
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.isMulCommutative (α := H)).is_comm.comm a b

theorem isSolvable_outer_alternatingGroup {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Group.IsSolvable (Outer (alternatingGroup (Fin n))) ∧
      Nat.card (Outer (alternatingGroup (Fin n))) ∣ 2 :=
  ⟨isSolvable_of_card_dvd_two (index_inner_dvd_two hn), index_inner_dvd_two hn⟩

end CFSG.Quasithin.SteinbergCB
