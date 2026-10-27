module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

namespace S143

open scoped Pointwise

namespace InspW2

theorem false_of_perfect_cyclic_sylow_quot {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] {C : Subgroup Q} [C.Normal] (hC : C ≤ Subgroup.center Q) (S : Sylow 2 Q)
    (hcyc : IsCyclic ↥((S : Subgroup Q).map (QuotientGroup.mk' C))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective (QuotientGroup.mk' C) := QuotientGroup.mk'_surjective C
  have : Group.IsPerfect (Q ⧸ C) := Group.IsPerfect.ofSurjective hf
  have : Nontrivial (Q ⧸ C) := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    have htop : C = ⊤ := by
      refine eq_top_iff.mpr fun q _ => ?_
      exact (QuotientGroup.eq_one_iff q).mp (Subsingleton.elim _ _)
    have hcomm : IsMulCommutative Q := ⟨⟨fun a b => by
      have ha := Subgroup.mem_center_iff.mp (hC (htop ▸ Subgroup.mem_top a)) b
      exact ha.symm⟩⟩
    obtain ⟨a, ha⟩ := exists_ne (1 : Q)
    have : Subsingleton Q := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact ha (Subsingleton.elim _ _)
  let S' : Sylow 2 (Q ⧸ C) := S.mapSurjective hf
  have hS' : (S' : Subgroup (Q ⧸ C)) = (S : Subgroup Q).map (QuotientGroup.mk' C) :=
    Sylow.coe_mapSurjective hf S
  have hcyc' : IsCyclic S' := by
    have : IsCyclic ↥(S' : Subgroup (Q ⧸ C)) := by rw [hS']; exact hcyc
    exact this
  obtain ⟨-, hprod, -, ⟨hN, hodd, -, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S' hcyc'
  set N := CFSG.pPrimeCore 2 (Q ⧸ C) with hNdef
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (S' : Subgroup (Q ⧸ C)).subtype) := by
    intro q
    obtain ⟨q0, rfl⟩ := QuotientGroup.mk_surjective q
    have hq0 : q0 ∈ (N : Set (Q ⧸ C)) * (S' : Set (Q ⧸ C)) := by
      rw [hprod]; exact Set.mem_univ q0
    obtain ⟨n, hn, s, hs, rfl⟩ := hq0
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have := hN.conj_mem n hn s⁻¹
    simpa [mul_assoc] using this
  have : Group.IsPerfect ((Q ⧸ C) ⧸ N) := inferInstance
  have : IsCyclic ((Q ⧸ C) ⧸ N) := isCyclic_of_surjective _ hsurj
  have : IsMulCommutative ((Q ⧸ C) ⧸ N) := inferInstance
  have hsub : Subsingleton ((Q ⧸ C) ⧸ N) := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hidx : N.index = 1 := by
    rw [Subgroup.index]
    exact Nat.card_unique
  have hNtop : N = ⊤ := Subgroup.index_eq_one.mp hidx
  have hodd' : Odd (Nat.card (Q ⧸ C)) := by
    rw [hNtop, Subgroup.card_top] at hodd; exact hodd
  exact Group.IsPerfect.not_isSolvable (Q ⧸ C) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd')

theorem false_of_perfect_sylow_two_quot {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] {C : Subgroup Q} [C.Normal] (hC : C ≤ Subgroup.center Q) (S : Sylow 2 Q)
    (hrel : C.relIndex (S : Subgroup Q) ≤ 2) : False := by
  refine false_of_perfect_cyclic_sylow_quot hC S ?_
  set M : Subgroup (Q ⧸ C) := (S : Subgroup Q).map (QuotientGroup.mk' C) with hM
  have h1 : Nat.card M = C.relIndex S := by
    rw [hM, ← Subgroup.relIndex_ker (K := (S : Subgroup Q)) (QuotientGroup.mk' C),
      QuotientGroup.ker_mk']
  have hpos : 0 < Nat.card M := Nat.card_pos
  rcases (by omega : Nat.card M = 1 ∨ Nat.card M = 2) with h | h
  · have : Subsingleton M := (Nat.card_eq_one_iff_unique.mp h).1
    infer_instance
  · have : Fact (Nat.Prime (Nat.card M)) := ⟨by rw [h]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl

end InspW2

end S143

end CFSG.Quasithin
