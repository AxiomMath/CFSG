module

public import CFSG.RankThree.PartOne.S9.QD32.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.RankThree.PartOne

open CFSG.SectionRank.Ccomm CFSG.RankThree.PartOne.QD32Facts Subgroup
open scoped commutatorElement

namespace QD32Facts

theorem eq_one_or_eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {u z : C} (hu : u ^ 2 = 1) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) : u = 1 ∨ u = z := by
  classical
  have := Fintype.ofFinite C
  by_contra h
  push Not at h
  have hsub : ({1, z, u} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hz
    · exact hu
  have h3 : ({1, z, u} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using h.2.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz1.symm, h.1.symm⟩
  have := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := C) (by norm_num : 0 < 2))
  omega

theorem hom_eq_one_of_isCyclic_isPGroup_two {A C : Type*} [Group A] [Finite A] [Group C] [Finite C]
    [IsCyclic C] (hC : IsPGroup 2 C) (hA : Odd (Nat.card A)) (σ : A →* MulAut C) : σ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine MonoidHom.ext fun a => ?_
  rw [MonoidHom.one_apply]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hC
  have h1 : orderOf (σ a) ∣ Nat.card A :=
    (orderOf_map_dvd σ a).trans (orderOf_dvd_natCard a)
  have h2 : orderOf (σ a) ∣ 2 ^ k := by
    have h := orderOf_dvd_natCard (σ a)
    rw [IsCyclic.card_mulAut, hk] at h
    refine h.trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk0]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hodd : Odd (orderOf (σ a)) := Odd.of_dvd_nat hA h1
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two.pow_of_ne_zero hjpos.ne')

end QD32Facts

end CFSG.RankThree.PartOne
