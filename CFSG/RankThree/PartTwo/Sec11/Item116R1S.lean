module

public import CFSG.RankThree.PartTwo.Sec11.Item116Holes

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (fusionIsSylowIn)
open scoped commutatorElement

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem false_of_R1_of_mem_partTwoS (h45 : Sec4.Item4_5) (hP2b : Item116P2b)
    (hP2c : Item116P2c) (h : ResidueConfig G A c L a R Y d) (hS : A ∈ partTwoS G)
    (hR1 : ResidueR1 G A c a d) : False := by
  obtain ⟨-, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  have hs := h.toSec11StdOfCtx (Or.inr hS)
  have hAe := h.mem_partTwoF.1
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_isPGroup 3 A hAe
  have hM3 := not_three_dvd_card_inSubgroup_theta
    (Subgroup.centralizer ({a} : Set G))
  have hAM : A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.commutative_plane_le_element_centralizer A hAe.1 a
      h.a_mem).trans (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _))
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := fun g => ⟨0, Subsingleton.elim _ _⟩
  have hAbot : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨S, hSsyl, -, hAS⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_two hA3 hM3 hAM bot_le hbot2 hAbot
  have hSA1 : ⁅S, A⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro s hs' x hx
    have h1 : x * s⁻¹ * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS hx) s⁻¹).mp (S.inv_mem hs')
    have : ⁅s, x⁆ = s * (x * s⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact S.mul_mem hs' h1
  have hSA2 : ⁅S, A⁆ ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)), A⁆ :=
    Subgroup.commutator_mono hSsyl.1 le_rfl
  have hodd : Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)), A⁆ : Subgroup G)) := hS.2.1 a h.a_mem h.a_ne_one
  have hSP : IsPGroup 2 S := hSsyl.2.1
  have h2 : IsPGroup 2 (⁅S, A⁆ : Subgroup G) := hSP.to_le hSA1
  have hoddSA : Odd (Nat.card (⁅S, A⁆ : Subgroup G)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hSA2)
  have hSAbot : ⁅S, A⁆ = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hoddSA
      exact (Nat.not_even_iff_odd.mpr hoddSA) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact (Subgroup.card_eq_one).mp hk
  exact not_Eii hP2b hP2c h45 hs h.inf_eq_zpowers h.normalizer_le h.isIrreducibleOn
    h.isSylowOf_top h.not_mem_zpowers hD8 hnW hnc hnd hna hSsyl hSAbot

end Certified

end CFSG.RankThree.PartTwo.Sec11
