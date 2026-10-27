module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofKDThree
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace KS1624CycProof

variable {X : Type} [Group X] [Finite X]

theorem mem_of_normal (hO3 : CFSG.pPrimeCore 3 X = ⊥)
    (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x : X} (hx : orderOf x = 3)
    {N : Subgroup X} (hN : N.Normal) (hN1 : N ≠ ⊥) : x ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card N := by
    by_contra h3
    have hle : N ≤ CFSG.pPrimeCore 3 X :=
      CFSG.le_pPrimeCore_of_normal_coprime hN
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    rw [hO3, le_bot_iff] at hle
    exact hN1 hle
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hy' : orderOf (y : X) = 3 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨t, ht⟩ := Proof1624KD.exists_mem_zpowers_conj hcyc hy' hx
  have hty : t * (y : X) * t⁻¹ ∈ N := hN.conj_mem _ y.2 t
  exact (Subgroup.zpowers_le.mpr hty) ht

theorem isSimpleGroup_of (hO3 : CFSG.pPrimeCore 3 X = ⊥)
    (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x : X} (hx : orderOf x = 3)
    (hnc : Subgroup.normalClosure ({x} : Set X) = ⊤) : IsSimpleGroup X := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have : Nontrivial X := ⟨⟨x, 1, hx1⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  · right
    have hxN := mem_of_normal hO3 hcyc hx hN hN1
    rw [eq_top_iff, ← hnc]
    exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hxN)

end KS1624CycProof

end CFSG.RankThree.PartTwo.Sec16
