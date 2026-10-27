module

public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.RankThree.PartOne.KSP6

open CFSG.RankThree.PartOne.OutStructure CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank

section Index

variable {X : Type} [Group X]

theorem zpow_eq_one_or_self {y : MulAut X} (hy : y ^ 2 = 1) (m : ℤ) : y ^ m = 1 ∨ y ^ m = y := by
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hy, one_zpow]
  · right
    rw [zpow_add, zpow_one, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hy,
      one_zpow, one_mul]

theorem relIndex_inf_inner_le_two (h : OutPChain 2 X) (F : Subgroup (MulAut X))
    (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hFs : ∀ x ∈ F, x ^ 2 = 1) :
    (F ⊓ Inn X).relIndex F ≤ 2 := by
  by_cases hF : F ≤ Inn X
  · rw [inf_eq_left.mpr hF, Subgroup.relIndex_self]
    norm_num
  · obtain ⟨x, hxF, hxI⟩ := Set.not_subset.1 hF
    have hx2 : x ^ 2 = 1 := hFs x hxF
    have key : ∀ y ∈ F, y ∈ Inn X ∨ x * y ∈ Inn X := by
      intro y hy
      have hy2 : y ^ 2 = 1 := hFs y hy
      have hcomm : x * y = y * x := hFc x hxF y hy
      have hxI2 : x ^ (2 ^ 1) ∈ Inn X := by
        rw [pow_one, hx2]
        exact one_mem _
      have hyI2 : y ^ (2 ^ 1) ∈ Inn X := by
        rw [pow_one, hy2]
        exact one_mem _
      rcases h.comparable hcomm hxI2 hyI2 with ⟨m, hm⟩ | ⟨m, hm⟩
      · rcases zpow_eq_one_or_self hy2 m with h1 | h1
        · rw [h1, mul_one] at hm
          exact absurd hm hxI
        · rw [h1] at hm
          exact Or.inr hm
      · rcases zpow_eq_one_or_self hx2 m with h1 | h1
        · rw [h1, mul_one] at hm
          exact Or.inl hm
        · rw [h1, ← hcomm] at hm
          exact Or.inr hm
    unfold Subgroup.relIndex
    have hmem : ∀ c : ↥F, c ∈ (F ⊓ Inn X).subgroupOf F ↔ (c : MulAut X) ∈ Inn X := fun c => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
    have h2 : ((F ⊓ Inn X).subgroupOf F).index = 2 := by
      rw [Subgroup.index_eq_two_iff']
      refine ⟨⟨x, hxF⟩, fun b => ?_⟩
      rw [hmem, hmem]
      show Xor (x * (b : MulAut X) ∈ Inn X) ((b : MulAut X) ∈ Inn X)
      by_cases hbI : (b : MulAut X) ∈ Inn X
      · have : x * (b : MulAut X) ∉ Inn X := fun hh => hxI (by
          have := (Inn X).mul_mem hh ((Inn X).inv_mem hbI)
          simpa using this)
        exact Or.inr ⟨hbI, this⟩
      · rcases key b b.2 with h1 | h1
        · exact absurd h1 hbI
        · exact Or.inl ⟨h1, hbI⟩
    exact h2.le

end Index

section Sp

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem outPChain_two_statedSp : OutPChain 2 (StatedSp 3 K) := by
  have hbij : Function.Bijective (proj 3 K) := UnitaryHigher.proj_bijective_of_charTwo
  let e : StatedSp 3 K ≃* StatedProj (StatedSp 3 K) := MulEquiv.ofBijective (proj 3 K) hbij
  exact OutPChain.of_mulEquiv e (outPNice_StatedSp (K := K) (r := 3) (by norm_num)
    Nat.prime_two).toChain

end Sp

end CFSG.RankThree.PartOne.KSP6
