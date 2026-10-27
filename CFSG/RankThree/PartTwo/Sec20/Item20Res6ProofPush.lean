module

import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAutQ8
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec20.OneTools
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

namespace Res6

variable {G : Type} [Group G] [Finite G]

section KT

variable {K T : Subgroup G}

theorem inf_pCoreOf_sup_eq {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ CFSG.Open.pCoreOf 2 (K ⊔ T) = CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun k hk => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hk)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T) (Subgroup.mem_sup_left hk))
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      (hXK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

omit [Finite G] in
theorem exists_pow_mem_of_sup (hT2 : IsPGroup 2 T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ K ⊔ T) : ∃ a : ℕ, x ^ 2 ^ a ∈ K := by
  have hx' : x ∈ ((T ⊔ K : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T K hTK] at hx'
  obtain ⟨t, ht, k, hk, rfl⟩ := hx'
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  obtain ⟨k', hk', he⟩ := exists_pow_eq_mul (hTK ht) hk (2 ^ a)
  refine ⟨a, ?_⟩
  rw [he, ha', one_mul]
  exact hk'

end KT

end Res6

end CFSG.RankThree.PartTwo.Sec20
