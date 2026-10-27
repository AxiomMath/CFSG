module

public import CFSG.RankThree.PartTwo.Sec18.Item183KE
public import CFSG.RankThree.PartTwo.Sec18.Item184a
import CFSG.RankThree.PartTwo.Sec18.Item181b

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem item183One_of_parts (hNM : Item183NM) (hET : Item183ET) : Item183One := by
  intro G _ _ A M hs c hcA hc1 K hK hiso hinner
  have h : Hyp183 G A M c K := ⟨hs, hcA, hc1, hK, hiso, hinner⟩
  by_cases hC : ∃ x : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers x : Set G)
  · obtain ⟨E, hD⟩ := Item183K.exists_E_of_cyclic h hC
    refine ⟨E, isE27_of_mem_partTwoE hD.E_mem_partTwoE, hD.E_le, hD.inf_noncyclic,
      hD.sectionCentralizer_noncyclic, ?_⟩
    obtain ⟨-, N, hN⟩ := mem_partTwoT_iff.mp (hET G A M c K E hD)
    rw [← hNM G A M c K E hD N hN]
    exact fun x hx => hN.2 hx
  · exact ⟨A, h.isE27, le_inf le_sup_left Subgroup.le_normalizer,
      Item183K.inf_noncyclic_of_not_cyclic h hC, hC, fun x hx => hs.mem_scriptM.2 hx⟩

theorem item183K_of_item183One (h183 : Item183One) : Item183K :=
  fun _ _ _ _ _ hs _ hcA hc1 _ hK hiso hinner => le_of_item183One h183 hs hcA hc1 hK hiso hinner

theorem rank3II_18_4_1_of_item183K
    (h1812 : Item181_2)
    (h183 : Item183K) (hLc : Claim184LcLe) : Item184_1 := by
  refine rank3II_18_4_1_of_not_SL h1812 fun G _ _ A M h H hH hSL => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcA, hc1, K, hK, hKiso, hinner, hLcK, hLLc⟩ := hLc G A M h H hH hSL
  have hKM : K ≤ M := h183 G A M h c hcA hc1 K hK hKiso hinner
  have hAH := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hRM : CFSG.Open.pCoreOf 2 H ≤ M :=
    le_of_le_normalizer_of_isPGroup_two h (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (hAH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  exact perfectResidual_not_le_of_mem_scriptH h hH
    (hLLc.trans (sup_le (hLcK.trans hKM) hRM))

end CFSG.RankThree.PartTwo.Sec18
