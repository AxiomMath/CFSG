module

public import CFSG.RankThree.GF2n.Stroth80.Sec714NotTwelve
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Open

theorem commutator_self_of_commutator_eq_top {A : Type} [Group A] (S : Subgroup A)
    (h : commutator ↥S = ⊤) : ⁅S, S⁆ = S := by
  have hmapS : Subgroup.map S.subtype (⊤ : Subgroup ↥S) = S := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h' : ⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆ = ⊤ := h
  have h2 := congrArg (Subgroup.map S.subtype) h'
  rw [Subgroup.map_commutator, hmapS] at h2
  exact h2

theorem statedOmega_quadPlus_perfect {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    ⁅StatedOmega (StatedQuadPlus n K), StatedOmega (StatedQuadPlus n K)⁆ =
      StatedOmega (StatedQuadPlus n K) := by
  obtain ⟨hnd, T, hT, hTQ⟩ := regular_quadPlus (K := K) (n := n) hn
  have hEp := commutator_self_of_commutator_eq_top (elementaryGroup (quadPlus n K))
    (commutator_elementaryGroup_eq_top' hnd hT.ge hTQ)
  rw [statedOmega_quadPlus_eq_map hn, ← Subgroup.map_commutator, hEp]


theorem statedOmegaPlusFourPerfect_holds : StatedOmegaPlusFourPerfectStatement := by
  intro K _ _ _
  exact statedOmega_quadPlus_perfect (n := 4) (by norm_num)

end CFSG.RankThree.GF2n.Stroth80
