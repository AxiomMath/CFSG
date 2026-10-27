module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27DGroupIndexParity
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `t ∈ O²(M)` trichotomy branch for Lemma 2.7

In `Lemma27Hypothesis`, the third branch of the Sylow-intersection
alternative is `c.t ∈ O²(M)`.  This leaf module closes that branch: apply
the GW Lemma 2.1 trichotomy to `M` (a proper subgroup of a minimal
counterexample, hence a `D`-group with dihedral Sylow `2`-subgroups).  The
index-four case contradicts `t ∈ O²(M)` through the normal `2`-complement
odd core; the other two cases use the D-group index-parity fact and the
index-two machinery in `Lemma27IndexTwo`.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-- In the `t ∈ O²(M)` branch, every normal subgroup of `M` of order
divisible by four contains the distinguished involution `t`. -/
public theorem t_mem_N_map_of_mem_twoResidualOf_of_DGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hMproper : M ≠ ⊤)
    (hSylow : ∀ P : Sylow 2 (↥M), ¬ IsCyclic P)
    (hO2 : c.t ∈ twoResidualOf M)
    {N : Subgroup (↥M)} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    c.t ∈ N.map M.subtype := by
  classical
  have htM : c.t ∈ M := pResidualOf_le M 2 hO2
  have hDM : IsDGroup (↥M) := properSubgroups_areDGroups hmin M hMproper
  have hDihedral : HasDihedralSylowTwo (↥M) := by
    intro P
    rcases hDM with ⟨hS, _⟩ | ⟨hS, _⟩ | ⟨hS, _K, _hKp, _L, _hL, _hLidx, _hLmodel⟩
    · rcases hS P with hcyc | hdi
      · exact False.elim (hSylow P hcyc)
      · exact hdi
    · rcases hS P with hcyc | hdi
      · exact False.elim (hSylow P hcyc)
      · exact hdi
    · rcases hS P with hcyc | hdi
      · exact False.elim (hSylow P hcyc)
      · exact hdi
  rcases gw_lemma_2_1 hDihedral with hcase1 | hcase2 | hcase3
  · rcases hcase1 with ⟨hno2, _hfusion, _hC'⟩
    have hnotQ : ¬ IsPGroup 2 ((↥M) ⧸ pPrimeCore 2 (↥M)) := by
      intro hQ
      have htOdd : c.t ∈ oddCoreOf M :=
        (twoResidualOf_le_oddCoreOf_of_isPGroup_quotient M hQ) hO2
      exact not_mem_odd_order_subgroup_of_involution c.t_involution
        (odd_card_oddCoreOf M) htOdd
    have hNidx : ¬ 4 ∣ N.index :=
      index_not_dvd_four_of_normal_card_div_four_of_isDGroup_not_twoQuotient
        (A := ↥M) hDM hnotQ hN h4
    by_cases hodd : Odd N.index
    · exact t_mem_N_map_of_index_odd M htM c.t_involution hN hodd
    · have h2 : 2 ∣ N.index := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
      obtain ⟨M₂, hM₂N, hM₂idx, _hNleM₂⟩ :=
        exists_normal_index_two_containing_of_index_eq_two_mul_odd
          (A := ↥M) (N := N) hN h2 hNidx
      exact False.elim (hno2 ⟨M₂, hM₂N, hM₂idx⟩)
  · rcases hcase2 with ⟨_hN2, _hno4, _hrest2⟩
    have hnotQ : ¬ IsPGroup 2 ((↥M) ⧸ pPrimeCore 2 (↥M)) := by
      intro hQ
      have htOdd : c.t ∈ oddCoreOf M :=
        (twoResidualOf_le_oddCoreOf_of_isPGroup_quotient M hQ) hO2
      exact not_mem_odd_order_subgroup_of_involution c.t_involution
        (odd_card_oddCoreOf M) htOdd
    have hNidx : ¬ 4 ∣ N.index :=
      index_not_dvd_four_of_normal_card_div_four_of_isDGroup_not_twoQuotient
        (A := ↥M) hDM hnotQ hN h4
    exact t_mem_N_of_mem_twoResidualOf_of_index_two_part M htM c.t_involution
      hO2 hN h4 hNidx
  · rcases hcase3 with ⟨_hN4, hNPC⟩
    have htOdd : c.t ∈ oddCoreOf M :=
      (twoResidualOf_le_oddCoreOf_of_normalPComplement M hNPC) hO2
    exact False.elim (not_mem_odd_order_subgroup_of_involution c.t_involution
      (odd_card_oddCoreOf M) htOdd)

end

end CFSG.GorensteinWalter
