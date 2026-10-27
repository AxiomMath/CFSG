module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec14.Item148Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1418Res2

variable {G : Type} [Group G] [Finite G]

theorem transOn_normalizer_of_fail {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : Fail1411 A (lB A)) {D : Subgroup G} (hD : D ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    (hD1 : D ≠ ⊥) : TransOn A (lB A) (xA A) (Subgroup.normalizer (D : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (D : Set G) with hN
  set Y := delta A (lB A) N with hY
  have hYN : Y ≤ N := delta_le N
  have hYΔ : Y = delta A (lB A) Y := (delta_delta N).symm
  have hYne : Y ≠ ⊤ := fun htop => normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hD1
    (isPGroup_of_mem_scriptQPi Nat.prime_two hD) (top_le_iff.mp (htop ▸ hYN))
  have hYsc : Y ∈ scriptY A := ⟨hYne, le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩
  have htrans : TransOn A (lB A) (xA A) Y := by
    by_cases hres : inSubgroup perfectResidual Y = ⊥
    · refine transOn_of_isSolvable_std h h146 hbot hYΔ hYsc ?_
      have h0 : perfectResidual ↥Y = ⊥ := by
        rw [inSubgroup] at hres
        exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hres
      exact (perfect_residual_characterization (G := ↥Y)).2.2.2.2.2.mp h0
    · refine hfail.2 Y hYΔ hYsc ?_ hres
      have hDY : D ≤ Y := le_delta hD.1.1 Subgroup.le_normalizer
      have hDO : D ≤ CFSG.Open.pCoreOf 2 Y :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDY hYN
          (isPGroup_of_mem_scriptQPi Nat.prime_two hD)
      intro hO
      rw [hO] at hDO
      exact hD1 (le_bot_iff.mp hDO)
  exact transOn_of_delta htrans

end Proof1418Res2

open Proof1418Res2

theorem step1411WGammaR_of (h : Claim1411LocalR) : Step1411WGammaR := by
  intro G _ _ A c L hR _ a ha
  have hS := hR.toSec14Std
  have haA : a ∈ A := (zpowers_mem_omegaA_iff.mp ha.1).1
  have ha1 : a ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp ha.1).2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    norm_num at h3
  refine (h G A c L hR).1 _ ⟨centralizer_singleton_ne_top hS.isSimpleGroup hS.nonabelian ha1, ?_⟩
  refine le_trans (fun x hx => ?_) Subgroup.le_normalizer
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hS.toSec13Data.commute hx haA

end CFSG.RankThree.PartTwo.Sec14
