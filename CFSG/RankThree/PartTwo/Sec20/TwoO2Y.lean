module

public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem TwoTheta.pCoreOf_le_of_hyp191 (h191 : Hyp191 G) {A M H Y T : Subgroup G}
    (hA : IsE27 A) (hM : M ∈ scriptM (gamma 2 A : Set G)) (hAH : A ≤ H)
    (hH : CFSG.Open.pCoreOf 2 H ≠ ⊥) (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hTH : T ≤ H)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : CFSG.Open.pCoreOf 2 Y ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHO : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hOH : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH) hHO hO2
  have hOM : CFSG.Open.pCoreOf 2 Y ≤ M := by
    refine hOH.trans ?_
    rw [← h191 A M H hA hM hAH hH]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hsup : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hO2 (hT.isPGroup) (hTH.trans hHO)
  have heq := hT.eq_of_le le_sup_right (sup_le hOM hT.le) hsup
  exact heq ▸ le_sup_left

theorem TwoTheta.mem_scriptM_gamma_map_conj {A M : Subgroup G}
    (hM : M ∈ scriptM (gamma 2 A : Set G)) {x : G} (hx : x ∈ M) :
    M ∈ scriptM (gamma 2 (A.map (MulAut.conj x).toMonoidHom) : Set G) := by
  have h := map_conj_mem_scriptM_gamma hM x
  rwa [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)] at h

end CFSG.RankThree.PartTwo.Sec20
