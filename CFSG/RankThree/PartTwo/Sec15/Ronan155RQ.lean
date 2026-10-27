module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155RDiamond
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofCases
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofRQK
import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec15.Item153Claims
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item155wProof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem exists_p_of_ctx155 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hYQ : Step155YQ0W A c L) (hPJQ : Step155PJQ0W A c L)
    {X K Y M T J : Subgroup G} (hC : Ctx155 A X K Y M T) (hmax : MaxT155 A X K T)
    (hab : Above155w A X) (hclaim : Claim155 A K Y) (hJM : J ∈ thetaComponentsIn M)
    (hJ0 : J ∈ scriptY0 A (lB A)) (hXJ : X ≤ J) :
    ∃ P : Subgroup G, P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2) ∧
      T ≤ P ∧ CFSG.Open.pCoreOf 2 Y ≤ P ∧ CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ P ∧
      CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ CFSG.Open.pCoreOf 2 Y ∧
      CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 (P ⊔ J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Late.IsE27 A := h.isE27
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM'
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn (hYM.trans Subgroup.le_normalizer) hJM hXJ
      (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hYX
  have hJM' : J ≤ M := le_of_mem_thetaComponentsIn hJM
  have hTmem : T ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2) :=
    ⟨⟨hC.mem_t.prop.1.1, hC.mem_t.prop.1.2.trans (le_inf hYM hYJ)⟩, hC.mem_t.prop.2⟩
  obtain ⟨P, hTP, hP⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2))) hTmem
  have hP2 : IsPGroup 2 P := isPGroup_of_mem_scriptQPi Nat.prime_two hP.prop
  have hPJn : P ≤ Subgroup.normalizer (J : Set G) := hP.prop.1.2.trans inf_le_right
  set Q := CFSG.Open.pCoreOf 2 (P ⊔ J) with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hR𝓠 : R ∈ scriptQ A (lB A) := hYQ h X K Y M T hC hmax hab
  have hRT : R ≤ T := by
    have hRmem : R ∈ scriptQPi A (lB A) Y (piOf 2) :=
      ⟨⟨hR𝓠, CFSG.LieType.BorelTits.pCoreOf_le 2 Y⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr
        hR2⟩
    have hTR := sup_mem_scriptQPi_of_item146 hA h146 hC.mem_t.prop hRmem
      (hC.mem_t.prop.1.2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    exact le_sup_right.trans (hC.mem_t.2 hTR le_sup_left)
  have hRP : R ≤ P := hRT.trans hTP
  have hQ𝓠 : Q ∈ scriptQ A (lB A) := hPJQ h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP
  have hQP : Q ≤ P := by
    have hPJM : P ⊔ J ≤ M ⊓ Subgroup.normalizer (J : Set G) :=
      sup_le hP.prop.1.2 (le_inf hJM' Subgroup.le_normalizer)
    have hQmem : Q ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2) :=
      ⟨⟨hQ𝓠, (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hPJM⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr hQ2⟩
    have hPQ := sup_mem_scriptQPi_of_item146 hA h146 hP.prop hQmem
      (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    exact le_sup_right.trans (hP.2 hPQ le_sup_left)
  have hRQn : R ≤ Subgroup.normalizer (Q : Set G) :=
    (hRP.trans le_sup_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    (hXJ.trans le_sup_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQK : Q ⊓ n155 A K ≤ Subgroup.normalizer (K : Set G) := by
    refine Proof155w2.le_normalizer_of_isPGroup_of_le_normalizer h h152 h153 hC.mem_k
      (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hC.le_k
      (hQ2.to_le inf_le_left) inf_le_right ?_
    exact Late.le_normalizer_inf hXQ
      ((hC.le_k.trans (Subgroup.le_normalizer.trans (normalizer_le_n155w h153 hC.mem_k))).trans
        Subgroup.le_normalizer)
  have hRQN : Q ⊓ n155 A K ≤ R :=
    Proof155w.inf_n155_le_pCoreOf_w h h1444 h146 hbot hC hmax hab hJ0 hXJ hP.prop.1.1
      (hP.prop.1.2.trans inf_le_left) hTP hQP hRQn hQK
  have hRchar : (R.subgroupOf R).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.topCharacteristic
  have hQR : Q ≤ R := by
    have hQ𝓠' : Q ∈ scriptQ A (lB A) := hQ𝓠
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
      (le_normalizer_sup hP.prop.1.1.1.2.2 hJ0.1.1.2).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    have hNQ𝓠 : Q ⊓ Subgroup.normalizer (R : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hQ𝓠' inf_le_left
        (Late.le_normalizer_inf hAQ (hAR.trans (Sec6.normalizer_le_normalizer_normalizer R)))
    have hNQN : Q ⊓ Subgroup.normalizer (R : Set G) ≤ n155 A K :=
      (le_delta hNQ𝓠 inf_le_right).trans (hclaim R hR1 le_rfl hRchar)
    exact le_of_inf_normalizer_le155 hR2 hQ2 hRQn ((le_inf inf_le_left hNQN).trans hRQN)
  have hVQ : CFSG.Open.pCoreOf 2 J ≤ Q := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J)
    exact sup_le (hPJn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
  exact ⟨P, hP, hTP, hRP, hQP, hQR, hVQ⟩

end CFSG.RankThree.PartTwo.Sec15.Ronan155R
