module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan155RKFact
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigTools
import CFSG.RankThree.PartTwo.Sec15.Ronan155RAut
import CFSG.RankThree.PartTwo.Sec15.Ronan155RRoute
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec15.Ronan155RDiamond
import CFSG.GroupTheory.PCore.Transport
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofFive
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofNotHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Cases


theorem step155CasesTwoWBig_of_nhj {A : Subgroup G} {c : G} {L : Subgroup G}
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hres : Step155CasesTwoNHJWBig A c L) : Step155CasesTwoWBig A c L := by
  intro h X K Y M T hC hXb hmax hab J hJM hJ0 hXJ hcl
  by_cases hHJ : AllPointsHJ A
  · exact fun ⟨htwo, _⟩ => Proof155w3.not_case154Two_of_allPointsHJ h h148 hbot hHJ hJ0.1 htwo
  · exact hres h hHJ X K Y M T hC hXb hmax hab J hJM hJ0 hXJ hcl

end Cases

theorem step155CasesNWBig_of {A : Subgroup G} {c : G} {L : Subgroup G} (h146 : Item146 A (lB A))
    (hYQ : Step155YQ0W A c L) (hPJQ : Step155PJQ0W A c L) (htwo : Step155CasesTwoWBig A c L)
    (hb : Step155CasesBW A c L) : Step155CasesNWBig A c L := by
  intro h X K Y M T hC hXb hmax hab J hJM hJ0 hXJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Late.IsE27 A := h.isE27
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
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
  have hR𝓠 : R ∈ scriptQ A (lB A) := hYQ h X K Y M T hC hmax hab
  have hRT : R ≤ T := by
    have hRmem : R ∈ scriptQPi A (lB A) Y (piOf 2) :=
      ⟨⟨hR𝓠, CFSG.LieType.BorelTits.pCoreOf_le 2 Y⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)⟩
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
        (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)⟩
    have hPQ := sup_mem_scriptQPi_of_item146 hA h146 hP.prop hQmem
      (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    exact le_sup_right.trans (hP.2 hPQ le_sup_left)
  refine ⟨P, hP, hTP, hQP, ?_, fun hRJ => Proof155w2.le_pCoreOf_sup_of_commutator_le hP2 hPJn
    hRP hRJ, htwo h X K Y M T hC hXb hmax hab J hJM hJ0 hXJ,
    hb h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP hRP hQP⟩
  exact (hRP.trans le_sup_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem step155CasesTwoNHJWBigR_of_diamond (hY4 : Y4LThreePiNHJR) (hd : DiamondBigR) :
    Step155CasesTwoNHJWBigR := by
  intro G _ _ A c L hR hS hNHJ X K Y M T hC hXb hmax hab J hJM hJ0 hXJ hcl
  rintro ⟨⟨n, m, hn, hm, ⟨φ⟩, hXε, -⟩, -⟩
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hpi : Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n :=
    hY4 G A c L hR hNHJ X hX4 n hn hXε
  have hK : K = X ⊔ CFSG.Open.pCoreOf 2 K := by
    rcases hC.hyp with hom | hK
    · rcases hom with ⟨hno, -⟩ | hcl'
      · exact absurd ⟨n, hn, hpi⟩ hno
      · exact absurd hcl' hcl
    · exact hK
  exact hd G A c L hR hNHJ X K Y M T hC hXb hmax hab hcl hK J hJM hJ0 hXJ n m hn hm ⟨φ⟩ hXε

theorem exists_p_of_ctx155_big {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hYQ : Step155YQ0W A c L)
    (hPJQ : Step155PJQ0W A c L) {X K Y M T J : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hXb : Big152 X) (hmax : MaxT155 A X K T) (hab : Above155w A X) (hclaim : Claim155 A K Y)
    (hJM : J ∈ thetaComponentsIn M) (hJ0 : J ∈ scriptY0 A (lB A)) (hXJ : X ≤ J) :
    ∃ P : Subgroup G, P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2) ∧
      T ≤ P ∧ CFSG.Open.pCoreOf 2 Y ≤ P ∧ CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ P ∧
      CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ CFSG.Open.pCoreOf 2 Y ∧
      CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 (P ⊔ J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Late.IsE27 A := h.isE27
  have hKb : Big152 K := big152_k hC hXb
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
    refine le_normalizer_of_isPGroup_of_le_normalizer_big h h152 h153 hC.mem_k hKb
      (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hC.le_k
      (hQ2.to_le inf_le_left) inf_le_right ?_
    exact Late.le_normalizer_inf hXQ
      ((hC.le_k.trans (Subgroup.le_normalizer.trans
        (normalizer_le_n155w_big h153 hC.mem_k hKb))).trans Subgroup.le_normalizer)
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

open scoped Ronan155R in
theorem diamondCharBigR_of_kf (hY4 : Y4LThreePiNHJR) (h152 : Item152BigR)
    (h153 : Ronan153Big.Item153BigR) (hgrow : Step155GrowWR) (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (hYQ : Step155YQ0WR) (hPJQ : Step155PJQ0WR)
    (hkf : Ronan155R.KFSubL3) : DiamondCharBigR := by
  intro G _ _ A c L hR hNHJ X K Y M T hC hXb hmax hab hcl hK J hJM hJ0 hXJ n m hn hm hφ hXε
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hφ
  have hS : Sec14Std G A c L := hR.toSec14Std
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX4
  have hn2 : 2 ≤ n :=
    Ronan155R.two_le_of_isoLThreePi hX4.2.2.2 hn (hY4 G A c L hR hNHJ X hX4 n hn hXε)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hclaim : Claim155 A K Y := by
    by_cases hKR : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)
    · exact claim155_of_le_normalizer_big (h153 G A c L hR) hC.mem_k (big152_k hC hXb) hKR hAR
    · exact hgrow G A c L hR hS X K Y M T hC hmax hab hKR
  obtain ⟨P, -, -, -, -, hQR, hVQ⟩ := exists_p_of_ctx155_big hS (h152 G A c L hR)
    (h153 G A c L hR) (h1444 G A c L hS) (h146 G A c L hS) (hbot G A c L hS) (hYQ G A c L hR)
    (hPJQ G A c L hR) hC hXb hmax hab hclaim hJM hJ0 hXJ
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  set V := CFSG.Open.pCoreOf 2 J with hVdef
  have hVR : V ≤ R := hVQ.trans hQR
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hVJ : V ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hJV : J ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hXY : X ≤ Y := by
    rw [← hC.res]
    exact Sec14.oPrimeResidualOf_le_self 3 Y
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, -, -, hF⟩ := facts_of_mem_maximalTwoLocalsContaining hS hM'
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn (hYM.trans Subgroup.le_normalizer) hJM hXJ
      (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hYX
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := hRY.trans hYJ
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    hRJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hMchar : CFSG.QuasithinUnique.CharTwo M := inf_centralizer_le_pCoreOf_of_fitting hF
  have hJsn : (J.subgroupOf M).IsSubnormal := ((mem_thetaComponentsIn_iff.mp hJM).2).2.1
  have hCV : J ⊓ Subgroup.centralizer (V : Set G) ≤ V :=
    CFSG.QuasithinUnique.CharTwo.of_isSubnormal hMchar (le_of_mem_thetaComponentsIn hJM) hJsn
  have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
  have hVsub : V.subgroupOf J = CFSG.pCore 2 ↥J := CFSG.openPCoreOf_subgroupOf 2 J
  haveI : (V.subgroupOf J).Normal := hVsub ▸ inferInstance
  set φ' : ↥J ⧸ V.subgroupOf J ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m)) :=
    (QuotientGroup.quotientMulEquivOfEq hVsub).trans φ with hφ'
  haveI hsS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hsJ : IsSimpleGroup (↥J ⧸ V.subgroupOf J) := φ'.isSimpleGroup
  have hdich : ∀ W : Subgroup G, W ≤ J → J ≤ Subgroup.normalizer (W : Set G) →
      W ≤ V ∨ W = J := fun W hWJ hJW =>
    Ronan155R.le_or_eq_of_normal hJp hsJ hVJ hV2 hWJ hJW
  have hXV : X ⊓ V ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Ronan155R.le_normalizer_inf' Subgroup.le_normalizer (hXJ.trans hJV))
      (hV2.to_le inf_le_right)
  set g := Ronan155R.secHom hXJ φ' with hg
  have hHp : ⁅g.range, g.range⁆ = g.range := Ronan155R.commutator_range_secHom hXJ φ' hXp
  have hNH : (CFSG.pCore 2 ↥X).map g ≤ g.range := Subgroup.map_le_range _ _
  have hN2 : IsPGroup 2 ((CFSG.pCore 2 ↥X).map g) := CFSG.pCore_isPGroup.map g
  have hHε : IsLThreeEpsAt (↥g.range ⧸ ((CFSG.pCore 2 ↥X).map g).subgroupOf g.range) 2 n := by
    obtain ⟨e⟩ := Ronan155R.nonempty_mulEquiv_secHom hXJ φ' hXV
    rcases hXε with ⟨⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨e.symm.trans ψ⟩
    · exact Or.inr ⟨hq, ⟨e.symm.trans ψ⟩⟩
  obtain ⟨hi, -, hiii, hiv⟩ := hkf n m hn2 hm g.range ((CFSG.pCore 2 ↥X).map g) hHp hNH hN2 hHε
  have hNbot : (CFSG.pCore 2 ↥X).map g = ⊥ :=
    hi _ hN2 ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp inferInstance)
  have hO2V : CFSG.Open.pCoreOf 2 X ≤ V := by
    intro x hx
    have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hx
    have hx' : (⟨x, hxX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (CFSG.mem_openPCoreOf_iff _).mp hx
    have h1 : g ⟨x, hxX⟩ ∈ (CFSG.pCore 2 ↥X).map g := Subgroup.mem_map_of_mem g hx'
    rw [hNbot, Subgroup.mem_bot] at h1
    exact (Ronan155R.mem_ker_secHom hXJ φ' ⟨x, hxX⟩).mp h1
  have hRXO : X ⊓ R ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Ronan155R.le_normalizer_inf' Subgroup.le_normalizer hXR) (hR2.to_le inf_le_right)
  have hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ V := by
    intro r hr x hx
    have h1 : r * x * r⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYX (hRY hr)) x).mp hx) (X.inv_mem hx)
    have h2 : r * x * r⁻¹ * x⁻¹ ∈ R := by
      have e : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
      rw [e]
      exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hXR hx) _).mp (R.inv_mem hr))
    exact hO2V (hRXO (Subgroup.mem_inf.mpr ⟨h1, h2⟩))
  have hH : ∀ h ∈ g.range, ∃ x : ↥J, (x : G) ∈ X ∧ φ' (x : ↥J ⧸ V.subgroupOf J) = h :=
    fun h hh => Ronan155R.exists_of_mem_range_secHom hXJ φ' hh
  exact Ronan155R.exists_char_of_secCent hR2 hR1 hVR hJV hRJ hRV hCV hdich
    (Ronan155R.h3_of_iii φ' hJV hRJ hRV hRX hH hiii)
    (Ronan155R.h4_of_iv φ' hJV hRJ hRV hRX hH hiv)

theorem diamondBigR_of_char (h152 : Item152BigR) (h153 : Ronan153Big.Item153BigR)
    (hgrow : Step155GrowWR) (hc : DiamondCharBigR) : DiamondBigR := by
  intro G _ _ A c L hR hNHJ X K Y M T hC hXb hmax hab hcl hK J hJM hJ0 hXJ n m hn hm hφ hXε
  have hS : Sec14Std G A c L := hR.toSec14Std
  have hKb : Big152 K := big152_k hC hXb
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hclaim : Claim155 A K Y := by
    by_cases hKR : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)
    · exact claim155_of_le_normalizer_big (h153 G A c L hR) hC.mem_k hKb hKR hAR
    · exact hgrow G A c L hR hS X K Y M T hC hmax hab hKR
  obtain ⟨C, hC1, hCR, hCc, hJC⟩ :=
    hc G A c L hR hNHJ X K Y M T hC hXb hmax hab hcl hK J hJM hJ0 hXJ n m hn hm hφ hXε
  have hJΔ : J = delta A (lB A) J := hJ0.1.2.2.1
  have hJN : J ≤ n155 A K :=
    calc J = delta A (lB A) J := hJΔ
      _ ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) := delta_mono hJC
      _ ≤ n155 A K := hclaim C hC1 hCR hCc
  have hJK : J ≤ K := le_of_le_n155'_big hS (h152 G A c L hR) (h153 G A c L hR) hC.mem_k hKb
    hX4 hJ0 hXJ hC.le_k hJN
  exact Ronan155R.not_le_of_diamond hXJ hJK hK hn hm hφ hXε

theorem step155CasesTwoNHJWBigR_of_route (hY4 : Y4LThreePiNHJR) (h152 : Item152BigR)
    (h153 : Ronan153Big.Item153BigR) (hgrow : Step155GrowWR) (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (hYQ : Step155YQ0WR) (hPJQ : Step155PJQ0WR) :
    Step155CasesTwoNHJWBigR :=
  step155CasesTwoNHJWBigR_of_diamond hY4 (diamondBigR_of_char h152 h153 hgrow
    (diamondCharBigR_of_kf hY4 h152 h153 hgrow h146 h1444 hbot hYQ hPJQ Ronan155R.kFSubL3))

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
