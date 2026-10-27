module

import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T115
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T120
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidGrp
import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofPL
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.GH74.GLS.C3.Layer1.St1Iv251
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem inf_normalizer_le_pCoreOf_two {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hmax : MaxT155 A X K T)
    (hab : Above155w A X) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    (hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 K ⊓ Subgroup.normalizer (X : Set G) ≤ CFSG.Open.pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hVdef
  set D := V ⊓ Subgroup.normalizer (X : Set G) with hDdef
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX4.1.2
  have hK4 : K ∈ scriptY4 A (lB A) := hC.mem_k.prop.1
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hK4.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hYY : Y ≤ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    have hY := Sec14.le_normalizer_oPrimeResidualOf (p := 3) hYY
    rwa [hC.res] at hY
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) :=
    hC.norm_k.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hD2 : IsPGroup 2 ↥D :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K).to_le inf_le_left
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_inf hAV (hAX.trans (Sec6.normalizer_le_normalizer_normalizer X))
  have hDQ : D ∈ scriptQ A (lB A) := mem_scriptQ_of_le hV inf_le_left hAD
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_inf hYV (hYX.trans (Sec6.normalizer_le_normalizer_normalizer X))
  have hDK : D ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_left.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer)
  have hTD : T ⊔ D ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 h.isE27 h146 hC.mem_t.prop.1.1 hDQ (hC.mem_t.prop.1.2.trans hYD)
  have hU1 : CFSG.Open.pCoreOf 2 X ≠ ⊥ := (isCharacteristicP_x_and_pCoreOf_ne_bot h h149 hC hIX).2
  have hXU : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hU1)
  have hM'mem : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (Y ⊔ D) : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle (hXU ((sup_le hAX (sup_le hYX inf_le_right)) hx))⟩
  have hOX : pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)))
      ≤ Subgroup.normalizer (X : Set G) :=
    ((pPrimeCoreOf_two_host_le_centralizer h h146 h149 hC hE hRP hIX).trans
      (Subgroup.centralizer_le fun x hx => x_le_oPrimeResidualOf_delta hC hx)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnot : ¬ delta A (lB A) M' ≤ n155 A K := fun hle' => hE0N
    ((le_delta (pPrimeCoreOf_two_host_mem_scriptQ h h146 hC hE hRP)
      (hOX.trans (hXU.trans hle))).trans hle')
  exact Proof155w.le_pCoreOf_of_ctx155w h h1444 h146 hbot hC hmax hab hD2 hDQ hYD hDK hTD hM'mem
    hnot

theorem commutator_le_centralizer_of_le_centralizer {R A O : Subgroup G}
    (hRO : R ≤ Subgroup.normalizer (O : Set G)) (hOA : O ≤ Subgroup.centralizer (A : Set G)) :
    ⁅R, A⁆ ≤ Subgroup.centralizer (O : Set G) := by
  have hAO : ⁅A, O⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hOA)
  have hOA' : ⁅O, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hAO
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_)
  · rw [hAO, Subgroup.commutator_bot_left]
  · exact eq_bot_iff.mpr ((Subgroup.commutator_mono
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hRO) le_rfl).trans hOA'.le)

theorem le_centralizer_center_of_eq_sup {A : Subgroup G} (h153 : Item153Main A (lB A))
    {X K E : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hXK : X ≤ K)
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (h132 : CFSG.Open.pCoreOf 2 K ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) ≤
      Subgroup.normalizer (X : Set G))
    (hEX : E ≤ Subgroup.centralizer (X : Set G)) (hE : ¬ E ≤ n155 A K) :
    CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) ≤
        Subgroup.normalizer (X : Set G) ∧
      K ≤ Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :
          Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hVdef
  set U := CFSG.Open.pCoreOf 2 X with hUdef
  set Z := V ⊓ Subgroup.centralizer (V : Set G) with hZdef
  have hK4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  have hUV : U ≤ V := pCoreOf_le_pCoreOf_of_le_sup hXK hKX.le
  have hXV : X ⊓ V = U := inf_pCoreOf_eq_pCoreOf_of_le_sup hXK hKX.le
  have hKV : K ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hNZ : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_inf le_rfl fun g hg => CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer hg
  have hZX : Z ≤ Subgroup.normalizer (X : Set G) :=
    le_trans (le_inf inf_le_left ((inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV))).trans
        (Subgroup.centralizer_le_normalizer _))) h132
  set Q := U ⊓ Z with hQdef
  have hQ2 : IsPGroup 2 ↥Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X).to_le inf_le_left
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_inf (hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      ((hK4.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)).trans hNZ)
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      ((hXK.trans hKV).trans hNZ)
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) :=
    ((Subgroup.le_centralizer_iff.mp inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := hKX.le.trans (sup_le hXQ hVQ)
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    (hEX.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X))))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ1 : Q = ⊥ := eq_bot_of_not_le_n155 h153 hK hQ2 hAQ hKQ hEQ hE
  have hc1 : ⁅X, Z⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hZX
  have hc2 : ⁅X, Z⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((hXK.trans hKV).trans hNZ)
  have hc : ⁅X, Z⁆ ≤ Q := by
    refine le_inf ?_ hc2
    rw [← hXV]
    exact le_inf hc1 (hc2.trans inf_le_left)
  have hXC : X ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (eq_bot_iff.mpr (hc.trans hQ1.le))
  exact ⟨hZX, hKX.le.trans (sup_le hXC (Subgroup.le_centralizer_iff.mp inf_le_right))⟩

theorem le_centralizer_center_of_commutator {A : Subgroup G} (h153 : Item153Main A (lB A))
    {K R E : Subgroup G} (hK : K ∈ scriptY0Star A (lB A))
    (hKZ : K ≤ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :
        Subgroup G) : Set G))
    (hZR : CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) ≤ R)
    (hRA : ⁅R, A⁆ ≤ Subgroup.centralizer (E : Set G)) (hE : ¬ E ≤ n155 A K) :
    A ≤ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :
        Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hVdef
  set Z := V ⊓ Subgroup.centralizer (V : Set G) with hZdef
  have hK4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hK4.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_inf hAV fun a ha => CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer
      (hAV ha)
  set Q := ⁅Z, A⁆ with hQdef
  have hQZ : Q ≤ Z := Subgroup.le_normalizer_iff_commutator_le_left.mp hAZ
  have hQ2 : IsPGroup 2 ↥Q :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K).to_le (hQZ.trans inf_le_left)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    Proof1418Res3.le_normalizer_commutator hAZ Subgroup.le_normalizer
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    (hKZ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQZ))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff.mp ((Subgroup.commutator_mono hZR le_rfl).trans hRA)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ1 : Q = ⊥ := eq_bot_of_not_le_n155 h153 hK hQ2 hAQ hKQ hEQ hE
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQ1)

theorem center_pCoreOf_two_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hmax : MaxT155 A X K T)
    (hab : Above155w A X) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    (hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) ≤
        CFSG.Open.pCoreOf 2 Y ∧
      A ≤ Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :
          Subgroup G) : Set G) ∧
      K ≤ Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :
          Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  set H := delta A (lB A) (R ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  set O := pPrimeCoreOf 2 H with hOdef
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hOX : O ≤ Subgroup.centralizer (X : Set G) :=
    (pPrimeCoreOf_two_host_le_centralizer h h146 h149 hC hE hRP hIX).trans
      (Subgroup.centralizer_le fun x hx => x_le_oPrimeResidualOf_delta hC hx)
  obtain ⟨hZX, hKZ⟩ := le_centralizer_center_of_eq_sup h153 hC.mem_k hC.le_k hKX hX4.1.2
    (inf_normalizer_pCoreOf_le_normalizer h h146 h149 hC hab hE hRP hIX hKX hE0N hV) hOX hE0N
  have hZR : CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) ≤ R :=
    (le_inf inf_le_left hZX).trans
      (inf_normalizer_le_pCoreOf_two h h1444 h146 h149 hbot hC hmax hab hE hRP hIX hE0N hV)
  obtain ⟨-, hRH, -, -⟩ := Sylow155B1.delta_host_facts h h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hRA : ⁅R, A⁆ ≤ Subgroup.centralizer (O : Set G) :=
    commutator_le_centralizer_of_le_centralizer (hRH.trans (le_normalizer_pPrimeCoreOf 2 H))
      ((pPrimeCoreOf_two_le_layerOddPreimage H).trans hEA)
  exact ⟨hZR, le_centralizer_center_of_commutator h153 hC.mem_k hKZ hZR hRA hE0N, hKZ⟩

theorem mem_pCoreOf_two_of_mem_center {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hmax : MaxT155 A X K T)
    (hab : Above155w A X) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    (hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A)) {z : G}
    (hzV : z ∈ CFSG.Open.pCoreOf 2 K)
    (hzC : z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G)) :
    z ∈ CFSG.Open.pCoreOf 2 Y ∧ A ≤ Subgroup.centralizer ({z} : Set G) ∧
      K ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨hZR, hAZ, hKZ⟩ := center_pCoreOf_two_le h h1444 h146 h149 h153 hbot hC hmax hab hE hRP
    hIX hEA hKX hE0N hV
  have hz : z ∈ CFSG.Open.pCoreOf 2 K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    ⟨hzV, hzC⟩
  have hsub := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (SetLike.mem_coe.mpr hz))
  exact ⟨hZR hz, hAZ.trans hsub, hKZ.trans hsub⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
