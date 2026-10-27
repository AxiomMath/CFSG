module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorrDefs
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec15.Item155R2Proof
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof155R2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof155w

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem le_pCoreOf_of_ctx155w (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hmax : MaxT155 A X K T) (hab : Above155w A X) {D M' : Subgroup G} (hD2 : IsPGroup 2 D)
    (hDQ : D ∈ scriptQ A (lB A)) (hYD : Y ≤ Subgroup.normalizer (D : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hTD : T ⊔ D ∈ scriptQ A (lB A))
    (hM' : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (Y ⊔ D) : Subgroup G) : Set G))
    (hnot : ¬ delta A (lB A) M' ≤ n155 A K) : D ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27
  by_contra hDR
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := hDQ.1.2.2
  have hXY : X ≤ Y := hC.res ▸ oPrimeResidualOf_le_self 3 Y
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hYeq : Y = X ⊔ R := by
    have := hC.isY.2.2
    rwa [hC.res] at this
  set S := R ⊔ D with hS
  set Y' := Y ⊔ D with hY'
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := hRY.trans hYD
  have hS2 : IsPGroup 2 S := IsPGroup.to_sup_of_normal_right' hR2 hD2 hRD
  have hS3 : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hY'S : Y' ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (le_normalizer_sup hYR hYD) (le_sup_right.trans Subgroup.le_normalizer)
  have hSY' : S ≤ Y' := sup_le (hRY.trans le_sup_left) le_sup_right
  have hSO : S ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSY' hY'S hS2
  have hY'XS : Y' = X ⊔ S := by rw [hY', hYeq, hS, sup_assoc]
  have hXY' : X ≤ Y' := hXY.trans le_sup_left
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := hXY'.trans hY'S
  have hM'' : M' ∈ CFSG.maximalTwoLocalsContaining ((Y' ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hM'
  obtain ⟨hY'M', -, hM'2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM''
  have hY'top : Y' ≠ ⊤ := fun htop => hM'2.1.1 (top_le_iff.mp (htop ▸ hY'M'))
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAY hAD
  have hY'K : Y' ≤ Subgroup.normalizer (K : Set G) := sup_le hC.norm_k hDK
  have hY'Δ : Y' = delta A (lB A) Y' := le_antisymm
    (sup_le (hY3.2.le.trans (delta_mono le_sup_left)) (le_delta hDQ le_sup_right))
    (delta_le _)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hR1 (le_bot_iff.mp (h0 ▸ ((le_sup_left : R ≤ S).trans hSO)))⟩,
      hY'Δ⟩
  set X' := oPrimeResidualOf 3 Y' with hX'
  have hXX' : X ≤ X' := hX4.2.1.le.trans (oPrimeResidualOf_mono 3 hXY')
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hY'X' : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (hY'XS.le.trans (sup_le_sup hXX' hSO))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  by_cases hXeq : X' = X
  ·
    have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hC.mem_t.prop
    have hTY : T ≤ Y := hC.mem_t.prop.1.2
    have hTD2 : IsPGroup 2 (T ⊔ D : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hT2 hD2 (hTY.trans hYD)
    have hTDmem : T ⊔ D ∈ scriptQPi A (lB A) Y' (piOf 2) :=
      ⟨⟨hTD, sup_le (hTY.trans le_sup_left) le_sup_right⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hTD2⟩
    obtain ⟨T', hTDT', hT'⟩ :=
      Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) Y' (piOf 2))) hTDmem
    have hctx : Ctx155 A X K Y' M' T' := by
      refine ⟨⟨hY'3, ?_, hY'X'⟩, hXeq, hC.mem_k, hC.le_k, hC.hyp, hY'K, hM', hnot, hT'⟩
      rw [show oPrimeResidualOf 3 Y' = X from hXeq]
      exact hX4
    have hDT : ¬ D ≤ T := fun hDT =>
      hDR (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hDT.trans hTY) hYD hD2)
    have hlt : T < T' :=
      lt_of_lt_of_le (lt_of_le_of_ne le_sup_left fun heq => hDT (heq ▸ le_sup_right)) hTDT'
    exact absurd (hmax Y' M' T' hctx) (not_le.mpr (Subgroup.card_lt_of_lt hlt))
  ·
    have hlt : X < X' := lt_of_le_of_ne hXX' (Ne.symm hXeq)
    have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX4.1.2
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := le_normalizer_sup (hAY.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)) hAD
    have hAX' : A ≤ Subgroup.normalizer (X' : Set G) := le_normalizer_oPrimeResidualOf hAY'
    have hY'NX' : Y' ≤ Subgroup.normalizer (X' : Set G) :=
      le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
    obtain ⟨e⟩ := isoQuot_of_le_sup hXX' (hX'Y'.trans hY'XS.le) hXS (hX'Y'.trans hY'S) hS2
    have hK3 := Sec17.Proof17Q0.pPrimeCoreOf_mem_invariantPiSubgroups hAY'
    have hKN : pPrimeCoreOf 3 Y' ≤
        Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 Y') : Set G) :=
      (pPrimeCoreOf_le 3 Y').trans (hY'Δ.le.trans (delta_le_normalizer_delta
        (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hK3 (le_normalizer_pPrimeCoreOf 3 Y')))
    have h147 := rank3II_14_7_reduction hA h1444 h146 hAY' hKN
    have hX0 : X ≤ deltaZero A (lB A) Y' :=
      (rank3II_15_1_lB hA hbot hX4).le.trans (deltaZero_mono hXY')
    have hSK : S ≤ pPrimeCoreOf 3 Y' := le_pPrimeCoreOf hSY' hY'S hS3
    have hXSQ : ⁅X, S⁆ ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le (delta_mem_scriptQ hA h146 hK3)
        ((Subgroup.commutator_mono hX0 hSK).trans h147) (le_normalizer_commutator hAX hAS)
    have hXSX' : ⁅X, S⁆ ≤ X' := by
      rw [Subgroup.commutator_le]
      intro x hx s hs
      have hxs : s * x⁻¹ * s⁻¹ ∈ X' :=
        (Subgroup.mem_normalizer_iff.mp (hY'NX' (hSY' hs)) x⁻¹).mp (inv_mem (hXX' hx))
      have e1 : ⁅x, s⁆ = x * (s * x⁻¹ * s⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hXX' hx) hxs
    have hX'Δ : X' = delta A (lB A) X' := by
      refine le_antisymm ?_ (delta_le _)
      calc X' ≤ X ⊔ ⁅X, S⁆ :=
            (le_of_eq (congrArg (oPrimeResidualOf 3) hY'XS)).trans (oPrimeResidualOf_sup_le hS2)
        _ ≤ delta A (lB A) X' :=
          sup_le (hX4.2.2.1.le.trans (delta_mono hXX')) (le_delta hXSQ hXSX')
    have hX'4 : X' ∈ scriptY4 A (lB A) := by
      refine ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), hAX'⟩,
        (oPrimeResidualOf_idem 3 Y').symm, hX'Δ, ?_⟩
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hX4.2.2.2
    have hX'K : X' ≤ K :=
      oPrimeResidualOf_le_of_le_sup hS2 (hSY'.trans hY'K) (hY'XS.le.trans
        (sup_le_sup_right hC.le_k S))
    have hΓ : K ∈ gam155 A (lB A) Y' X' := ⟨hC.mem_k, hX'K, hY'K⟩
    have hhyp : omg155 A X' ∨ K = X' ⊔ CFSG.Open.pCoreOf 2 K := by
      rcases hC.hyp with hom | hKX
      · left
        rcases hom with ⟨h1, h2⟩ | hcl
        · refine Or.inl ⟨fun ⟨n, hn, hpi⟩ => h1 ⟨n, hn, ?_⟩, ⟨fun f => h2.false (e.trans f)⟩⟩
          rcases hpi with ⟨hq, ⟨f⟩⟩ | ⟨hq, ⟨f⟩⟩
          · exact Or.inl ⟨hq, ⟨e.trans f⟩⟩
          · exact Or.inr ⟨hq, ⟨e.trans f⟩⟩
        · exact omg155_of_le hXX' hcl
      · right
        exact le_antisymm (hKX.le.trans (sup_le_sup_right hXX' _))
          (sup_le hX'K (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
    exact hnot ((hab Y' ⟨hY'3, hX'4, hY'X'⟩ hlt).2 K hΓ hhyp M' hM')

theorem inf_n155_le_pCoreOf_w (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X K Y M T P J : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hmax : MaxT155 A X K T) (hab : Above155w A X)
    (hJ0 : J ∈ scriptY0 A (lB A)) (hXJ : X ≤ J) (hP : P ∈ scriptQ A (lB A)) (hPM : P ≤ M)
    (hTP : T ≤ P) (hQP : CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ P)
    (hRQ : CFSG.Open.pCoreOf 2 Y ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (P ⊔ J) : Set G))
    (hQK : CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ n155 A K ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ n155 A K ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 Y with hR
  set Q := CFSG.Open.pCoreOf 2 (P ⊔ J) with hQ
  set NK := Subgroup.normalizer (K : Set G) with hNK
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hP.1.2.2
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJ0.1.1.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_normalizer_sup hAP hAJ).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hQ𝓠 : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_le hP hQP hAQ
  have hAK : A ≤ NK := hC.mem_k.prop.1.1.2
  have hANK : A ≤ Subgroup.normalizer (NK : Set G) :=
    hAK.trans (Sec6.normalizer_le_normalizer_normalizer K)
  set D' := Q ⊓ NK with hD'
  have hD'2 : IsPGroup 2 D' := hQ2.to_le inf_le_left
  have hAD' : A ≤ Subgroup.normalizer (D' : Set G) := Late.le_normalizer_inf hAQ hANK
  have hD'Q : D' ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ𝓠 inf_le_left hAD'
  have hYeq : Y = X ⊔ R := by
    have := hC.isY.2.2
    rwa [hC.res] at this
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    (hXJ.trans le_sup_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hYeq]
    exact sup_le hXQ hRQ
  have hYD' : Y ≤ Subgroup.normalizer (D' : Set G) :=
    Late.le_normalizer_inf hYQ (hC.norm_k.trans (Sec6.normalizer_le_normalizer_normalizer K))
  have hT : T ∈ scriptQ A (lB A) := hC.mem_t.prop.1.1
  have hTD' : T ⊔ D' ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hP (sup_le hTP (inf_le_left.trans hQP)) (le_normalizer_sup hT.1.2.2 hAD')
  have hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, hAM, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (Y ⊔ D') : Subgroup G) : Set G) :=
    ⟨hC.mem_m.1, fun x hx => (sup_le hAM (sup_le hYM ((inf_le_left.trans hQP).trans hPM))) hx⟩
  have hD'R : D' ≤ R := le_pCoreOf_of_ctx155w h h1444 h146 hbot hC hmax hab hD'2 hD'Q
    hYD' inf_le_right hTD' hM' hC.not_le
  exact (le_inf inf_le_left hQK).trans hD'R

theorem step155GrowW_of (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Item154 A (lB A) L')
    (halt : Step155GrowAltW A c L) : Step155GrowW A c L := by
  intro h X K Y M T hC hmax hab hKR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Late.IsE27 A := h.isE27
  set R := CFSG.Open.pCoreOf 2 Y with hR
  set O := CFSG.Open.pCoreOf 2 K with hO
  set Z := ⁅O, K⁆ with hZ
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hK0 : K ∈ scriptY0 A (lB A) := hC.mem_k.prop
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hXY : X ≤ Y := hC.res ▸ oPrimeResidualOf_le_self 3 Y
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hRK0 : R ≤ Subgroup.normalizer (K : Set G) := hRY.trans hC.norm_k
  by_cases hZR : Z ≤ R
  · by_cases hRK : ⁅R, K⁆ ≤ O
    · exact absurd (le_normalizer_of_commutator_le hR2 hRK0 hK0.1.2.1 hRK hZR) hKR
    ·
      have hRmem : R ∈ invariantPiSubgroups (Subgroup.normalizer (K : Set G)) (A ⊔ X)
          (piOf 2) :=
        ⟨hRK0, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, sup_le hAR (hXY.trans hYR)⟩
      have halts : Case154Two L K X ∨ Case154Three A L K X R :=
        (h154 c L h.toSec13Data.zpowers_mem_omegaA h.toSec13Data.mem_lA K hK0 X hX4 hC.le_k R
          hRmem).resolve_left hRK
      have hom : omg155 A X := by
        refine hC.hyp.resolve_right fun hKX => ?_
        rcases halts with ⟨n, m, hn, hm, ⟨φK⟩, hXε, -⟩ | ⟨⟨φK⟩, ⟨φX⟩, -⟩
        · have hc := Sec16.card_quot_pCore_eq_of_eq_sup hC.le_k hKX
          rw [Nat.card_congr φK.toEquiv] at hc
          exact Sec16.false_of_card_eq_projSL hn hm hXε hc
        · exact Sec16.false_of_j2_a5 hC.le_k hKX φK φX
      refine halt h X K Y M T hC hmax hab hKR hZR hRK ?_
      rcases halts with h2 | h3
      ·
        have hcl : ¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
            L' ∈ lA A c' ∧ L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L' := by
          rintro ⟨c', L', hc', hL', heq⟩
          obtain ⟨n, m, -, -, ⟨φK⟩, -⟩ := h2
          rcases h154 c' L' hc' hL' K hK0 X hX4 hC.le_k R hRmem with h1' |
              ⟨-, -, -, -, -, -, hne⟩ | ⟨⟨φK'⟩, -⟩
          · exact hRK h1'
          · exact hne heq
          · exact KFacts.KS14.not_isLThreeEpsAt_j2 2 (2 * n * m) (Or.inl ⟨φK'.symm.trans φK⟩)
        exact Or.inl ⟨h2, hom.resolve_right hcl, hcl⟩
      ·
        exact Or.inr ⟨h3, hom.resolve_left fun h1 => h1.2.false h3.2.1.some⟩
  ·
    intro C hC1 hCR hCc
    by_contra hnot
    have hZ𝓠 : Z ∈ scriptQ A (lB A) :=
      Sec17.Proof17Q0.commutator_pCoreOf_mem_scriptQ hA h1444 h146 hbot hK0.1
    have hZO : Z ≤ O := commutator_pCoreOf_le K
    have hZ2 : IsPGroup 2 Z := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K).to_le hZO
    have hYK : Y ≤ Subgroup.normalizer (K : Set G) := hC.norm_k
    have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
      hYK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
    have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_commutator hYO hYK
    set D := Z ⊓ Subgroup.normalizer (R : Set G) with hD
    have hD2 : IsPGroup 2 D := hZ2.to_le inf_le_left
    have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
      Late.le_normalizer_inf hZ𝓠.1.2.2 (hAR.trans (Sec6.normalizer_le_normalizer_normalizer R))
    have hDQ : D ∈ scriptQ A (lB A) := mem_scriptQ_of_le hZ𝓠 inf_le_left hAD
    have hYD : Y ≤ Subgroup.normalizer (D : Set G) :=
      Late.le_normalizer_inf hYZ (hYR.trans (Sec6.normalizer_le_normalizer_normalizer R))
    have hDK : D ≤ Subgroup.normalizer (K : Set G) :=
      (inf_le_left.trans hZO).trans
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer)
    have hT : T ∈ scriptQ A (lB A) := hC.mem_t.prop.1.1
    have hTD : T ⊔ D ∈ scriptQ A (lB A) :=
      sup_mem_scriptQ_of_item146 hA h146 hT hDQ (hC.mem_t.prop.1.2.trans hYD)
    have hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h' := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := R) (C.subgroupOf R)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCR] at h'
    have hC2 : IsPGroup 2 C := hR2.to_le hCR
    obtain ⟨M', hCM', hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
      (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hC2 hC1)
    have hM'mem : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (Y ⊔ D) : Subgroup G) : Set G) :=
      ⟨hM', fun x hx => hCM' ((sup_le hAR (sup_le hYR inf_le_right)).trans hNRC hx)⟩
    have hnot' : ¬ delta A (lB A) M' ≤ n155 A K := fun hle => hnot ((delta_mono hCM').trans hle)
    have hDR : D ≤ R := le_pCoreOf_of_ctx155w h h1444 h146 hbot hC hmax hab hD2 hDQ hYD hDK
      hTD hM'mem hnot'
    exact hZR (le_of_inf_normalizer_le155 hR2 hZ2 (hRY.trans hYZ) hDR)

end Proof155w

open Proof155w

theorem step155RQNW_of {A : Subgroup G} {c : G} {L : Subgroup G} (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hK : Step155RQKW A c L) : Step155RQNW A c L :=
  fun h X K Y M T P J hC hmax hab hJM hJ0 hXJ D =>
    inf_n155_le_pCoreOf_w h h1444 h146 hbot hC hmax hab hJ0 hXJ D.mem_p.prop.1.1
      (D.mem_p.prop.1.2.trans inf_le_left) D.le_tp D.le_qp D.norm_rq
      (hK h X K Y M T P J hC hmax hab hJM hJ0 hXJ D)

theorem step155GrowWR_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h154 : Item154R) (halt : Step155GrowAltWR) : Step155GrowWR :=
  fun G _ _ A c L hR => step155GrowW_of (h1444 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std)
    (fun c' L' hc' hL' => h154 G A c' L' (sec15R_of_basePoint hR hc' hL')) (halt G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
