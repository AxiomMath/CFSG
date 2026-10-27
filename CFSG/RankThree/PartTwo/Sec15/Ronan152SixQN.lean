module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofQN
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

open Proof15Res4 Proof15Res7

section Certificates


theorem Conf1515HJ.isJ2Type (h : Conf1515HJ A c L Y) : IsJ2Type Y :=
  h.quot_pCore_two_equiv

theorem Conf1515HJ.n155_le_normalizer_big
    (h : Conf1515HJ A c L Y) (h152 : Item152Big A (lB A)) (h153 : Item153MainJ2 A (lB A)) :
    n155 A Y ≤ Subgroup.normalizer (Y : Set G) := fun _ ht =>
  mem_normalizer_of_map_conj_eq_self (Ronan152Six.map_conj_eq_of_hasFaithfulE9_big
    h.sec15R.toSec14Std h152 h.mem_scriptY0Star h.isJ2Type.big152 h.hasFaithfulE9
    (Ronan152Six.n155_mem_maximalTwoLocalsContaining_j2 h153 h.mem_scriptY0Star h.isJ2Type) ht)

theorem Conf1515HJ.delta_le_normalizer_big
    (h : Conf1515HJ A c L Y) (h152 : Item152Big A (lB A)) (h153 : Item153MainJ2 A (lB A))
    (h155 : Item155wJ2 A (lB A)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRQ : R ∈ scriptQ A (lB A))
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hZR : zHJ L Y d ≤ Subgroup.normalizer (R : Set G))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hRd : R ≤ Subgroup.centralizer ({d} : Set G)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (zHJ L Y d ⊔ R) : Subgroup G) : Set G)) :
    delta A (lB A) M ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  obtain ⟨eZ⟩ := h.zHJ_quot hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  have hCq : IsQuasisimple ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
    (Item148HJ.centralizer_facts h.j2 hz1 hzc).1
  have hC1080 : Nat.card ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) = 1080 := by
    rw [card_of_isTripleCover (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc),
      card_alternatingGroup_six]
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZL : Z ≤ L := hZle.trans (inf_le_left.trans inf_le_left)
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ hmap
  set Y' := Z ⊔ R with hY'def
  have hY'C : Y' ≤ Subgroup.centralizer ({d} : Set G) := sup_le hZd hRd
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAZ hAR
  have hY'R : Y' ≤ Subgroup.normalizer (R : Set G) := sup_le hZR Subgroup.le_normalizer
  have hRO' : R ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'R hR2
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.sec15R.toTheoremFourHyp hd1 (top_le_iff.mp (htop ▸ hY'C))
  have hY'Δ : Y' ≤ delta A (lB A) Y' :=
    sup_le (hZΔ.trans (delta_mono le_sup_left)) (le_delta hRQ le_sup_right)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRO'))⟩, le_antisymm hY'Δ (delta_le Y')⟩
  have hZ'Z : oPrimeResidualOf 3 Z = Z := by
    rw [hZdef, zHJ, Proof156Res4.oRes3_idem']
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hZX' : Z ≤ X' := hZ'Z ▸ oPrimeResidualOf_mono 3 le_sup_left
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'le : X' ≤ Z ⊔ (X' ⊓ R) := Proof155w.le_sup_inf_of_le hZR hZX' hX'Y'
  have hX'R : X' ≤ Subgroup.normalizer ((X' ⊓ R : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hX'Y'.trans hY'R)
  obtain ⟨e₁⟩ := Proof155R2.isoQuot_of_le_sup hZX' hX'le (hZX'.trans hX'R) hX'R
    (hR2.to_le inf_le_right)
  set e := e₁.symm.trans eZ with he
  have hX'Δ : X' ≤ delta A (lB A) X' :=
    hX'le.trans (sup_le (hZΔ.trans (delta_mono hZX'))
      (le_delta (mem_scriptQ_of_le hRQ inf_le_right
        (Late.le_normalizer_inf (le_normalizer_oPrimeResidualOf hAY') hAR)) inf_le_left))
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), le_normalizer_oPrimeResidualOf hAY'⟩,
      (Proof156Res4.oRes3_idem' Y').symm, le_antisymm hX'Δ (delta_le X'),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hCq⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hZX'.trans le_sup_left) (hRO'.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hX'Y : X' ≤ Y :=
    Proof155R2.oPrimeResidualOf_le_of_le_sup hR2 hRY (sup_le_sup_right hZY R)
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨h.mem_scriptY0Star, hX'Y, sup_le (hZY.trans Subgroup.le_normalizer) hRY⟩
  have hX'1080 : Nat.card (↥X' ⧸ CFSG.pCore 2 ↥X') = 1080 := by
    rw [Nat.card_congr e.toEquiv, hC1080]
  have hhyp : omg155 A X' ∨ Y = X' ⊔ CFSG.Open.pCoreOf 2 Y := by
    refine Or.inl (Or.inl ⟨fun ⟨n, _, hiso⟩ =>
      not_isoLThreePi_of_card_small (Or.inr hX'1080) 2 n hiso, ⟨fun e5 => ?_⟩⟩)
    have h60 := Nat.card_congr e5.toEquiv
    rw [hX'1080, card_alternatingGroup_five] at h60
    norm_num at h60
  have hX'b : Big152 X' := by
    unfold Big152
    rw [hX'1080]
    norm_num
  exact (h155 Y' hY'3 hX'4 hX'b hY'eq Y hΓ h.isJ2Type hhyp M hM).trans
    (h.n155_le_normalizer_big h152 h153)

theorem Conf1515HJ.exists_Q_big
    (h : Conf1515HJ A c L Y)
    (h152 : Item152Big A (lB A)) (h153 : Item153MainJ2 A (lB A)) (h155 : Item155wJ2 A (lB A))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    (hodd : ¬ Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))) :
    ∃ Q ∈ scriptQPiStar A (lB A) (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) (piOf 2),
      Q ≠ ⊥ ∧ Q ≤ Subgroup.normalizer (Y : Set G) ∧
        zHJ L Y d ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.sec15R.toSec14Std
  obtain ⟨P, hP1, hP2, hPD, hAP, hZP, hmax⟩ := h.exists_maxP hdA hd1 hdZ hodd
  set O3 := pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hO3
  have hPQ : P ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le_pPrimeCoreOf hS hdA (hPD.trans inf_le_right) hAP
  have hPmem : P ∈ scriptQPi A (lB A) O3 (piOf 2) :=
    ⟨⟨hPQ, hPD.trans inf_le_right⟩, (isPiSubgroup_piOf_iff Nat.prime_two P).mpr hP2⟩
  obtain ⟨Q, hPQle, hQmax⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) O3 (piOf 2))) hPmem
  have hQmem := hQmax.prop
  have hQ2 : IsPGroup 2 Q := isPGroup_of_mem_scriptQPi Nat.prime_two hQmem
  have hQQ : Q ∈ scriptQ A (lB A) := hQmem.1.1
  have hQO3 : Q ≤ O3 := hQmem.1.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hP1)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (zHJ L Y d ⊔ P) : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAP (sup_le hZP Subgroup.le_normalizer) hx)⟩
  have hΔ := h.delta_le_normalizer_big h152 h153 h155 hdA hd1 hdZ hP2 hP1 hPQ hAP hZP
    (hPD.trans inf_le_left) ((hPD.trans inf_le_right).trans (pPrimeCoreOf_le 3 _)) hMm
  set NQ := Q ⊓ Subgroup.normalizer (P : Set G) with hNQ
  have hANQ : A ≤ Subgroup.normalizer (NQ : Set G) :=
    Late.le_normalizer_inf hAQ (hAP.trans Subgroup.le_normalizer)
  have hNQQ : NQ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQQ inf_le_left hANQ
  have hNQY : NQ ≤ Subgroup.normalizer (Y : Set G) :=
    (le_delta hNQQ (inf_le_right.trans hle)).trans hΔ
  have hNQeq : NQ = P :=
    hmax NQ (hQ2.to_le inf_le_left) (le_inf hNQY (inf_le_left.trans hQO3)) hANQ
      (le_inf hPQle Subgroup.le_normalizer)
  have hQP : Q ≤ P := le_of_inf_normalizer_le hQ2 hPQle hNQeq.le
  have hQeq : Q = P := le_antisymm hQP hPQle
  refine ⟨Q, hQmax, ?_, ?_, ?_⟩
  · rw [hQeq]
    exact hP1
  · rw [hQeq]
    exact hPD.trans inf_le_left
  · rw [hQeq]
    exact hZP

theorem Conf1515HJ.normalizer_inf_le_big
    (h : Conf1515HJ A c L Y) (h152 : Item152Big A (lB A)) (h153 : Item153MainJ2 A (lB A))
    (h155 : Item155wJ2 A (lB A)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {Q : Subgroup G}
    (hQ : Q ∈ scriptQPiStar A (lB A) (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))
      (piOf 2))
    (hQ1 : Q ≠ ⊥) (hQY : Q ≤ Subgroup.normalizer (Y : Set G))
    (hZQ : zHJ L Y d ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.sec15R.toSec14Std
  have hD := h.sec13Data
  have hY := h.mem_scriptY0Star
  have hQmem := hQ.prop
  have hQ2 : IsPGroup 2 Q := isPGroup_of_mem_scriptQPi Nat.prime_two hQmem
  have hQQ : Q ∈ scriptQ A (lB A) := hQmem.1.1
  have hQd : Q ≤ Subgroup.centralizer ({d} : Set G) := hQmem.1.2.trans (pPrimeCoreOf_le 3 _)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set Z := zHJ L Y d with hZdef
  have hZL : Z ≤ L := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_left)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ
      (h.map_zHJ hdA hd1 hdZ hdL)
  rintro g ⟨hgA, hgQ⟩
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hQ2 hQ1)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (Z ⊔ Q) : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAQ (sup_le hZQ Subgroup.le_normalizer) hx)⟩
  have hΔM := h.delta_le_normalizer_big h152 h153 h155 hdA hd1 hdZ hQ2 hQ1 hQQ hAQ hZQ hQY hQd
    hMm
  have hgM : g ∈ M := hle hgQ
  have hMg : M.map (MulAut.conj g).toMonoidHom = M :=
    map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hΔg : (delta A (lB A) M).map (MulAut.conj g).toMonoidHom = delta A (lB A) M := by
    rw [Sec17.HeadProof.map_conj_delta hgA M, hMg]
  set Yg := Y.map (MulAut.conj g).toMonoidHom with hYg
  have hΔYg : delta A (lB A) M ≤ Subgroup.normalizer (Yg : Set G) := by
    intro x hx
    have hx' : x ∈ (delta A (lB A) M).map (MulAut.conj g).toMonoidHom := hΔg.symm ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    have hyN := hΔM hy
    refine mem_normalizer_of_map_conj_eq_self ?_
    rw [hYg, ← map_conj_mul, show (MulAut.conj g).toMonoidHom y * g = g * y by
      simp [MulAut.conj_apply], map_conj_mul, map_conj_eq_self_of_mem_normalizer hyN]
  have hZM : Z ≤ M := hZQ.trans hle
  have hZYg : Z ≤ Subgroup.normalizer (Yg : Set G) :=
    (hZΔ.trans (delta_mono hZM)).trans hΔYg
  have hQM : Q ≤ M := Subgroup.le_normalizer.trans hle
  have hQYg : Q ≤ Subgroup.normalizer (Yg : Set G) :=
    (le_delta hQQ hQM).trans hΔYg
  have hYg0 : Yg ∈ scriptY0Star A (lB A) := Sec16.map_conj_mem_scriptY0Star hgA hY
  have hYgJ : IsJ2Type Yg := h.isJ2Type.map_conj g
  have hAYg : A ≤ Subgroup.normalizer (Yg : Set G) := hYg0.prop.1.1.2
  have hNYg : n155 A Yg ∈ CFSG.maximalTwoLocalsContaining ((Yg ⊔ A : Subgroup G) : Set G) :=
    Ronan152Six.n155_mem_maximalTwoLocalsContaining_j2 h153 hYg0 hYgJ
  have hNle : Subgroup.normalizer (Yg : Set G) ≤ n155 A Yg :=
    normalizer_le_n155w_of_j2 h153 hYg0 hYgJ
  have hNYgm : n155 A Yg ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (Z ⊔ Q) : Subgroup G) : Set G) :=
    ⟨hNYg.1, fun x hx => hNle (sup_le hAYg (sup_le hZYg hQYg) hx)⟩
  have hΔN := h.delta_le_normalizer_big h152 h153 h155 hdA hd1 hdZ hQ2 hQ1 hQQ hAQ hZQ hQY hQd
    hNYgm
  have hYgY : Yg ≤ Subgroup.normalizer (Y : Set G) :=
    (hYg0.prop.1.2.2.1.le.trans (delta_mono (Subgroup.le_normalizer.trans hNle))).trans hΔN
  have hMY : n155 A Y ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    Ronan152Six.n155_mem_maximalTwoLocalsContaining_j2 h153 hY h.isJ2Type
  have hYθ := Ronan152Six.mem_thetaComponentsIn_of_big hS h152 hY h.isJ2Type.big152 hMY
  obtain ⟨-, -, hM2, hF⟩ := facts_of_mem_maximalTwoLocalsContaining hS hMY
  have hYgle : Yg ≤ n155 A Y := hYgY.trans (normalizer_le_n155w_of_j2 h153 hY h.isJ2Type)
  obtain ⟨J, hJ, hYgJ', hJ0⟩ := h152 Yg hYg0.prop.1 hYgJ.big152 (n155 A Y) hM2 hYgle hF
  have hJeq : Yg = J := hYg0.eq_of_le hJ0 hYgJ'
  rw [← hJeq] at hJ
  obtain ⟨E, hEY, hEab, hE9, -⟩ := h.hasFaithfulE9
  have hEg : E.map (MulAut.conj g).toMonoidHom ≤ Yg := Subgroup.map_mono hEY
  have heq := eq_of_mem_thetaComponentsIn_of_hasFaithfulE9 hS hMY.1 hYθ hJ h.hasFaithfulE9
    hEg (CFSG.SectionRank.isElemAbelian_map hEab _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9])
  exact mem_normalizer_of_map_conj_eq_self heq.symm

end Certificates

theorem step1515HJQN_of_big
    (h152 : Item152BigR) (h153 : Item153MainJ2R)
    (h155 : Item155wJ2R) :
    Step1515HJQN := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hodd
  have hR := h.sec15R
  obtain ⟨Q, hQ, hQ1, hQY, hZQ⟩ := h.exists_Q_big (h152 G A c L hR) (h153 G A c L hR)
    (h155 G A c L hR) hdA hd1 hdZ hodd
  exact ⟨Q, hQ, fun g hg => h.normalizer_inf_le_big (h152 G A c L hR) (h153 G A c L hR)
    (h155 G A c L hR) hdA hd1 hdZ hQ hQ1 hQY hZQ hg.1⟩

end CFSG.RankThree.PartTwo.Sec15
