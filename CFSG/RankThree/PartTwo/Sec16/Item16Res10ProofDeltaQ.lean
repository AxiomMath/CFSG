module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofDeltaQ
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item176ProofTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res10DeltaQ

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem pCoreOf_sup_mem_scriptQ {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (h142 : Concl142 A (lB A)) (h146 : Item146 A (lB A))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hLY : L ≤ Y)
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y)
    (hQ0 : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    {R : Subgroup G} (hRQ : R ∈ scriptQ A (lB A)) (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) :
    CFSG.Open.pCoreOf 2 (R ⊔ L) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hR.toSec13Data
  have hE27 : Late.IsE27 A := hR.toSec14Std.isE27
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set P := CFSG.Open.pCoreOf 2 (R ⊔ L) with hPdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (R ⊔ L)
  have hNO : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hOY : O ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hRLY : R ⊔ L ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le hRY (hLY.trans Subgroup.le_normalizer)
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (R ⊔ L)).trans hRLY
  have hRP : R ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (R ⊔ L))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRQ.1.2.2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    (Sec14.le_normalizer_sup hAR hD.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (R ⊔ L))
  have hPO2 : IsPGroup 2 (P ⊔ O : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hP2 hO2 (hPY.trans hNO)
  have hRPO : R ≤ Subgroup.normalizer ((P ⊔ O : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hRP (hRY.trans hNO)
  set S := R ⊔ (P ⊔ O) with hSdef
  have hS2 : IsPGroup 2 S := IsPGroup.to_sup_of_normal_right' hR2 hPO2 hRPO
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    Sec14.le_normalizer_sup hAR (Sec14.le_normalizer_sup hAP (hAY.trans hNO))
  set T := S ⊓ Y with hTdef
  have hT2 : IsPGroup 2 T := hS2.to_le inf_le_left
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := Late.le_normalizer_inf hAS hAY
  have hOT : O ≤ T := le_inf (le_sup_right.trans le_sup_right) hOY
  have hTcov : T = (T ⊓ L) ⊔ O := by
    refine le_antisymm (fun t ht => ?_) (sup_le inf_le_left hOT)
    have htY : t ∈ ((Y ⊓ L ⊔ O : Subgroup G) : Set G) := by
      rw [← hcov]
      exact ht.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Y ⊓ L) O (inf_le_left.trans hYO)] at htY
    obtain ⟨l, hl, o, ho, rfl⟩ := htY
    have hlT : l ∈ T := by
      have h1 := T.mul_mem ht (T.inv_mem (hOT ho))
      rwa [mul_inv_cancel_right] at h1
    exact Subgroup.mul_mem_sup ⟨hlT, hl.2⟩ ho
  have hTLQ : T ⊓ L ∈ scriptQ A (lB A) :=
    Sec17.Proof176.mem_scriptQ_of_le_centralizer h142 hD.zpowers_mem_omegaA
      (not_three_dvd_of_isPGroup_two (hT2.to_le inf_le_left))
      (Late.le_normalizer_inf hAT hD.le_normalizer) (inf_le_right.trans hD.le_centralizer)
  have hTQ : T ∈ scriptQ A (lB A) := by
    rw [hTcov]
    exact Sec14.sup_mem_scriptQ_of_item146 hE27 h146 hTLQ hQ0
      ((inf_le_left.trans inf_le_right).trans hYO)
  have hRT : R ≤ Subgroup.normalizer (T : Set G) :=
    Late.le_normalizer_inf (le_sup_left.trans Subgroup.le_normalizer) hRY
  have hRTQ : R ⊔ T ∈ scriptQ A (lB A) := Sec14.sup_mem_scriptQ_of_item146 hE27 h146 hRQ hTQ hRT
  have hPle : P ≤ R ⊔ T := by
    intro p hp
    have hpRY : p ∈ ((R ⊔ Y : Subgroup G) : Set G) :=
      (sup_le_sup_left hLY R) ((CFSG.LieType.BorelTits.pCoreOf_le 2 (R ⊔ L)) hp)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R Y hRY] at hpRY
    obtain ⟨r, hr, y, hy, rfl⟩ := hpRY
    have hyS : y ∈ S := by
      have h1 : r⁻¹ * (r * y) ∈ S := S.mul_mem (S.inv_mem (Subgroup.mem_sup_left hr))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left hp))
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem_sup hr ⟨hyS, hy⟩
  exact mem_scriptQ_of_le hRTQ hPle hAP

theorem cover_of_not_a10 (h1514 : Item1514R) (hMeets : Step163Meets) {A : Subgroup G} {c : G}
    {L : Subgroup G} (hR : Sec15R G A c L) (hO : CFSG.Open.pCoreOf 2 L = ⊥) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y)
    (hY10 : IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) :
    Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y := by
  rcases h1514 G A c L hR Y hY (hMeets G A c L hR Y hY hLY) with
    ⟨hcov, -⟩ | ⟨⟨h7⟩, -, -, hY7 | hY10'⟩ | ⟨-, -, -, -, hno, -⟩
  · exact hcov
  · obtain ⟨hY7⟩ := hY7
    rw [inf_eq_right.mpr hLY]
    refine le_antisymm (Res9DeltaQ.le_sup_pCoreOf_of_card hLY hO ?_)
      (sup_le hLY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
    have h2520 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 := by
      rw [Nat.card_congr hY7.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    have hL2520 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
      rw [Nat.card_congr h7.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    rw [h2520, ← hL2520]
    exact Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L))
  · obtain ⟨φ⟩ := hY10'
    exact (hY10.false φ).elim
  · exact absurd hLY (hno Y hY)

end Res10DeltaQ

open Res10DeltaQ

theorem step163DeltaQ_of_res10 (h142 : Concl142R) (h1514 : Item1514R) (hMeets : Step163Meets)
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) : Step163DeltaQ := by
  intro G _ _ A c L hR hL hO Y hY R hgood hRY hfpf
  by_cases hY10 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
  · obtain ⟨φ⟩ := hY10
    exact Res9DeltaQ.mem_scriptQ_of_alternating_ten h142 h1514 hMeets h1444 h146 hbot hR hL hO
      hY φ hgood hRY hfpf
  rw [not_nonempty_iff] at hY10
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : L ≤ Y := hL Y hY
  have hcov := cover_of_not_a10 h1514 hMeets hR hO hY hLY hY10
  have hQ0 : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    ProofVB167.pCoreOf_mem_scriptQ_of_cover hR.toSec14Std (h1444 G A c L hR.toSec14Std)
      (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std) (h142 G A c L hR) hY.prop.1
      (Or.inl hcov)
  exact pCoreOf_sup_mem_scriptQ hR (h142 G A c L hR) (h146 G A c L hR.toSec14Std)
    hY.prop.1.1.2 hLY hcov hQ0 hgood.1.1.1 (isPGroup_of_mem_scriptQPi Nat.prime_two hgood.1) hRY

end CFSG.RankThree.PartTwo.Sec16
