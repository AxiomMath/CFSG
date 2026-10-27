module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec17.Item1725Proof
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec17.Item1722Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim1722XThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → ¬ 3 ∣ Nat.card (xA A ⊔ S : Subgroup G)

namespace Proof1721

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_three_eq_bot {X : Subgroup G} (hX : ¬ 3 ∣ Nat.card X) :
    oPrimeResidualOf 3 X = ⊥ := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_eq_bot_iff]
  rintro x ⟨hxX, k, hk⟩
  have hdvd : orderOf (⟨x, hxX⟩ : X) ∣ Nat.gcd (3 ^ k) (Nat.card X) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk)))
      (orderOf_dvd_natCard _)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact congrArg Subtype.val hdvd

theorem pCoreOf_le_of_mem_scriptQPiStar {A Y S : Subgroup G} (hY : Y ∈ scriptQ A (lB A))
    (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) : CFSG.Open.pCoreOf 2 Y ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSY : S ≤ Y := hS.prop.1.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hOY : O ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hSO : S ≤ Subgroup.normalizer (O : Set G) :=
    hSY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.2.2
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hSO2 : IsPGroup 2 (S ⊔ O : Subgroup G) := IsPGroup.to_sup_of_normal_right' hS2 hO2 hSO
  have hmem : S ⊔ O ∈ scriptQPi A (lB A) Y (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hY (sup_le hSY hOY) (Sec14.le_normalizer_sup hAS hAO), sup_le hSY hOY⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hSO2⟩
  exact le_sup_right.trans (hS.2 hmem le_sup_left)

end Proof1721

open Proof1721 in
theorem claim1722X_of (hX3 : Claim1722XThree) (h146 : Item146S14) (h166 : Item166S17)
    (h168 : Item168S17) (h179 : Item179S17) (hbot : Item145BotS17) : Claim1722X := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  have hA : IsE27 A := hs.isE27
  have h166' := h166 G A c L Y₀ hs
  have hbot' := hbot G A c L Y₀ hs
  set X := xA A ⊔ S with hXdef
  have hX3' : ¬ 3 ∣ Nat.card X := hX3 G A c L Y₀ Y₁ S p P h
  have hxAQ : xA A ∈ scriptQ A (lB A) := xA_mem_scriptQ hA.1.1
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  obtain ⟨hSG, -, -, -⟩ := h.item168_at h166' hbot' (h168 G A c L Y₀ hs)
  have hSM : S ≤ Subgroup.normalizer (Y₀ : Set G) := hs.qStar_le S hSG
  have hxAM : xA A ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (HeadProof.centralizer_le_M hs)
  have hXM : X ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le hxAM hSM
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec14.le_normalizer_sup hxAQ.1.2.2 hSQ.1.2.2
  have hXΔ : X = delta A (lB A) X :=
    le_antisymm (sup_le (le_delta hxAQ le_sup_left) (le_delta hSQ le_sup_right)) (delta_le X)
  have hXtop : X ≠ ⊤ := by
    intro htop
    apply hX3'
    rw [htop, Subgroup.card_top]
    have := Subgroup.card_dvd_of_le (le_top : A ≤ ⊤)
    rw [hA.2, Subgroup.card_top] at this
    exact (by norm_num : 3 ∣ 27).trans this
  obtain ⟨⟨U, hU, hUM⟩, hUY⟩ := h179 G A c L Y₀ hs Y₀ hs.mem_y0Star
  have hY₁3 : Y₁ ∈ scriptY3Star A (lB A) :=
    hs.mem_scriptY3Star_of_not_le h166' hbot' h.mem_y1Star h.not_le_M
  have hY₁Q : Y₁ ∈ scriptQ A (lB A) :=
    Proof165.mem_scriptQ_of_three hA (h146 G A c L hs.toSec14Std) h.mem_y1Star.prop.1.2
      h.mem_y1Star.prop.1.1.1.2 (not_three_dvd_of_oPrimeResidualOf_eq_bot' h.mem_y1Star.prop.2)
  have hUS : U ≤ S :=
    (hUY U hU hUM Y₁ hY₁3).trans (pCoreOf_le_of_mem_scriptQPiStar hY₁Q h.mem_qStar_two)
  set O := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) with hO
  have hOX : O ⊓ X ≤ CFSG.Open.pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact Late.le_normalizer_inf
      (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) Subgroup.le_normalizer
  have hUX : U ≤ CFSG.Open.pCoreOf 2 X := (le_inf hUM.2 (hUS.trans le_sup_right)).trans hOX
  have hU1 : U ≠ ⊥ := by
    intro hbot
    have h4 := hU.1.2.2
    rw [hbot, Subgroup.card_bot] at h4
    omega
  have hO2X : CFSG.Open.pCoreOf 2 X ≠ ⊥ := fun hbot => hU1 (le_bot_iff.mp (hbot ▸ hUX))
  exact ⟨⟨⟨⟨hXtop, hAX⟩, hO2X⟩, hXΔ⟩, oPrimeResidualOf_three_eq_bot hX3'⟩

end CFSG.RankThree.PartTwo.Sec17
