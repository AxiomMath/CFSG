module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res13ProofFour
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofDelta

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

namespace Proof17Res13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_zpowers_eq_bot_iff {H : Subgroup G} {x : G} :
    ⁅H, Subgroup.zpowers x⁆ = ⊥ ↔ H ≤ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]

theorem isTwoLocal_normalizer {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) :
    CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (Y₀ : Set G)) := by
  have hmem : Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) :=
    h.scriptM_eq ▸ Set.mem_singleton _
  obtain ⟨P, hP1, hP2, hP⟩ := hmem.1.1
  exact ⟨P, hP1, hP2, hP⟩

theorem not_pCoreOf_le_centralizer {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) :
    ¬ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ≤
      Subgroup.centralizer ({c} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  have hcM : c ∈ M := h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hcC : c ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq)
  have hcQ : c ∈ CFSG.Open.pCoreOf 2 M := h.charTwoType M (isTwoLocal_normalizer h) ⟨hcM, hcC⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨c, hcQ⟩
  have hk' : c ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [h.toSec13Data.orderOf_eq] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

omit [Finite G] in
theorem not_commute_of_quaternion {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2)
    (hR : ∀ u ∈ R, ∀ v ∈ R, u * v = v * u) : False := by
  have hne : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  apply hne
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (hR _ (e.symm _).2 _ (e.symm _).2)

omit [Finite G] in
theorem isElemAbelian_card_of_isKleinFour {R : Subgroup G} (hR : IsKleinFour R) :
    CFSG.Assembly.IsElemAbelian 2 R ∧ Nat.card R = 4 :=
  ⟨⟨IsKleinFour.isMulCommutative, fun x hx => by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : R))⟩, IsKleinFour.card_four⟩

open Proof17Res11 in
theorem exists_choice_of (hFaith : Step1712Faith) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hV : Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 V) V)
    (hVc : ⁅V, Subgroup.zpowers c⁆ = ⊥) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hVP : V ≤ Subgroup.normalizer (P : Set G))
    (hPc : ¬ P ≤ Subgroup.centralizer ({c} : Set G)) :
    ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧ ∃ Z ∈ fourGroups A,
      Z ≤ V ⊓ Subgroup.centralizer ({a} : Set G) ∧ ⁅Z, A⁆ ≠ ⊥ ∧
      ⁅P ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (Z : Set G),
        Subgroup.zpowers c⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcord : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hc1 : c ≠ 1 := h.toSec13Data.ne_one
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hAM : A ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hVC : V ≤ Subgroup.centralizer ({c} : Set G) := commutator_zpowers_eq_bot_iff.mp hVc
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.toSec13Data.commute hx hy
  have hAcen : ∀ {Y : Subgroup G}, Y ≤ A → A ≤ Subgroup.normalizer
      (Subgroup.centralizer (Y : Set G) : Set G) := fun {Y} hYA x hx => Subgroup.le_normalizer
    (Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hYA hy) x hx)
  have hAne : A ≠ ⊥ := fun hA0 => hc1 (by rwa [hA0, Subgroup.mem_bot] at hcA)
  have hgenP := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 3
    Nat.prime_three A P hA.1 hAne hAP (coprime_three_of_isPGroup_two hP2)
  obtain ⟨B, hBA, hB3, hBc⟩ : ∃ B : Subgroup G, B ≤ A ∧ (B.subgroupOf A).index = 3 ∧
      ¬ P ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hPc
    rw [← hgenP]
    exact iSup_le fun B => iSup_le fun hBA => iSup_le fun hB3 => hcon B hBA hB3
  have hcB : c ∉ B := fun hcB => hBc fun x hx =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB) hx.2
  have hBcard : Nat.card B * 3 = Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
    rw [inf_of_le_left hBA] at h1
    rw [← h1, Subgroup.relIndex, hB3, mul_comm]
  have hB9 : Nat.card B = 9 := by
    rw [hA.2] at hBcard
    omega
  have hBc' : ∀ b ∈ B, b ≠ 1 → b ∉ Subgroup.zpowers c := by
    intro b hb hb1 hbc
    have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hbc
    have heq : Subgroup.zpowers b = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers,
          orderOf_eq_prime (HeadProof.pow_three_of_std h (hBA hb)) hb1, hcord])
    exact hcB ((Subgroup.zpowers_le.mpr hb) (heq ▸ Subgroup.mem_zpowers c))
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hA.1 hBA
  have hBne : B ≠ ⊥ := by
    intro hB0
    rw [hB0, Subgroup.card_bot] at hB9
    omega
  have hgenV := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 3
    Nat.prime_three B V hBab hBne (hBA.trans hAV) (coprime_three_of_isPGroup_two hV2)
  obtain ⟨Y', hY'B, hY'3, y, hyB, hyW⟩ : ∃ Y' : Subgroup G, Y' ≤ B ∧
      (Y'.subgroupOf B).index = 3 ∧ ∃ y ∈ B,
        ¬ V ⊓ Subgroup.centralizer (Y' : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hb
      push Not at hb
      exact hBne ((Subgroup.eq_bot_iff_forall B).mpr hb)
    apply hFaith G A c L Y₀ h V hV hVc b (hBA hbB) (hBc' b hbB hb1)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure, ← hgenV]
    exact iSup_le fun Y' => iSup_le fun hY'B => iSup_le fun hY'3 => hcon Y' hY'B hY'3 b hbB
  have hY'card : Nat.card Y' * 3 = Nat.card B := by
    have h1 := Subgroup.relIndex_mul_card (H := Y') (K := B)
    rw [inf_of_le_left hY'B] at h1
    rw [← h1, Subgroup.relIndex, hY'3, mul_comm]
  obtain ⟨a, haY', ha1⟩ : ∃ a ∈ Y', a ≠ 1 := by
    by_contra hb
    push Not at hb
    have hY0 := (Subgroup.eq_bot_iff_forall Y').mpr hb
    rw [hY0, Subgroup.card_bot, hB9] at hY'card
    omega
  have haB : a ∈ B := hY'B haY'
  have haA : a ∈ A := hBA haB
  set W := V ⊓ Subgroup.centralizer (Y' : Set G) with hWdef
  have hWV : W ≤ V := inf_le_left
  have hW2 : IsPGroup 2 W := hV2.to_le hWV
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    Late.le_normalizer_inf hAV (hAcen (hY'B.trans hBA))
  have hWa : W ≤ Subgroup.centralizer ({a} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haY'))
  obtain ⟨Z, hZp, hyZ⟩ := exists_commutatorPiece_not_mem hA.1 hW2 hAW (hBA hyB) hyW
  have hZW : Z ≤ W := hZp.1
  have hZV : Z ≤ V := hZW.trans hWV
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hZp.2.1.le
  have hZab : CFSG.Assembly.IsElemAbelian 2 Z := Sec5.isElemAbelian_of_le hVab hZV
  have hZ4 : Nat.card Z = 4 := by
    rcases Source.IsCommutatorPiece.kleinFour_or_quaternion hA.1 hW2 hZp with hK | hq
    · exact (isElemAbelian_card_of_isKleinFour hK).2
    · obtain ⟨e⟩ := hq
      exact (not_commute_of_quaternion e fun u hu v hv =>
        congrArg Subtype.val (hZab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)).elim
  have hZa : Z ≤ Subgroup.centralizer ({a} : Set G) := hZW.trans hWa
  have hZA : ⁅Z, A⁆ ≠ ⊥ := by
    intro hbot
    apply hyZ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hbot hu) y (hBA hyB)).symm
  refine ⟨a, haA, hBc' a haB ha1, Z, mem_fourGroups_iff.mpr ⟨hAZ, hZab, hZ4⟩, le_inf hZV hZa,
    hZA, ?_⟩
  set T₀ := P ⊓ Subgroup.centralizer ({a} : Set G) with hT₀def
  have hT₀2 : IsPGroup 2 T₀ := hP2.to_le inf_le_left
  have hAa : A ≤ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
    fun x hx => Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx a haA))
  have hcT₀ : c ∈ Subgroup.normalizer (T₀ : Set G) := Late.le_normalizer_inf hAP hAa hcA
  have hZT₀ : Z ≤ Subgroup.normalizer (T₀ : Set G) :=
    Late.le_normalizer_inf (hZV.trans hVP) (hZa.trans Subgroup.le_normalizer)
  have hcodd : Odd (orderOf c) := by
    rw [hcord]
    decide
  have hcZ : ∀ b ∈ Z, c * b = b * c := fun b hb =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hVC (hZV hb))).symm
  have hT₀c : ¬ T₀ ≤ Subgroup.centralizer ({c} : Set G) := fun hle =>
    hBc ((inf_le_inf_left P (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr haB))).trans hle)
  intro hbot
  apply hT₀c
  have hfix : ∀ q ∈ T₀, (∀ b ∈ Z, q * b = b * q) → c * q = q * c := by
    intro q hq hqZ
    have hqC : q ∈ T₀ ⊓ Subgroup.centralizer (Z : Set G) :=
      ⟨hq, Subgroup.mem_centralizer_iff.mpr fun b hb => (hqZ b hb).symm⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (commutator_zpowers_eq_bot_iff.mp hbot hqC)).symm
  have h1 := CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hT₀2
    (hV2.to_le hZV) hcT₀ hZT₀ hcodd hcZ hfix
  intro q hq
  exact Subgroup.mem_centralizer_singleton_iff.mpr (h1 q hq).symm

end Proof17Res13

end CFSG.RankThree.PartTwo.Sec17
