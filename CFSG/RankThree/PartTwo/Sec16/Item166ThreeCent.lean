module

public import CFSG.RankThree.PartTwo.Sec14.Item14Statements
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec16.Notation
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofStar
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late

theorem eq_bot_of_normal_odd {H : Type*} [Group H] [Finite H]
    (hF : CFSG.generalizedFitting H = CFSG.pCore 2 H) {D : Subgroup H} [D.Normal]
    (hD : ¬ 2 ∣ Nat.card D) : D = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CFSG.IsCharacteristicP 2 H :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore H 2).mpr hF
  have hle : D ≤ CFSG.pPrimeCore 2 H := by
    have hmem : D ∈ {K : Subgroup H | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} :=
      ⟨inferInstance, (Nat.prime_two.coprime_iff_not_dvd).mpr hD⟩
    exact le_sSup hmem
  rw [CFSG.pPrimeCore_eq_bot_of_isCharacteristicP H 2 hchar] at hle
  exact le_bot_iff.mp hle

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_bot_of_odd {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A)) {Z O : Subgroup G}
    (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z) (hOZ : O ≤ Z)
    (hZO : Z ≤ Subgroup.normalizer (O : Set G)) (hO2 : ¬ 2 ∣ Nat.card O)
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) : ⁅O, A⁆ = ⊥ := by
  have hA : IsE27 A := h.isE27
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := hZ.prop.1.1.2
  have hZQ : Z ∈ scriptQ A (lB A) :=
    Proof165.mem_scriptQ_of_three hA h146 hZ.prop.2 hAZ hZ3
  obtain ⟨hN2, hNF, hZN⟩ := Y4Core.twoLocal_facts h hZ.prop.1
  have hNZ : Z = delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Z : Set G)) :=
    Proof15Res8Star.eq_delta_normalizer_of_mem_scriptY3Star h hZ
  set N := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Z : Set G)
  set R := ⁅O, A⁆
  have hRO : R ≤ O := Subgroup.le_normalizer_iff_commutator_le_left.mp hAO
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := Subgroup.normalizer_commutator_ge_right O A
  have hRZ : R ≤ Z := hRO.trans hOZ
  have hRQ : R ∈ scriptQ A (lB A) := mem_scriptQ_of_le hZQ hRZ hAR
  have h3O : ¬ 3 ∣ Nat.card O := fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le hOZ))
  have hA3 : IsPGroup 3 A :=
    IsPGroup.of_card_dvd_pow (n := 3) (by rw [hA.2]; norm_num)
  have hR0 : R ∈ scriptQZero A (lB A) :=
    ⟨hRQ, (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three A O hA3 h3O hAO).symm⟩
  have hRN : R ≤ N := hRZ.trans hZN
  have hRZ₀ : R ≤ deltaZero A (lB A) N := le_deltaZero hR0 hRN
  have hZ₀Z : deltaZero A (lB A) N ≤ Z := by
    rw [hNZ]
    exact deltaZero_le_delta N
  have hFZ₀ : CFSG.generalizedFitting ↥(deltaZero A (lB A) N) =
      CFSG.pCore 2 ↥(deltaZero A (lB A) N) := ((h149 N hN2.1).2.2.2 hNF).2
  set Z₀ := deltaZero A (lB A) N
  have hZ₀O : Z₀ ≤ Subgroup.normalizer (O : Set G) := hZ₀Z.trans hZO
  have hnorm : ((O ⊓ Z₀).subgroupOf Z₀).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun x y hx hy => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hZ₀O hy) x).mp hx.1,
      Z₀.mul_mem (Z₀.mul_mem hy hx.2) (Z₀.inv_mem hy)⟩
  have hodd : ¬ 2 ∣ Nat.card ((O ⊓ Z₀).subgroupOf Z₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact fun h2 => hO2 (h2.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hDbot : (O ⊓ Z₀).subgroupOf Z₀ = ⊥ := eq_bot_of_normal_odd hFZ₀ hodd
  have hinfbot : O ⊓ Z₀ = ⊥ := by
    have hmap := congrArg (fun D : Subgroup ↥Z₀ => D.map Z₀.subtype) hDbot
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] at hmap
  have hRbot : R = ⊥ := by
    have hle : R ≤ O ⊓ Z₀ := le_inf hRO hRZ₀
    rw [hinfbot] at hle
    exact le_bot_iff.mp hle
  exact hRbot

theorem le_centralizer_of_odd {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A)) {Z O : Subgroup G}
    (hZ : Z ∈ scriptY3Star A (lB A)) (hZ3 : ¬ 3 ∣ Nat.card Z) (hOZ : O ≤ Z)
    (hZO : Z ≤ Subgroup.normalizer (O : Set G)) (hO2 : ¬ 2 ∣ Nat.card O)
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) :
    O ≤ Subgroup.centralizer (A : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact commutator_eq_bot_of_odd h h146 h149 hZ hZ3 hOZ hZO hO2 hAO

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
