module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorrDefs
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155w2

theorem twentyseven_dvd_of_mod_three_eq_one {q : ℕ} (hq : q % 3 = 1) :
    27 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have e1 : (3 * t + 1) ^ 2 = 3 * t * (3 * t + 2) + 1 := by ring
  have e2 : (3 * t + 1) ^ 3 = 9 * t * (3 * t ^ 2 + 3 * t + 1) + 1 := by ring
  rw [e1, e2, Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact ⟨t * (3 * t + 2) * (t * (3 * t ^ 2 + 3 * t + 1)), by ring⟩

theorem twentyseven_dvd_of_mod_three_eq_two {q : ℕ} (hq : q % 3 = 2) :
    27 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  have e1 : (3 * t + 2) ^ 2 = 3 * (3 * t + 1) * (t + 1) + 1 := by ring
  have e2 : (3 * t + 2) ^ 3 + 1 = 9 * (t + 1) * (3 * t ^ 2 + 3 * t + 1) := by ring
  rw [e1, e2, Nat.add_sub_cancel]
  exact ⟨(3 * t + 1) * (t + 1) * ((t + 1) * (3 * t ^ 2 + 3 * t + 1)), by ring⟩

theorem nine_dvd_card_of_isLThreePi {Z : Type} [Group Z] (h : IsLThreePi Z) :
    9 ∣ Nat.card Z := by
  obtain ⟨p, e, hp, he, h | h⟩ := h
  · obtain ⟨hq, ⟨φ⟩⟩ := h
    rw [Nat.card_congr φ.toEquiv]
    have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [hK] at hc
    have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg] at hc
    obtain ⟨k, hk⟩ := twentyseven_dvd_of_mod_three_eq_one hq
    rw [hk] at hc
    exact ⟨(p ^ e) ^ 3 * k, by linarith⟩
  · obtain ⟨hq, ⟨φ⟩⟩ := h
    rw [Nat.card_congr φ.toEquiv]
    have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg] at hc
    obtain ⟨k, hk⟩ := twentyseven_dvd_of_mod_three_eq_two hq
    rw [hk] at hc
    exact ⟨(p ^ e) ^ 3 * k, by linarith⟩

theorem nine_dvd_card_quot_of_chosen136 {A : Subgroup G} (hA : Chosen136 A) {c : G}
    (hc : Subgroup.zpowers c ∈ omegaA A) {L : Subgroup G} (hL : L ∈ lA A c) :
    9 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  rcases (hA.2 c hc L hL).1 with h1 | hpi | h3 | h4 | h5
  · obtain ⟨φ⟩ := h1
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  · exact nine_dvd_card_of_isLThreePi hpi
  · obtain ⟨φ⟩ := h3
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    norm_num
  · obtain ⟨φ⟩ := h4
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num
  · obtain ⟨φ⟩ := h5
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num

theorem ne_sup_of_a5 {X L : Subgroup G}
    (hX : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)))
    (h9 : 9 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    L ≠ (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro heq
  obtain ⟨φ⟩ := hX
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥X))
  have hXc : Nat.card X = 60 * 2 ^ a := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X),
      Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1, ha]
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
  have h9L : 9 ∣ Nat.card L := h9.trans (Subgroup.card_quotient_dvd_card _)
  have hLN : L ⊓ X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hdvd : Nat.card L ∣ Nat.card X * 2 ^ b := by
    have h1 : Nat.card L ∣ Nat.card (L ⊓ X : Subgroup G) * Nat.card (CFSG.Open.pCoreOf 2 L) := by
      conv_lhs => rw [heq]
      exact card_sup_dvd_card_mul hLN
    rw [hb] at h1
    exact h1.trans (Nat.mul_dvd_mul_right (Subgroup.card_dvd_of_le inf_le_right) _)
  rw [hXc, mul_assoc, ← pow_add] at hdvd
  have h960 : 9 ∣ 60 * 2 ^ (a + b) := h9L.trans hdvd
  have hcop : Nat.Coprime 9 (2 ^ (a + b)) := Nat.Coprime.pow_right _ (by norm_num)
  have := hcop.dvd_of_dvd_mul_right h960
  omega

end Proof155w2

open Proof155w2

@[expose] noncomputable def Step155GrowAltTwoW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ¬ K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) →
    ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ CFSG.Open.pCoreOf 2 Y →
    ¬ ⁅CFSG.Open.pCoreOf 2 Y, K⁆ ≤ CFSG.Open.pCoreOf 2 K →
    Case154Two L K X →
    (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) →
    IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
      Claim155 A K Y

@[expose] noncomputable def Step155GrowAltTwoWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155GrowAltTwoW A c L

theorem step155GrowAltW_of_two {A : Subgroup G} {c : G} {L : Subgroup G}
    (h2 : Step155GrowAltTwoW A c L) : Step155GrowAltW A c L := by
  intro h X K Y M T hC hmax hab hKR hZR hRK hcase
  rcases hcase with ⟨htwo, ⟨hpi, ha5⟩, hcl⟩ | ⟨hthree, c', L', hc', hL', heq⟩
  · exact h2 h X K Y M T hC hmax hab hKR hZR hRK htwo hpi ha5 hcl
  · exact (ne_sup_of_a5 hthree.2.1 (nine_dvd_card_quot_of_chosen136 h.chosen136 hc' hL')
      heq).elim

theorem step155GrowAltWR_of_two (h2 : Step155GrowAltTwoWR) : Step155GrowAltWR :=
  fun G _ _ A c L hR => step155GrowAltW_of_two (h2 G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
