module

public import CFSG.RankThree.PartTwo.Sec15.MathAsch1513Of316
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec12.Hering129KH2b
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1Cover

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1515

variable {G : Type} [Group G] [Finite G]

theorem one_le_of_isoLThreePi_two {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {m : ℕ}
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m) : 1 ≤ m := by
  by_contra hm
  obtain rfl : m = 0 := by omega
  have h9 := Proof155w2.nine_dvd_card_quot_of_chosen136 h.chosen136 h.zpowers_mem_omegaA h.mem_lA
  rcases hL with ⟨-, ⟨φ⟩⟩ | ⟨h2, -⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 0)
    have hF : Nat.card (GaloisField 2 0) = 2 := by
      rw [Nat.card_congr (Sec12.Hering129KH2b.galoisFieldZeroAlgEquiv 2).toEquiv, Nat.card_zmod]
    rw [hF] at hc
    rw [Nat.card_congr φ.toEquiv] at h9
    norm_num at hc
    omega
  · norm_num at h2

section A7

theorem false_of_a7_at_two
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {m : ℕ} (hm : 1 ≤ m) (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hmY : MeetsY4 A (lB A) L Y)
    (hY7 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 Sec14.Ronan149.item145BotS14_holds h hY4
  obtain ⟨φY⟩ := hY7
  have hYc : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 := by
    rw [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven]
  have hQs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Proof1514.isSimpleGroup_of_mulEquiv_alternating (by norm_num) φY
  have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isSimpleGroup hQs
      (by rw [hYc]; norm_num))
  have hY7' : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 2520 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq heq).toEquiv, hYc]
  have h3L : 3 ∣ Nat.card L :=
    (Proof1514.three_dvd_card_inf_of_meetsY4 hmY).trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have h5 : ∀ k : ℕ, 1 ≤ k → ∀ _ : Fact (Nat.Prime 5),
      ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 5 k := by
    intro k hk _ h5
    have heq5 := Sec19.Step1917EqProof.eq_of_isoLThreePi hm hk hL h5
    have h2 : 2 ∣ 5 ^ k := heq5 ▸ dvd_pow_self 2 (by omega)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
  rcases cases148_of_mem_scriptY4 (Sec14.Ronan148M.item148R_holds G A c L h) h.isElemAbelian.1
      hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
      ⟨⟨φ10⟩, -, -⟩ | ⟨c', L', n, m', hc', hL', -, -, hiso', -⟩
  · obtain rfl := hpt c' L' hc' hL'
    rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p', f, e', hp', -, -, -, hε⟩ | ⟨⟨φJ⟩, -⟩
    · obtain ⟨φ⟩ := hφ
      exact Proof1514.not_isoLThreePi_of_card_2520 (by
        rw [← Nat.card_congr φ.toEquiv, hY7']) 2 m hL
    · rcases hL'' with hM | ⟨h5f, ⟨φ⟩⟩ | ⟨h5f, ⟨φU⟩⟩
      · obtain ⟨φM⟩ := hM
        exact KFacts.KS14.not_isoLThreePi_M22 2 m (isoLThreePi_congr φM hL)
      · exact h5 2 (by norm_num) h5f (Or.inl ⟨by norm_num, ⟨φ⟩⟩)
      · exact h5 1 le_rfl h5f (Or.inr ⟨by norm_num, ⟨φU⟩⟩)
    · exact not_isLThreeEpsAt_of_card_2520 hY7' p' f hε
    · exact Proof1514.not_isoLThreePi_of_j2 φJ hL
  · obtain rfl := hpt c' L' hc' hL'
    exact Proof1514.not_isoLThreePi_of_j2 φJ hL
  · have h1 := Nat.card_congr φ10.toEquiv
    rw [hY7', KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at h1
    omega
  · exact Proof1514.not_isoLThreePi_of_card_2520 hY7' 2 (3 * n) hiso'

section Step

theorem step1515_at_two
    (h316 : Sec19.Item316) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) {m : ℕ} (hm : 1 ≤ m)
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m)
    (hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Step1515 A (lB A) c L := by
  intro Y hY hmY _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Res1Omega1513.omegaA_eq_of_isoLThreePi h316 h hL hnPGL hWH ⟨Y, hY.prop⟩
  have hAHY : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) :=
    le_inf (hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
      hY.prop.1.1.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le hAHY hA3
  obtain ⟨hprod, -, hYL, hcases, -⟩ :=
    Res1H1.item1511R_of_item316 h316 G A c L h 2 m hm hL Y hY.prop hmY P hAP hP
  rcases hcases with hε | hY7
  · exact ⟨2, m, inferInstance, hm, hL, hprod, hYL, hε, hΩ⟩
  · exact (false_of_a7_at_two h hm hL hΩ hY hmY hY7).elim

end Step

end A7

end CFSG.RankThree.PartTwo.Sec15.Res1Cover
