module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck158Core
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15.Proof158Steps

variable {G : Type} [Group G] [Finite G]

theorem leaf2_card_L
    (h138 : Item138N) (h41 : Sec4.Item4_1LargePrime) {A L J P : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hJ : J ∈ scriptY0 A (lB A))
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (J : Set G)))
    (hAP : A ≤ P) (hΩ : A ≠ omegaOneThree P) (hA9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) ∧ (Nat.card L).factorization 3 = 2 := by
  have hD := hR.toSec13Data
  have hA := hD.isElemAbelian
  have hA27 := hD.card_eq
  have hsecA : ∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a haA haC
    have h1 := hD.mem_lA.2.2.1
    rw [sectionCentralizer_eq_inf hD.le_normalizer] at h1
    have h2 : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := ⟨haA, haC⟩
    rw [h1] at h2
    exact h2
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (hA9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) := by
    intro h9
    obtain ⟨E, hEP, hEN, hcE, hE, hE27, hsec, hTC, -⟩ :=
      Liebeck158.exists_typeC_of_split h41 hR he hL3 hJ.2 hP h3L hAP hA hA27 hA9 hAeq hsecA hΩ
    have hL3pi : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨p, e, inferInstance, he, hL3⟩
    have hEE : E ∈ partTwoE G :=
      mem_partTwoE_of_le_normalizer hJ.2 hE hE27 ((hEP.trans hP.le).trans inf_le_right)
    obtain ⟨-, hmod9, -⟩ := h138 G A c L hD hL3pi E hcE hE hE27 hEN hsec
      (Or.inr (hypT_of_mem_of_mem hR hEE hcE)) hTC
    exact hmod9 p e he hL3 h9
  refine ⟨h9, ?_⟩
  have hbar := Item138Proof.factorization_card_three_eq_two he hL3 h9
  have hcard : Nat.card L = Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) *
      Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (aschbacherSolvableCore 3 ↥L).card_eq_card_quotient_mul_card_subgroup
  have hθ : (Nat.card (aschbacherSolvableCore 3 ↥L)).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd three_not_dvd_card_aschbacherSolvableCore
  rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
    hbar, hθ]

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
