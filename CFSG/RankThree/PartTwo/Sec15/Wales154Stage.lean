module

import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Wales154Read

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Stage


theorem allPointsHJ_of_point (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A)
    (hL' : L' ∈ lA A c')
    (hJ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    AllPointsHJ A := by
  have hD' : Sec13Data G A c' L' :=
    { h.toSec13Data with zpowers_mem_omegaA := hc', mem_lA := hL' }
  obtain ⟨d, hdA, hd1, hdc⟩ := exists_three_central_of_j2 hD' hJ
  exact fun e he => exists_hj_of_hj_point h134 h48 Sec4.Sporadic.rank3II_4_15 h hc' hL' hJ hdA
    hd1 hdc he

theorem quot_j2_of_allPointsHJ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hHJ : AllPointsHJ A) {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G}
    (hL' : L' ∈ lA A c') :
    Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨Le, hLe, ⟨φ⟩⟩ := hHJ c' hc'
  have h3 : 3 ∣ Nat.card Le := by
    have hc := Nat.card_congr φ.toEquiv
    rw [KFacts.KS14.card_nativeJ2] at hc
    have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Le)
    rw [hc] at hdvd
    exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
  have hLeL : Le = L' := (h.chosen136.2 c' hc' L' hL').2 Le hLe.1 h3
  subst hLeL
  exact ⟨φ⟩

end Stage

section Read


theorem read154_nhj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (hR : Sec15R G A c L) (hNHJ : ¬ AllPointsHJ A) {Z : Subgroup G}
    (hZ : Z ∈ scriptY4 A (lB A)) :
    (∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      (∀ z ∈ Z, c' * z * c'⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) ∧
      ∃ L' ∈ lA A c',
        Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
        ((Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
          Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 7))) ∨
        (∃ (p f e : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e ∧
          Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') p (f * e) ∧
          IsLThreeEpsAt (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) p f)) ∨
    Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 10)) ∨
    (∃ (c' : G) (L' : Subgroup G) (n m : ℕ), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      1 ≤ n ∧ 1 ≤ m ∧ Sec4.IsoLThreePi (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) 2 (3 * n) ∧
      IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 (n * m)) := by
  have hZΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hZ
  rcases Proof1523Res3.cases148Full_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hZ hZΔ
    with ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', -, L', hc', hL', hJ, -⟩ | ⟨hA10, -⟩ | h5
  · obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc'o : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
    have htriv := trivial_of_dec hc'A hc'o hZ.1.2 hdec
    rcases hcases with h1 | h2 | h3 | ⟨hJ, -⟩
    · exact Or.inl ⟨c', hc', htriv, L', hL', Or.inl h1⟩
    · exact Or.inl ⟨c', hc', htriv, L', hL', Or.inr (Or.inl h2)⟩
    · exact Or.inl ⟨c', hc', htriv, L', hL', Or.inr (Or.inr h3)⟩
    · exact (hNHJ (allPointsHJ_of_point h134 h48 hR.toSec14Std hc' hL' hJ)).elim
  · exact (hNHJ (allPointsHJ_of_point h134 h48 hR.toSec14Std hc' hL' hJ)).elim
  · exact Or.inr (Or.inl hA10)
  · exact Or.inr (Or.inr h5)

theorem read154_hj (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (hR : Sec15R G A c L) (hHJ : AllPointsHJ A) {Z : Subgroup G}
    (hZ : Z ∈ scriptY4 A (lB A)) :
    (∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      (∀ z ∈ Z, c' * z * c'⁻¹ * z⁻¹ ∈ pPrimeCoreOf 3 Z) ∧
      Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* CFSG.Blueprint.NativeSporadic.J2)) ∨
    Sec4.IsTripleCover (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) (alternatingGroup (Fin 6)) ∨
    Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 5)) ∨
    Sec4.IsTripleCover (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z) CFSG.Blueprint.NativeSporadic.ON ∨
    Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 7)) ∨
    (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) := by
  have hZΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hZ
  rcases Proof1523Res3.cases148Full_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hZ hZΔ
    with ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨-, -, -, -, -, -, -, -, -, -, h3⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', hn, hm, -, hε⟩
  · obtain ⟨φJ⟩ := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc'o : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
    have htriv := trivial_of_dec hc'A hc'o hZ.1.2 hdec
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨hL, -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
    · exact Or.inl ⟨c', hc', htriv, ⟨φ.trans φJ⟩⟩
    · exfalso
      rcases hL with ⟨⟨φM⟩⟩ | ⟨_, ⟨φL⟩⟩ | ⟨_, ⟨φU⟩⟩
      · exact KFacts.KS14.ks17J2NotList.2.2.false (φJ.symm.trans φM)
      · exact KFacts.KS14.not_isLThreeEpsAt_j2 5 2 (Or.inl ⟨φJ.symm.trans φL⟩)
      · exact KFacts.KS14.not_isLThreeEpsAt_j2 5 1
          (Or.inr ⟨by norm_num, ⟨φJ.symm.trans φU⟩⟩)
    · exact (KFacts.KS14.ks17J2NotList.1 p (f * e)
        (Proof155w3.isoLThreePi_of_mulEquiv φJ hiso)).elim
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr (Or.inl h5))
  · rcases h3 with hON | h7 | h7
    · exact Or.inr (Or.inr (Or.inr (Or.inl hON)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7))))
  · obtain ⟨φJ⟩ := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    exact (KFacts.KS14.ks17J2NotList.2.1.false (φJ.symm.trans φ7)).elim
  · obtain ⟨φJ⟩ := quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    exact (KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (IsLThreeEpsAt.of_mulEquiv φJ hε)).elim

end Read


end CFSG.RankThree.PartTwo.Sec15.Wales154
