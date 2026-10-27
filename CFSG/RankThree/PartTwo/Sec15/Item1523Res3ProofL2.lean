module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofL2Orders
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJList

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS Equiv
open CFSG.Assembly.RankThreeEven (projSL)


theorem step153ListedL2R_of_item148R
    (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ n : ℕ, 4 ≤ n → Even n →
        IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* projSL 2 (GaloisField 2 n)) := by
  intro G _ _ A c L h Y hY n hn4 hev
  refine ⟨fun e => ?_⟩
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 h hY4
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have hcen : ∀ z ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y), z = 1 := fun z hz =>
    Sec21.eq_one_of_forall_commute_of_mulEquiv_projSL e (Subgroup.mem_center_iff.mp hz)
  have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    Proof1515.pPrimeCore_three_eq_pCore_two_of hY4.2.2.2 hne fun Z _ hZc _ _ =>
      (Subgroup.eq_bot_iff_forall Z).mpr fun z hz => hcen z (hZc hz)
  set e' := (QuotientGroup.quotientMulEquivOfEq heq).trans e with he'
  have hYc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e'.toEquiv, Sec21.card_projSL_two n (by omega)]
  have hcen' : Nat.card (Subgroup.center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) = 1 := by
    rw [Subgroup.card_eq_one]
    exact (Subgroup.eq_bot_iff_forall _).mpr fun z hz =>
      Sec21.eq_one_of_forall_commute_of_mulEquiv_projSL e' (Subgroup.mem_center_iff.mp hz)
  have hTC : ∀ {S : Type} [Group S], ¬ Sec4.IsTripleCover (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) S :=
    fun hT => by
      rw [hT.1] at hcen'
      norm_num at hcen'
  have hord : ∀ {S : Type} [Group S] {N : ℕ}, Nat.card S = N → N ≤ 16776959 → N ≠ 4080 →
      N ≠ 262080 → IsEmpty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* S) := fun hS hN h4 h6 =>
    ⟨fun φ => Proof1523Res3.card_L2_ne hn4 hev hN h4 h6 (by rw [← hYc, Nat.card_congr φ.toEquiv,
      hS])⟩
  have hJ2 : IsEmpty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    hord KFacts.KS14.card_nativeJ2 (by norm_num) (by norm_num) (by norm_num)
  have hA7 : IsEmpty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)) :=
    hord card_alternatingGroup_seven (by norm_num) (by norm_num) (by norm_num)
  rcases Proof1515.cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', -, h3⟩ |
      ⟨⟨φ10⟩, -, -⟩ | ⟨c', L', m, k, hc', hL', -, -, hiso, -⟩
  ·
    rcases hcases with hφ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e₀, hp, -, -, -, hε⟩ | ⟨-, h6 | hφ⟩
    ·
      obtain ⟨φ⟩ := hφ
      rcases (h.chosen136.2 c' hc' L' hL').1 with hJ | ⟨p, e₀, hp, -, hiso⟩ | h7 | hM | hM
      · obtain ⟨φJ⟩ := hJ
        exact hJ2.false (φ.trans φJ)
      · exact Proof1523Res3.not_isoLThreePi_of_card_L2 hn4 hev hYc p e₀
          (Proof1515.isoLThreePi_congr φ.symm hiso)
      · obtain ⟨φ7⟩ := h7
        exact hA7.false (φ.trans φ7)
      · obtain ⟨φM⟩ := hM
        exact (hord KFacts.KS14.card_nativeM22 (by norm_num) (by norm_num)
          (by norm_num)).false (φ.trans φM)
      · obtain ⟨φM⟩ := hM
        exact (hord KFacts.KS14.card_nativeM12 (by norm_num) (by norm_num)
          (by norm_num)).false (φ.trans φM)
    · exact hA7.false φ
    · exact Proof1523Res3.not_isLThreeEpsAt_of_card_L2 hn4 hev hYc p f hε
    · exact hTC h6
    · obtain ⟨φ⟩ := hφ
      exact (hord card_alternatingGroup_five (by norm_num) (by norm_num) (by norm_num)).false φ
  ·
    rcases h3 with hON | hφ | ⟨_, ⟨φ⟩⟩
    · exact hTC hON
    · obtain ⟨φ⟩ := hφ
      exact hA7.false φ
    · exact (hord Proof1515.card_projSL_three_seven (by norm_num) (by norm_num)
        (by norm_num)).false φ
  ·
    exact (hord card_alternatingGroup_ten (by norm_num) (by norm_num) (by norm_num)).false φ10
  ·
    exact Proof1523Res3.not_isoLThreePi_of_card_L2 hn4 hev hYc 2 (3 * m) hiso

end CFSG.RankThree.PartTwo.Sec15
