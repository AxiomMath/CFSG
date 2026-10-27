module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA7
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofFactor
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1LeKA7
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Lemma95
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Omega
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Finite
public import CFSG.RankThree.PartTwo.Sec15.F153ObsR
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T112
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof1515

variable {G : Type} [Group G] [Finite G]

theorem eq_inf_sup_pCoreOf_two_of_mem_scriptY4_of_m22 (h148 : Item148R)
    (hbot : Item145BotS14) (h142 : Item142R) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (hL22 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {Y : Subgroup G}
    (hY4 : Y ∈ scriptY4 A (lB A)) :
    Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
  obtain ⟨φL⟩ := hL22
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have hL443 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φL (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Subgroup.zpowers c' = Subgroup.zpowers c ∧ L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact ⟨hcc, eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'⟩
  have hnot34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hL443, KFacts.KS14.card_projSL_three_four] at h1
    omega
  rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  · obtain ⟨hcc, rfl⟩ := hpt c' L' hc' hL'
    have hO : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y := by
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        exact pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 ⟨φ.trans φL⟩ multFree_M22
      · exact pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 h7 multFree_alternatingGroup_seven
      · exact (KFacts.KS14.not_isoLThreePi_M22 p (f * e) (isoLThreePi_congr φL hiso)).elim
      · obtain ⟨φJ⟩ := hJ
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL443
        omega
    rw [hcc] at hdec
    have hfac := eq_inf_sup_pPrimeCoreOf_of_item142 h (h142 G A c L' h) h3L hnot34 hY4 hdec
    rw [pPrimeCoreOf_eq_pCoreOf_two hO, inf_comm] at hfac
    exact hfac
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL443
    omega
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at hL443
    omega
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    exact (KFacts.KS14.not_isLThreeEpsAt_M22 2 (n * m) (IsLThreeEpsAt.of_mulEquiv φL hε)).elim

theorem eq_inf_sup_pCoreOf_two_of_mem_scriptY4_of_a7 (h148 : Item148R)
    (hbot : Item145BotS14) (h142 : Item142R) (h131 : Item131) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hL7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {Y : Subgroup G}
    (hY4 : Y ∈ scriptY4 A (lB A)) :
    Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
  obtain ⟨φL⟩ := hL7
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have hL2520 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
    rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φL (by rw [card_alternatingGroup_seven]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Subgroup.zpowers c' = Subgroup.zpowers c ∧ L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact ⟨hcc, eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'⟩
  have hnot34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hL2520, KFacts.KS14.card_projSL_three_four] at h1
    omega
  rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, hWS⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  · obtain ⟨hcc, rfl⟩ := hpt c' L' hc' hL'
    have hO : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y := by
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        exact pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 ⟨φ.trans φL⟩
          multFree_alternatingGroup_seven
      · exact pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 h7 multFree_alternatingGroup_seven
      · exact (Proof1514.not_isoLThreePi_of_card_2520 hL2520 p (f * e) hiso).elim
      · obtain ⟨φJ⟩ := hJ
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL2520
        omega
    rw [hcc] at hdec
    have hfac := eq_inf_sup_pPrimeCoreOf_of_item142 h (h142 G A c L' h) h3L hnot34 hY4 hdec
    rw [pPrimeCoreOf_eq_pCoreOf_two hO, inf_comm] at hfac
    exact hfac
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL2520
    omega
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    exact (false_of_wStarS4 h131 h (Or.inl ⟨φL⟩) hΩ hWS).elim
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    exact (not_isLThreeEpsAt_of_card_2520 hL2520 2 (n * m) hε).elim

theorem le_K_of_eq_inf_sup_pCoreOf_two_of_m22 {A : Subgroup G} {c : G} {L : Subgroup G}
    (hM22 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (h1512 : Item1512 A (lB A) L) {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A))
    (hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K) :
    L ≤ K := by
  rw [h1512 hM22 K hK hcover]
  exact le_sup_left

theorem isSimpleGroup_quot_pCore_two_of_mem_scriptY4 (h148 : Item148R)
    (hbot : Item145BotS14) (h142 : Item142R) (h131 : Item131) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {X : Subgroup G} (hX4 : X ∈ scriptY4 A (lB A)) :
    IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have hXΔ := eq_deltaZero_of_mem_scriptY4 hbot h hX4
  have h3L : 3 ∣ Nat.card L := by
    rcases hL with hL7 | hL22
    · obtain ⟨φ⟩ := hL7
      exact three_dvd_card_of_mulEquiv φ (by rw [card_alternatingGroup_seven]; norm_num)
    · obtain ⟨φ⟩ := hL22
      exact three_dvd_card_of_mulEquiv φ (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := fun c' L' hc' hL' => by
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have htype : Nonempty (↥X ⧸ CFSG.pPrimeCore 3 ↥X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥X ⧸ CFSG.pPrimeCore 3 ↥X ≃* CFSG.Blueprint.NativeSporadic.M22) := by
    rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hX4 hXΔ with
      ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
        ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, hWS⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at hcases
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        rcases hL with hL7 | hL22
        · obtain ⟨φL⟩ := hL7
          exact Or.inl ⟨φ.trans φL⟩
        · obtain ⟨φL⟩ := hL22
          exact Or.inr ⟨φ.trans φL⟩
      · exact Or.inl h7
      · rcases hL with hL7 | hL22
        · obtain ⟨φL⟩ := hL7
          exact (Proof1514.not_isoLThreePi_of_card_2520 (by
            rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]) p (f * e) hiso).elim
        · obtain ⟨φL⟩ := hL22
          exact (KFacts.KS14.not_isoLThreePi_M22 p (f * e) (isoLThreePi_congr φL hiso)).elim
      · obtain ⟨φJ⟩ := hJ
        rcases hL with hL7 | hL22
        · obtain ⟨φL⟩ := hL7
          have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
            rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]
          rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
          omega
        · obtain ⟨φL⟩ := hL22
          have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
            rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
          rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
          omega
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at φJ
      rcases hL with hL7 | hL22
      · obtain ⟨φL⟩ := hL7
        have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
          rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
        omega
      · obtain ⟨φL⟩ := hL22
        have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
          rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
        omega
    · exact (false_of_wStarS4 h131 h hL hΩ hWS).elim
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at hε
      rcases hL with hL7 | hL22
      · obtain ⟨φL⟩ := hL7
        exact (not_isLThreeEpsAt_of_card_2520 (by
          rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]) 2 (n * m) hε).elim
      · obtain ⟨φL⟩ := hL22
        exact (KFacts.KS14.not_isLThreeEpsAt_M22 2 (n * m)
          (IsLThreeEpsAt.of_mulEquiv φL hε)).elim
  rcases htype with htype7 | htype22
  · have hO : CFSG.pPrimeCore 3 ↥X = CFSG.pCore 2 ↥X :=
      pPrimeCore_eq_pCore_of_mem_scriptY4 hX4 htype7 multFree_alternatingGroup_seven
    haveI hsimp : IsSimpleGroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X) :=
      Proof1514.isSimpleGroup_of_mulEquiv_alternating (by norm_num) htype7.some
    exact (QuotientGroup.quotientMulEquivOfEq hO).symm.isSimpleGroup
  · have hO : CFSG.pPrimeCore 3 ↥X = CFSG.pCore 2 ↥X :=
      pPrimeCore_eq_pCore_of_mem_scriptY4 hX4 htype22 multFree_M22
    haveI hsimp : IsSimpleGroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
      haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
        CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      exact htype22.some.isSimpleGroup
    exact (QuotientGroup.quotientMulEquivOfEq hO).symm.isSimpleGroup

theorem quot_pCore_two_equiv_a7_of_mem_scriptY4 (h148 : Item148R)
    (hbot : Item145BotS14) (h142 : Item142R) (h131 : Item131) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hL7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {K : Subgroup G}
    (hK4 : K ∈ scriptY4 A (lB A)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨φL⟩ := hL7
  have hKΔ := eq_deltaZero_of_mem_scriptY4 hbot h hK4
  have hL2520 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
    rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φL (by rw [card_alternatingGroup_seven]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := fun c' L' hc' hL' => by
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have htype : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* alternatingGroup (Fin 7)) := by
    rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hK4 hKΔ with
      ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
        ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, hWS⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at hcases
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        exact ⟨φ.trans φL⟩
      · exact h7
      · exact (Proof1514.not_isoLThreePi_of_card_2520 hL2520 p (f * e) hiso).elim
      · obtain ⟨φJ⟩ := hJ
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL2520
        omega
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at φJ
      rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL2520
      omega
    · exact (false_of_wStarS4 h131 h (Or.inl ⟨φL⟩) hΩ hWS).elim
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at hε
      exact (not_isLThreeEpsAt_of_card_2520 hL2520 2 (n * m) hε).elim
  obtain ⟨φ⟩ := htype
  have hO : CFSG.pPrimeCore 3 ↥K = CFSG.pCore 2 ↥K :=
    pPrimeCore_eq_pCore_of_mem_scriptY4 hK4 ⟨φ⟩ multFree_alternatingGroup_seven
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).symm.trans φ⟩

theorem type_quot_pCore_two_of_mem_scriptY4 (h148 : Item148R)
    (hbot : Item145BotS14) (h142 : Item142R) (h131 : Item131) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {Y : Subgroup G} (hY4 : Y ∈ scriptY4 A (lB A)) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M22) := by
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have h3L : 3 ∣ Nat.card L := by
    rcases hL with hL7 | hL22
    · obtain ⟨φ⟩ := hL7
      exact three_dvd_card_of_mulEquiv φ (by rw [card_alternatingGroup_seven]; norm_num)
    · obtain ⟨φ⟩ := hL22
      exact three_dvd_card_of_mulEquiv φ (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  have hL2520 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 ∨
      Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
    rcases hL with hL7 | hL22
    · obtain ⟨φ⟩ := hL7
      exact Or.inl (by rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_seven])
    · obtain ⟨φ⟩ := hL22
      exact Or.inr (by rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22])
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := fun c' L' hc' hL' => by
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have htype : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M22) := by
    rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
      ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
        ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, hWS⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at hcases
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        rcases hL with hL7 | hL22
        · obtain ⟨φL⟩ := hL7
          exact Or.inl ⟨φ.trans φL⟩
        · obtain ⟨φL⟩ := hL22
          exact Or.inr ⟨φ.trans φL⟩
      · exact Or.inl h7
      · rcases hL2520 with h1 | h1
        · exact (Proof1514.not_isoLThreePi_of_card_2520 h1 p (f * e) hiso).elim
        · rcases hL with hL7 | hL22
          · obtain ⟨φL⟩ := hL7
            rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven] at h1
            omega
          · obtain ⟨φL⟩ := hL22
            exact (KFacts.KS14.not_isoLThreePi_M22 p (f * e) (isoLThreePi_congr φL hiso)).elim
      · obtain ⟨φJ⟩ := hJ
        rcases hL2520 with h1 | h1
        · rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
          omega
        · rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
          omega
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at φJ
      rcases hL2520 with h1 | h1
      · rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
        omega
      · rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
        omega
    · exact (false_of_wStarS4 h131 h hL hΩ hWS).elim
    · have hLeq : L' = L := hpt c' L' hc' hL'
      rw [hLeq] at hε
      rcases hL with hL7 | hL22
      · obtain ⟨φL⟩ := hL7
        exact (not_isLThreeEpsAt_of_card_2520 (by
          rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]) 2 (n * m) hε).elim
      · obtain ⟨φL⟩ := hL22
        exact (KFacts.KS14.not_isLThreeEpsAt_M22 2 (n * m)
          (IsLThreeEpsAt.of_mulEquiv φL hε)).elim
  rcases htype with htype7 | htype22
  · have hO : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
      pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 htype7 multFree_alternatingGroup_seven
    exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hO).symm.trans htype7.some⟩
  · have hO : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
      pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 htype22 multFree_M22
    exact Or.inr ⟨(QuotientGroup.quotientMulEquivOfEq hO).symm.trans htype22.some⟩

theorem twinOKType_of_mem_scriptY0 (h148 : Item148R) (hbot : Item145BotS14)
    (h142 : Item142R) (h131 : Item131) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {Y : Subgroup G}
    (hY0 : Y ∈ scriptY0 A (lB A)) : F153Obs.TwinOKType Y := by
  refine Or.inl ?_
  have hsimple :=
    isSimpleGroup_quot_pCore_two_of_mem_scriptY4 h148 hbot h142 h131 h hL hN hΩ hY0.1
  have hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 ∨
      Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 443520 := by
    rcases type_quot_pCore_two_of_mem_scriptY4 h148 hbot h142 h131 h hL hN hΩ hY0.1 with ⟨e⟩ | ⟨e⟩
    · exact Or.inl (by rw [Nat.card_congr e.some.toEquiv, card_alternatingGroup_seven])
    · exact Or.inr (by rw [Nat.card_congr e.some.toEquiv, KFacts.KS14.card_nativeM22])
  haveI := hsimple
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) with h0 | h0
    · exact h0
    · exfalso
      have hc : IsMulCommutative (↥Y ⧸ CFSG.pCore 2 ↥Y) := Subgroup.center_eq_top_iff.1 h0
      have hp : Nat.Prime (Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
        Group.is_simple_iff_prime_card.1 inferInstance
      rcases hcard with h2 | h2 <;> rw [h2] at hp <;> norm_num at hp
  rw [hZ]
  simp

theorem res1L112InAt_a7 {A : Subgroup G} {c : G} {L X K Y M T : Subgroup G}
    (h142 : Concl142S14) (h148 : Item148R) (hbot : Item145BotS14)
    (h142R : Item142R) (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (h153 : Item153Main A (lB A)) (h1411 : Item1411_1 A (lB A)) (h135 : Item135)
    (hR : Sec15R G A c L)
    (hq : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hS : Sec14Std G A c L) (hC : Ctx155 A X K Y M T) (hLX : ¬ L ≤ X) :
    L ≤ delta A (lB A) L ∧ L ≤ K ∧ K = L ⊔ CFSG.Open.pCoreOf 2 K ∧
      CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  have hLΔ : L ≤ delta A (lB A) L := le_delta_of_a7 hR (h142 G A c L hS) hq
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    omegaA_eq_singleton_of_a7_m22 h131 h133 hset hR (Or.inr hq) hN
  have hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K :=
    eq_inf_sup_pCoreOf_two_of_mem_scriptY4_of_a7 h148 hbot h142R h131 hR hq hΩ hC.mem_k.prop.1
  have hKbar : Lemma95KQuotient K :=
    quot_pCore_two_equiv_a7_of_mem_scriptY4 h148 hbot h142R h131 hR hq hN hΩ hC.mem_k.prop.1
  have hobs : Claim153Obs A (lB A) := by
    intro Y hY0 S hS
    exact F153Obs.theoremA881 G A c L hR Y hY0.prop
      (twinOKType_of_mem_scriptY0 h148 hbot h142R h131 hR (Or.inl hq) hN hΩ hY0.prop)
      S hS.prop.1.2 hS.prop.1.1.1.2.2 (by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop)
        rw [hn]
        exact (by decide : Nat.Coprime 2 3).pow_left n)
  have hLNK : L ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_scriptY0Star_of_a7 hR hq hC.mem_k hcover hN h153
      hobs h1411 (h142 G A c L hS) h135 hKbar
  have hLK : L ≤ K :=
    le_K_of_mem_scriptY0Star_of_a7_of_LN hR (hC.res ▸ hC.isY.2.1) hC.mem_k hC.le_k hLX hLΔ hΩ
      hq hcover hLNK
  have hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K := by
    rw [← inf_eq_left.mpr hLK]; exact hcover
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hKtype := type_quot_pCore_two_of_mem_scriptY4 h148 hbot h142R h131 hR (Or.inl hq) hN hΩ
    hC.mem_k.prop.1
  have hXtype := type_quot_pCore_two_of_mem_scriptY4 h148 hbot h142R h131 hR (Or.inl hq) hN hΩ hX4
  have hfin : NoPerfectTwoCoreSection (↥K ⧸ CFSG.pCore 2 ↥K) (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rcases hKtype with hK | hK <;> rcases hXtype with hX | hX
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_alt7_alt7
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_alt7_m22
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_m22_alt7
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_m22_m22
  have hstep : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K :=
    pCoreOf_two_le_pCoreOf_two_of_noPerfectTwoCoreSection hC.le_k (isPerfect_of_mem_scriptY4 hX4)
      (isSimpleGroup_quot_pCore_two_of_mem_scriptY4 h148 hbot h142R h131 hR (Or.inl hq) hN hΩ hX4)
      hfin
  exact ⟨hLΔ, hLK, hKL, hstep⟩

theorem res1L112InAt_m22 {A : Subgroup G} {c : G} {L X K Y M T : Subgroup G}
    (h142 : Concl142S14) (h148 : Item148R) (hbot : Item145BotS14)
    (h142R : Item142R) (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (h1512 : Item1512 A (lB A) L) (hgen : Step142LowerGenM22)
    (hR : Sec15R G A c L)
    (hq : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hS : Sec14Std G A c L) (hC : Ctx155 A X K Y M T) (hLX : ¬ L ≤ X) :
    L ≤ delta A (lB A) L ∧ L ≤ K ∧ K = L ⊔ CFSG.Open.pCoreOf 2 K ∧
      CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  have hLΔ : L ≤ delta A (lB A) L := le_delta_of_m22 hgen hR (h142 G A c L hS) hq
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    omegaA_eq_singleton_of_a7_m22 h131 h133 hset hR (Or.inl hq) hN
  have hcover : K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K :=
    eq_inf_sup_pCoreOf_two_of_mem_scriptY4_of_m22 h148 hbot h142R hR hq hΩ hC.mem_k.prop.1
  have hLK : L ≤ K :=
    le_K_of_eq_inf_sup_pCoreOf_two_of_m22 (A := A) (c := c) (L := L) hq
      h1512 hC.mem_k hcover
  have hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K := by
    rw [← inf_eq_left.mpr hLK]; exact hcover
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hKtype := type_quot_pCore_two_of_mem_scriptY4 h148 hbot h142R h131 hR (Or.inr hq) hN hΩ
    hC.mem_k.prop.1
  have hXtype := type_quot_pCore_two_of_mem_scriptY4 h148 hbot h142R h131 hR (Or.inr hq) hN hΩ hX4
  have hfin : NoPerfectTwoCoreSection (↥K ⧸ CFSG.pCore 2 ↥K) (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rcases hKtype with hK | hK <;> rcases hXtype with hX | hX
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_alt7_alt7
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_alt7_m22
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_m22_alt7
    · exact noPerfectTwoCoreSection_congr hK.some.symm hX.some.symm noPerfectTwoCoreSection_m22_m22
  have hstep : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K :=
    pCoreOf_two_le_pCoreOf_two_of_noPerfectTwoCoreSection hC.le_k (isPerfect_of_mem_scriptY4 hX4)
      (isSimpleGroup_quot_pCore_two_of_mem_scriptY4 h148 hbot h142R h131 hR (Or.inr hq) hN hΩ hX4)
      hfin
  exact ⟨hLΔ, hLK, hKL, hstep⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
