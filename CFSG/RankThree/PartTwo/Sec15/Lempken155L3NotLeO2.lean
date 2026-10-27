module

public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec15.Praeger155R1L112Step3
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeO2
import CFSG.RankThree.PartTwo.Sec15.Gagen1521KS
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Main
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith

public section

namespace CFSG.RankThree.PartTwo.Sec15.LempkenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)
variable {G : Type} [Group G] [Finite G]

theorem isoLThreePi_quot_pCore_two_of_cover {L K : Subgroup G} (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L) {p e : ℕ} [Fact p.Prime]
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) :
    Sec4.IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) p e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := Proof155R2.isoQuot_of_le_sup hLK hKL.le
    (hLK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  exact Proof1511.isoLThreePi_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans φ) hiso

theorem pCoreOf_two_le_of_isLThreeEpsAt {A X K : Subgroup G} (hX4 : X ∈ scriptY4 A (lB A))
    (hXK : X ≤ K) {e n : ℕ} (he : 1 ≤ e) (hK : Sec4.IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) 2 e)
    (hX : IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp := (CFSG.RankThree.PartTwo.Sec15.KSL3Two.isSimpleGroup_and_not_isSolvable hX).1
  apply Sylow155R1.pCoreOf_two_le_pCoreOf_two_of_noPerfectTwoCoreSection hXK
    (isPerfect_of_mem_scriptY4 hX4) hsimp
  intro H _ hne
  exact ⟨fun φ => hne (ks1521SubTwoCore _ e he hK H (CFSG.pCore 2 ↥H)
    CFSG.pCore_isPGroup 2 n (IsLThreeEpsAt.of_mulEquiv φ.symm hX))⟩

theorem pCoreOf_two_le_of_omg155_of_not_isoA5 (h154 : Item154R) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) {X K : Subgroup G}
    (hK0 : K ∈ scriptY0 A (lB A)) (hX4 : X ∈ scriptY4 A (lB A)) (hXK : X ≤ K)
    (hKiso : Sec4.IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) p e)
    (hA5 : IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 X with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX4.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hRmem : R ∈ invariantPiSubgroups (Subgroup.normalizer (K : Set G)) (A ⊔ X) (piOf 2) :=
    ⟨(hRX.trans hXK).trans Subgroup.le_normalizer,
      (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, sup_le hAR hXR⟩
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    Sec13.Ronan138P5.center_eq_bot_of_isLThreePi hK0.1.2.2.2
      ⟨p, e, inferInstance, he, hKiso⟩
  rcases h154 G A c L hR K hK0 X hX4 hXK R hRmem with h1 | h2 | h3
  · exact Gagen155R1HJ.le_pCoreOf_of_commutator_le (hRX.trans hXK) h1 hZ
  · obtain ⟨n, m, hn, hm, ⟨φ⟩, hXε, -⟩ := h2
    by_cases hp2 : p = 2
    · subst hp2
      exact pCoreOf_two_le_of_isLThreeEpsAt hX4 hXK he hKiso hXε
    · exfalso
      have hmod : 2 ^ (2 * n * m) % 3 = 1 := by
        rw [show 2 * n * m = 2 * (n * m) by ring, pow_mul, Nat.pow_mod]
        norm_num
      have hL3 : Sec4.IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) 2 (2 * n * m) :=
        Or.inl ⟨hmod, ⟨φ⟩⟩
      have hn0 : 0 < n := by omega
      have hm0 : 0 < m := by omega
      have h2nm : 1 ≤ 2 * n * m := by
        have : 0 < 2 * n * m := Nat.mul_pos (Nat.mul_pos (by norm_num) hn0) hm0
        omega
      have heq : p ^ e = 2 ^ (2 * n * m) :=
        Sec19.Step1917EqProof.eq_of_isoLThreePi he h2nm hKiso hL3
      have hp : Nat.Prime p := Fact.out
      have hdvd : p ∣ 2 ^ (2 * n * m) := by
        rw [← heq]
        exact dvd_pow_self p (by omega)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  · obtain ⟨-, hXA5, -⟩ := h3
    exact (hA5.false hXA5.some).elim

theorem l3_pCoreOf_le_of_ctx155 (h154 : Item154R) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c}) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hKiso : Sec4.IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) p e) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  rcases hC.hyp with hω | hKX
  · rcases hω with ⟨-, hA5⟩ | ⟨c', L', hc', hL', hfac⟩
    · exact pCoreOf_two_le_of_omg155_of_not_isoA5 h154 hR he hC.mem_k.prop hX4 hC.le_k hKiso hA5
    · have hc'c : Subgroup.zpowers c' = Subgroup.zpowers c := by
        rw [hΩ] at hc'
        exact hc'
      have h3L : 3 ∣ Nat.card L := Sec16.Proof1613.three_dvd_card_L hR.toSec14Std
      have hL'L : L' = L :=
        Proof1515.eq_of_mem_lA_of_zpowers_eq hR.toSec14Std h3L hc'c hL'
      rw [hL'L] at hfac
      have hOLK : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 K :=
        Sylow155R1.pCoreOf_le_pCoreOf_of_le_sup hLK hKL.le
      apply Sylow155R1.pCoreOf_le_pCoreOf_of_le_sup hC.le_k
      calc K = L ⊔ CFSG.Open.pCoreOf 2 K := hKL
        _ = ((L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L) ⊔ CFSG.Open.pCoreOf 2 K := by
            conv_lhs => rw [hfac]
        _ ≤ X ⊔ CFSG.Open.pCoreOf 2 K :=
            sup_le (sup_le (inf_le_right.trans le_sup_left)
              (hOLK.trans le_sup_right)) le_sup_right
  · exact Sylow155R1.pCoreOf_le_pCoreOf_of_le_sup hC.le_k hKX.le

end CFSG.RankThree.PartTwo.Sec15.LempkenL3
