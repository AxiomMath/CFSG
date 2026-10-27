module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProof
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Item14Hyperplanes
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofEps
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTen
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.Sec16.Item161Proof
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOrders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Y4LThreePiNHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ X ∈ scriptY4 A (lB A), ∀ n : ℕ, 1 ≤ n →
      IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n → Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n

variable {G : Type} [Group G] [Finite G]

namespace Proof154Pi

theorem isoLThreePi_two_of_isoLThreePi {X : Type} [Group X] [Finite X]
    (hXp : Group.IsPerfect X) {n p e : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n) (he : 1 ≤ e)
    (hε : IsLThreeEpsAt X 2 n) (hπ : Sec4.IsoLThreePi X p e) : Sec4.IsoLThreePi X 2 n := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, rfl⟩ := kf148FieldChar_holds X e he hXp hπ 2 n hn hε
    exact hπ
  · exact (Sec16.Proof166Res4.not_isLThreeEpsAt_two_of_isoLThreePi hp2 he hπ hn hε).elim

theorem not_isLThreeEpsAt_two_of_card_a10 {X : Type} [Group X] (hX : Nat.card X = 1814400)
    {n : ℕ} (hn : 1 ≤ n) (hε : IsLThreeEpsAt X 2 n) : False := by
  obtain ⟨g, u, hg, hu, hc⟩ := Sec16.exists_card_mul_of_isLThreeEpsAt hn hε
  rw [hX] at hc
  have hg' : Odd g := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hg with rfl | rfl <;> decide
  have h7 : 2 ^ 7 * (14175 * g) = 2 ^ (3 * n) * u := by
    rw [← hc]
    ring
  have h73 := Item148Rank.eq_of_two_pow_mul_odd148 ((by decide : Odd 14175).mul hg') hu h7
  omega

theorem isoLThreePi_of_mem_scriptY4
    (h134 : Item134) (h48 : Sec4.Item4_8) (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4) (hσ : Step148KTypeSigma)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A)
    {X : Subgroup G} (hX : X ∈ scriptY4 A (lB A)) {n : ℕ} (hn : 1 ≤ n)
    (hε : IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) :
    Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n := by
  by_contra hnpi
  have hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
  have hXp : Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) := hq.1
  have hmod : 2 ^ n % 3 ≠ 0 := fun h0 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))
    omega
  have hmin : (2 ^ n % 3 = 2 ∧ Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∨
      (2 ^ n % 3 = 1 ∧ 2 < 2 ^ n ∧ Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃*
        CFSG.Assembly.RankThreeEven.projSU 3 2 n)) := by
    rcases hε with hL | ⟨h2, hU⟩
    · refine Or.inl ⟨?_, hL⟩
      by_contra h1
      exact hnpi (Or.inl ⟨by omega, hL⟩)
    · refine Or.inr ⟨?_, h2, hU⟩
      by_contra h1
      exact hnpi (Or.inr ⟨by omega, hU⟩)
  obtain ⟨hs, -, -⟩ := Main148.isSimpleGroup_of_eps hXp hn hmin
  have hO : CFSG.pPrimeCore 3 ↥X = CFSG.pCore 2 ↥X :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isSimpleGroup hs
      (Proof1515.three_dvd_card_of_mem_scriptY4 hX))
  let eX : (↥X ⧸ CFSG.pPrimeCore 3 ↥X) ≃* (↥X ⧸ CFSG.pCore 2 ↥X) :=
    QuotientGroup.quotientMulEquivOfEq hO
  have hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
    lB_eq_bot_of_not_allPointsHJ' h134 h48 h hNHJ hB
  have hAc : IsMulCommutative ↥A := h.toSec13Data.isElemAbelian.1
  have hYB : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) X B := fun B hB =>
    yBOne_of_lB_eq_bot hAc hB (hLB B hB)
  obtain ⟨f, -, hf⟩ := exists_hyperplanes_thirteen h.isE27
  have hXΔ : X = deltaZero A (lB A) X :=
    rank3II_15_1_lB h.isE27 ⟨f 0, hf 0, hLB _ (hf 0)⟩ hX
  have hXs : ¬ Group.IsSolvable ↥X := by
    intro hsol
    have : Nontrivial (↥X ⧸ CFSG.pCore 2 ↥X) := hs.toNontrivial
    exact Group.IsPerfect.not_isSolvable (↥X ⧸ CFSG.pCore 2 ↥X) inferInstance
  have hcore : ¬ ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ X ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({b} : Set G)) := by
    intro hc
    have h1 : Case148One A (lB A) X := case148One_of_core hCore h hX.1 hXs hYB hc
    have h1' : deltaZero A (lB A) X ≤ pPrimeCoreOf 3 X := h1
    rw [← hXΔ] at h1'
    apply Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hX
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1' y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h X hX.1 hXs hYB B hB Q hQ hQY b hb hb1 hQb
  let := ker148_normal hX.1.2
  have hkt : KType148 A X e K Le := hKT G A c L h X hX.1 hXs hYB B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (X ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L h X hX.1 hXs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h.chosen136 hkt)
  have h3K : 3 ∣ Nat.card ↥(img148 A X K) := Main148.three_dvd_card_img148_of_types h hkt.2
  obtain ⟨hJXle, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  have hKX : K ≤ X := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  obtain ⟨eK⟩ := Y4Core.nonempty_img148_equiv_map hX.1.2 hKX
  obtain ⟨eJ⟩ := Y4Core.nonempty_img148_equiv_map hX.1.2 hJXle
  have hJtop : (J.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) = ⊤ := by
    have hs' : IsSimpleGroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
      have := hs
      exact eX.isSimpleGroup
    rcases (hJ'.2.1.map (QuotientGroup.mk'_surjective _)).eq_bot_or_top_of_isSimpleGroup hs' with
      hbot | htop
    · exfalso
      have hK1 : (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) = ⊥ :=
        le_bot_iff.mp ((Subgroup.map_mono (Subgroup.subgroupOf_mono X hKJ)).trans hbot.le)
      have hc := Nat.card_congr eK.toEquiv
      rw [hK1, Subgroup.card_bot] at hc
      rw [hc] at h3K
      omega
    · exact htop
  have eJX : ↥(img148 A X J) ≃* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (eJ.trans (MulEquiv.subgroupCongr hJtop)).trans (Subgroup.topEquiv.trans eX)
  have hA7 := KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hA10 := KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2
  rcases halt with hEq | ⟨-, ⟨φ⟩⟩ | ⟨m, hm, -, hJπ, -⟩ | hD
  ·
    have eKX : ↥(img148 A X K) ≃* ↥X ⧸ CFSG.pCore 2 ↥X :=
      (MulEquiv.subgroupCongr hEq).trans eJX
    rcases hkt.2 with ⟨heΩ, hLeA, hφ | ⟨-, ⟨φ⟩⟩ | ⟨p, f', e', hp, hf', he', hiso, hL3⟩⟩ |
        ⟨-, ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩⟩
    ·
      obtain ⟨φ⟩ := hφ
      have ψ : ↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le := eKX.symm.trans φ
      rcases (h.chosen136.2 e heΩ Le hLeA).1 with ⟨⟨χ⟩⟩ | ⟨p, e'', hp, he'', hiso⟩ | ⟨⟨χ⟩⟩ |
          ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
      · exact KFacts.KS14.not_isLThreeEpsAt_j2 2 n (IsLThreeEpsAt.of_mulEquiv (ψ.trans χ) hε)
      · exact hnpi (isoLThreePi_two_of_isoLThreePi (hp := hp) hXp hn he'' hε
          (Proof1515.isoLThreePi_congr ψ.symm hiso))
      · exact Item148Rank.not_isLThreeEpsAt_of_card_2520
          ((Nat.card_congr (ψ.trans χ).toEquiv).trans hA7) 2 n hε
      · exact KFacts.KS14.not_isLThreeEpsAt_M22 2 n (IsLThreeEpsAt.of_mulEquiv (ψ.trans χ) hε)
      · exact KFacts.KS14.not_isLThreeEpsAt_M12 2 n (IsLThreeEpsAt.of_mulEquiv (ψ.trans χ) hε)
    ·
      exact Item148Rank.not_isLThreeEpsAt_of_card_2520
        ((Nat.card_congr (eKX.symm.trans φ).toEquiv).trans hA7) 2 n hε
    ·
      have hKπ := hσ G A c L h X hX.1 hXs hYB B Q e K Le hP hkt.1 heΩ hLeA p f' e' hp hf' he'
        hiso hL3
      exact hnpi (isoLThreePi_two_of_isoLThreePi (hp := hp) hXp hn hf' hε
        (Proof1515.isoLThreePi_congr eKX hKπ))
    ·
      exact Item148Rank.not_isLThreeEpsAt_of_card_2520
        ((Nat.card_congr (eKX.symm.trans φ).toEquiv).trans hA7) 2 n hε
    ·
      have h7 : Sec4.IsoLThreePi ↥(img148 A X K) 7 1 := Or.inl ⟨by norm_num, ⟨φ⟩⟩
      exact hnpi (isoLThreePi_two_of_isoLThreePi (hp := hp7) hXp hn le_rfl hε
        (Proof1515.isoLThreePi_congr eKX h7))
  ·
    exact not_isLThreeEpsAt_two_of_card_a10
      ((Nat.card_congr (eJX.symm.trans φ).toEquiv).trans hA10) hn hε
  ·
    exact hnpi (isoLThreePi_two_of_isoLThreePi hXp hn (by omega) hε
      (Proof1515.isoLThreePi_congr eJX hJπ))
  ·
    exact hD4 G A c L h X hX.1 hXs hYB B Q e K Le hP hkt heA J hJ hKJ hAJ hD

end Proof154Pi

theorem y4LThreePiNHJR_of
    (h134 : Item134) (h48 : Sec4.Item4_8) (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4) (hσ : Step148KTypeSigma) :
    Y4LThreePiNHJR :=
  fun _ _ _ _ _ _ hR hNHJ _ hX _ hn hε =>
    Proof154Pi.isoLThreePi_of_mem_scriptY4 h134 h48 hCore hPoint hKT hLift hD4 hσ
      hR.toSec14Std hNHJ hX hn hε

end CFSG.RankThree.PartTwo.Sec15
