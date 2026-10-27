module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofLoc
public import CFSG.RankThree.PartTwo.Sec17.Item17ResProof1724
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofPts
import CFSG.RankThree.PartTwo.Sec17.Item17ResProofX
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof17Res9

variable {G : Type} [Group G] [Finite G]

theorem exists_envelope_of_not_three_dvd {A : Subgroup G} {p : ℕ} (hp : p.Prime)
    {Y : Subgroup G} (h3 : ¬ 3 ∣ Nat.card (oPrimeResidualOf p (delta A (lB A) Y))) :
    ∃ R : Subgroup G, R ≤ Y ∧ A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
      ∀ S' ∈ scriptQPiStar A (lB A) Y (piOf p), S' ≤ R := by
  have : Fact p.Prime := ⟨hp⟩
  have hAD : A ≤ Subgroup.normalizer ((delta A (lB A) Y : Subgroup G) : Set G) :=
    le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  refine ⟨oPrimeResidualOf p (delta A (lB A) Y),
    (oPrimeResidualOf_le_self p _).trans (delta_le Y), le_normalizer_oPrimeResidualOf hAD, h3,
    fun S' hS' => ?_⟩
  have hSp : IsPGroup p S' := isPGroup_of_mem_scriptQPi hp hS'.prop
  have hSD : S' ≤ delta A (lB A) Y := le_delta hS'.prop.1.1 hS'.prop.1.2
  rw [oPrimeResidualOf_eq_closure]
  intro x hx
  obtain ⟨k, hk⟩ := hSp ⟨x, hx⟩
  exact Subgroup.subset_closure ⟨hSD hx, k, by simpa using congrArg Subtype.val hk⟩

theorem exists_envelope_centralizer_c
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({c} : Set G) ∧
      A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
      ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({c} : Set G)) (piOf p), S' ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have h14 : Sec14Std G A c L := hs.toSec14Std
  have hD13 : Sec13Data G A c L := hs.toSec13Data
  have hA : Late.IsE27 A := h14.isE27'
  have hcA : c ∈ A := hD13.mem_A
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hJ2, h9, hAc, -, -, -⟩ := hs.j2_local hJ
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set X := xA A with hXdef
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := centralizer_le_normalizer_of_three_dvd h14 h3L
  have hAC : A ≤ C := fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm z hz c hcA)
  have hXC : X ≤ C :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := hXC.trans hCL
  have hX3 : ¬ 3 ∣ Nat.card X :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD13.mem_lA.2.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1).trans
      (le_normalizer_pPrimeCoreOf 3 _)
  refine ⟨(L ⊔ X) ⊓ cQuot L ⊓ C, inf_le_right, ?_, ?_, ?_⟩
  · exact Late.le_normalizer_inf (Late.le_normalizer_inf (Sec14.le_normalizer_sup hAL hAX)
      (hAL.trans (Proof17Res.le_normalizer_cQuot L))) (hAC.trans Subgroup.le_normalizer)
  · intro h3
    exact not_three_dvd_card_sup_inf_cQuot hJ2 le_rfl hXL hXL hX3
      (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  · intro S' hS'
    have hS'C : S' ≤ C := hS'.prop.1.2
    have hS'Q : S' ∈ scriptQ A (lB A) := hS'.prop.1.1
    have hS'p : IsPGroup p S' := isPGroup_of_mem_scriptQPi hp hS'.prop
    have hAS' : A ≤ Subgroup.normalizer (S' : Set G) := hS'Q.1.2.2
    have hS'LX : S' ≤ L ⊔ X :=
      Sec14.Item148Point.le_sup_of_eq_zpowers_sup142 h14 hAc
        ⟨hS'C.trans (Sec14.centralizer_singleton_le_normalizer_zpowers c), hS'Q.1.2.1, hAS'⟩
    have hS'Q' : S' ≤ cQuot L := le_cQuot_of_j2 hJ2 hp hp3 hS'p (hS'C.trans hCL) inf_le_right
      (hA.isPGroup.to_le inf_le_left) h9 (inf_le_left.trans hAS')
    exact le_inf (le_inf hS'LX hS'Q') hS'C

end Proof17Res9

open Proof17Res9 in
theorem item1724LocR_of
    (h1721 : Item1721) (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hbal : Step143Balance)
    (hnorm : Item1724NormThreePrime) : Item1724LocR := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h Y hY
  have hs := h.toSec17Std
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨hΩ, -, -⟩ := rank3II_17_15_HJ_of hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hJ
  by_cases h3 : 3 ∣ Nat.card (oPrimeResidualOf p (delta A (lB A) Y))
  swap
  · exact exists_envelope_of_not_three_dvd h.p_prime h3
  rcases hY with ⟨D, hD, hD1, rfl⟩ | ⟨a, ha, ha1, rfl⟩
  · exact hnorm G A c L Y₀ Y₁ S p P w Q h hJ D hD hD1 h3
  · by_cases haΩ : Subgroup.zpowers a ∈ omegaA A
    · have hac : Subgroup.zpowers a = Subgroup.zpowers c := by
        rw [hΩ] at haΩ
        exact haΩ
      rw [centralizer_singleton_eq_of_zpowers_eq hac]
      exact exists_envelope_centralizer_c hs hJ h.p_prime h.three_lt_p
    · by_cases hsp : ∃ B, IsHyperplane A B ∧ a ∈ B ∧ lB A B ≠ ⊥
      · obtain ⟨B, hB, haB, hLB⟩ := hsp
        exact exists_threePrime_envelope hbal hs hΩ hJ h.p_prime h.three_lt_p ha ha1 haΩ hB haB
          hLB
      · push Not at hsp
        exfalso
        have hΔ := Sec14.delta_eq_sup_of_lB_eq_bot hbal h.toSec14Std ha ha1 haΩ hsp
        have hΔ3 : ¬ 3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) := by
          rw [hΔ]
          exact Proof176Steps.not_three_dvd_card_sup
            (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
        exact hΔ3 (h3.trans (Subgroup.card_dvd_of_le (oPrimeResidualOf_le_self p _)))

end CFSG.RankThree.PartTwo.Sec17
