module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofDelta
public import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofHyp

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

theorem step1515HJEndFpfRLe_of_off
    (h142 : Concl142R) (hoff : Step1515HJEndFpfRBoundOff) :
    Step1515HJEndFpfRLe := by
  intro G _ _ A c L h hfree d hdA hd1 hdZ hodd
  have hD := h.sec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  set R : Subgroup G :=
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ with hRdef
  have hRL : R ≤ Subgroup.centralizer (L : Set G) :=
    Proof15Res10.commutator_le_centralizer hD.le_centralizer
  have hcent : ∀ x ∈ L, R ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hRL hr) x hx).symm
  have hdL : d ∈ L := Proof15Res4.mem_of_isZCentral hdZ
  obtain ⟨hR2, -⟩ := Proof15Res11.commutatorR_isPGroup h
  have hR3 : IsPiSubgroup (piCompl 3) R := by
    refine (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr fun h3 => ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hRQ : R ∈ scriptQ A (lB A) := by
    by_cases hΩ : ∃ F ∈ omegaA A, F ≤ A ⊓ L
    · obtain ⟨F, hF, hFAL⟩ := hΩ
      obtain ⟨-, -, b, hFb, -⟩ := id hF
      subst hFb
      have hmem := Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA
        (h142 G A c L h.sec15R) hF hR3 (Proof15Res10.le_normalizer_commutatorR h)
      rwa [inf_eq_left.mpr (hcent b (hFAL (Subgroup.mem_zpowers b)).2)] at hmem
    · push Not at hΩ
      refine Proof15Res10.commutator_mem_scriptQ h ?_
      rw [qBound, Proof1518R2.lB_eq_bot_of_forall_not_le1523 hΩ, sup_bot_eq]
      exact hoff G A c L h hfree d hdA hd1 hdZ hodd hΩ
  exact (le_delta hRQ (hcent d hdL)).trans le_sup_left

theorem step1515HJEndFpfA6A6_of_core (hC : Step1515HJEndFpfRCore) : Step1515HJEndFpfA6A6 :=
  fun G _ _ A c L h hfree d hdA hd1 hdZ hodd _ _ _ _ _ _ _ =>
    hC G A c L h hfree d hdA hd1 hdZ hodd

end CFSG.RankThree.PartTwo.Sec15
