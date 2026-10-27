module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Defs
import CFSG.RankThree.PartTwo.Sec11.Item116R2ZNum
import CFSG.RankThree.PartTwo.Sec11.Item116R2ZL2
import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3
import CFSG.RankThree.PartTwo.Sec11.SimsR1L38SolvableA
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

theorem zNumeric_psl2 {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp3 : p ≠ 3) {A B : ℕ}
    (hA : A = Nat.card (projSL 2 (GaloisField p (3 * e))))
    (hB : B = Nat.card (projSL 2 (GaloisField p e))) :
    9 ∣ A ∧ B.factorization 3 < A.factorization 3 := by
  have hcardK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hcardK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), ← pow_mul, mul_comm]
  have hq2 : 2 ≤ p ^ e := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p)
  have h3 : ¬ 3 ∣ p ^ e := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  refine three_adic_L2 hq2 h3 ?_ ?_
  · have h := KSListsProof.card_projSL_two_mul (GaloisField p (3 * e))
    rw [hcardK3] at h
    rw [hA]
    exact h
  · have h := KSListsProof.card_projSL_two_mul (GaloisField p e)
    rw [hcardK] at h
    rw [hB]
    exact h

theorem zNumeric_L38 {A B : ℕ} (hA : A = Nat.card (projSL 3 (GaloisField 2 3)))
    (hB : B = Nat.card (projSL 3 (GaloisField 2 1))) :
    9 ∣ A ∧ B.factorization 3 < A.factorization 3 := by
  have hA' : A = 16482816 := by
    rw [hA]
    exact SimsR1.L38Solvable.card_projSL_three_eight
  have hB' : B = 168 := by
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 1)
    rw [GaloisField.card 2 1 (by norm_num)] at h
    rw [← hB] at h
    norm_num at h
    omega
  have h9 : 9 ∣ A := by rw [hA']; norm_num
  refine ⟨h9, ?_⟩
  have hA0 : A ≠ 0 := by rw [hA']; norm_num
  have h2A : 2 ≤ A.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hA0).1 (by simpa using h9)
  have hB0 : B ≠ 0 := by rw [hB']; norm_num
  have hnB : ¬ 2 ≤ B.factorization 3 := fun h =>
    absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hB0).2 h)
      (by rw [hB']; norm_num)
  omega

theorem zNumeric_of_surviving {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L)
    (hS : IsSurvivingCase L) :
    9 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∧
      (Nat.card (fixedSub (thetaQuotMulAut L (compAction L ⟨a, ha⟩)))).factorization 3 <
        (Nat.card (L ⧸ aschbacherSolvableCore 3 L)).factorization 3 := by
  set α : MulAut (L ⧸ aschbacherSolvableCore 3 L) := thetaQuotMulAut L (compAction L ⟨a, ha⟩)
    with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, ← map_pow]
    have h1 : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext ha3
    rw [h1, map_one, map_one]
  have hαi : α ∉ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
    obtain ⟨hx, h⟩ := hout
    exact h
  have hα1 : α ≠ 1 := fun h => hαi ⟨1, by rw [map_one, h]⟩
  have hαo : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  rcases hS with ⟨m, hm, ⟨e⟩⟩ | hL3 | ⟨p, hp, hp3, ⟨e⟩⟩
  · obtain ⟨ef⟩ := nonempty_fixedSub_equiv_L2 (p := 2) (e := m) (by omega) ⟨e⟩ hαo hαi
    exact zNumeric_psl2 (p := 2) (e := m) (by omega) (by norm_num)
      (Nat.card_congr e.toEquiv) (Nat.card_congr ef.toEquiv)
  · obtain ⟨eL⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 3)) := by
      rcases hL3 with ⟨h1, -⟩ | ⟨-, h2⟩
      · norm_num at h1
      · exact h2
    have hfix := SimsR1.FieldCent.isoLThreeMinusPi_fixedSub (m := 1) le_rfl hL3 hαo hαi
    obtain ⟨ef⟩ : Nonempty (fixedSub α ≃* projSL 3 (GaloisField 2 1)) := by
      rcases hfix with ⟨h1, -⟩ | ⟨-, h2⟩
      · norm_num at h1
      · exact h2
    exact zNumeric_L38 (Nat.card_congr eL.toEquiv) (Nat.card_congr ef.toEquiv)
  · haveI := hp
    obtain ⟨ef⟩ := nonempty_fixedSub_equiv_L2 (p := p) (e := 1) le_rfl ⟨e⟩ hαo hαi
    exact zNumeric_psl2 (p := p) (e := 1) le_rfl (by omega)
      (Nat.card_congr e.toEquiv) (Nat.card_congr ef.toEquiv)

end CFSG.RankThree.PartTwo.Sec11
