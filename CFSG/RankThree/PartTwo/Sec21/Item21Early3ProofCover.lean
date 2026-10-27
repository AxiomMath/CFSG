module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofCenterOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Certificate8095
import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
import CFSG.RankThree.PartTwo.Census.TransitiveLift
import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverJ3
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.LieType.Simplicity.Classical
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.PartTwo.Sec14.Item145Bot

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

namespace Item21Early3Proof

open Item21EarlyProof Item21Early2Proof

section Covers

variable {J : Type} [Group J] [Finite J]

omit [Finite J] in
@[expose] noncomputable def coverMap {S : Type*} [Group S] (e : J ⧸ Subgroup.center J ≃* S) :
    J →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))

omit [Finite J] in
theorem coverMap_surjective {S : Type*} [Group S] (e : J ⧸ Subgroup.center J ≃* S) :
    Function.Surjective (coverMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite J] in
theorem coverMap_ker {S : Type*} [Group S] (e : J ⧸ Subgroup.center J ≃* S) :
    (coverMap e).ker = Subgroup.center J := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk x) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

theorem exists_central_involution (hZ2 : IsPGroup 2 (Subgroup.center J))
    (hZnt : Nontrivial (Subgroup.center J)) :
    ∃ z ∈ Subgroup.center J, z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
    (Sec4.Census.two_dvd_card_center hZ2 hZnt)
  refine ⟨z, z.2, ?_, ?_⟩
  · intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rw [← Subgroup.orderOf_coe] at hz
    rw [← hz]
    exact pow_orderOf_eq_one _

theorem four_le_pRank_of_isTwoCover_m22 (h : Sec4.Census.IsTwoCover J NativeSporadic.M22) :
    4 ≤ CFSG.pRank 2 J := by
  obtain ⟨-, hZ2, hZnt, ⟨e⟩⟩ := h
  obtain ⟨z, hz, hz1, hz2⟩ := exists_central_involution hZ2 hZnt
  have hzk : coverMap e z = 1 := by rw [← MonoidHom.mem_ker, coverMap_ker]; exact hz
  exact Sec4.Census.DoubleCoverLift.E8Datum.four_le_pRank
    Sec4.Census.DoubleCoverRanks.m22_e8Datum (coverMap_surjective e) (coverMap_ker e).le hzk hz1 hz2

theorem five_le_pRank_of_isTwoCover_j3
    (h : Sec4.Census.IsTwoCover J NativeSporadic.J3) : 5 ≤ CFSG.pRank 2 J := by
  obtain ⟨-, hZ2, hZnt, ⟨e⟩⟩ := h
  obtain ⟨z, hz, hz1, hz2⟩ := exists_central_involution hZ2 hZnt
  have hzk : coverMap e z = 1 := by rw [← MonoidHom.mem_ker, coverMap_ker]; exact hz
  obtain ⟨a₁, a₂, a₃, a₄, n, hd⟩ := Sec4.Census.SporadicTwoCover.j3_e16Datum
  exact hd.five_le_pRank (coverMap_surjective e) (coverMap_ker e).le hzk hz1 hz2

theorem le_pRank_of_isTwoCover_psl3 {n : ℕ} (hn : 2 ≤ n)
    (h : Sec4.Census.IsTwoCover J (projSL 3 (GaloisField 2 n))) : n + 1 ≤ CFSG.pRank 2 J := by
  obtain ⟨-, hZ2, hZnt, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hq4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  set φ := coverMap e with hφdef
  have hφ := coverMap_surjective e
  have hk : φ.ker ≤ Subgroup.center J := (coverMap_ker e).le
  have hK3 : 3 ≤ Nat.card (GaloisField 2 n) := by rw [hK]; omega
  obtain ⟨A, hA, hcard⟩ := Sec4.Census.TransitiveLift.exists_isElementaryAbelian_card hφ hk
    (W := (Sec4.Census.DoubleCoverRanksTwo.rootHom (K := GaloisField 2 n)).range)
    (fun y y' hy hy' => Sec4.Census.DoubleCoverRanksTwo.commute_lift_rootHom hφ hk hy hy')
    (fun y hy => by
      obtain ⟨a, ha⟩ := hy
      exact Sec4.Census.DoubleCoverRanksTwo.exists_sq_eq_sq_E hφ hk hK3
        (ha ▸ Sec4.Census.DoubleCoverRanksTwo.rootHom_mem_range_uHom a))
  obtain ⟨z, hz, hz1, hz2⟩ := exists_central_involution hZ2 hZnt
  have hzk : φ z = 1 := by rw [← MonoidHom.mem_ker, coverMap_ker]; exact hz
  have hΩ : 2 ≤ Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := by
    have : Nontrivial {c : J // φ c = 1 ∧ c ^ 2 = 1} :=
      ⟨⟨⟨1, map_one φ, one_pow 2⟩, ⟨z, hzk, hz2⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  refine Sec4.Census.TransitiveLift.le_pRank_of_card hA ?_
  rw [hcard, Sec4.Census.DoubleCoverRanksTwo.card_range_rootHom, hK, pow_succ]
  exact Nat.mul_le_mul le_rfl hΩ

end Covers

variable {X : Type} [Group X] [Finite X]

theorem center_cases_of_isBar211
    (h : IsBar211 X)
    (h3 : 3 ∣ Nat.card (Subgroup.center X)) :
    Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.M22) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Even n ∧
        Nonempty (X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField 2 n))) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.J3) := by
  have hbot : Subgroup.center X ≠ ⊥ := by
    intro hZ
    rw [hZ, Subgroup.card_bot] at h3
    norm_num at h3
  unfold IsBar211 at h
  rcases h with h | h | h | h | h | h | h | h | h |
      ⟨n, hn, he, h | h | hG | hD | h | h⟩ | h | ⟨n, hn, hno, h⟩ | h | h |
      h | h | h
  ·
    exact Or.inl h.2
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.M22) e center_nativeM22_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.M23) e center_nativeM23_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.HS) e center_nativeHS_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.M24) e center_nativeM24_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.He) e center_nativeHe_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.J2) e center_nativeJ2_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.Ru) e center_nativeRu_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.J4) e center_nativeJ4_eq_bot)
      hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSL_three_eq_bot hn he)) hbot
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    obtain ⟨f⟩ := nonempty_quot_SL3 n
    exact Or.inr (Or.inl ⟨n, hn2, he, ⟨(quotCenterCongr e).trans f⟩⟩)
  ·
    exact absurd (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hG).1 hbot
  ·
    exact absurd (CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions hD).1 hbot
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSp_two_eq_bot hn2)) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSU_four_eq_bot (by omega))) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e Sec4.Item434SmallTwoOther.U54.center_U54) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSU_four_eq_bot (by omega))) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.J3) e center_nativeJ3_eq_bot)
      hbot
  ·
    exact Or.inr (Or.inr h.2)
  ·
    have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    refine absurd (center_eq_bot_of_isSimpleGroup_of_not_prime ?_) hbot
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
      show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide]
    norm_num
  ·
    have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
    refine absurd (center_eq_bot_of_isSimpleGroup_of_not_prime ?_) hbot
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
      show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
    norm_num
  ·
    have : IsSimpleGroup X :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 3 2 1 h
    refine absurd (center_eq_bot_of_isSimpleGroup_of_not_prime ?_) hbot
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl,
      show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide]
    norm_num

end Item21Early3Proof

end CFSG.RankThree.PartTwo.Sec21
