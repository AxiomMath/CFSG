module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.H13.A7SectionRank
import CFSG.Sporadic.Bridge.M22
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
import CFSG.Open.PGLModelStated
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Alternating

public section

namespace CFSG.RankThree.PartOne.N143.T2

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank projSU)

theorem nativeM22_card_eq : Nat.card Blueprint.NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem pRank_three_le_two_A6 :
    CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) ≤ 2 :=
  (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank.2.1).le

theorem pRank_three_le_two_A7 :
    CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 7))) ≤ 2 :=
  (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank.2.2.1).le

theorem pRank_three_le_two_M22 :
    CFSG.Open.pRank 3 (⊤ : Subgroup Blueprint.NativeSporadic.M22) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hP : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP
  have hdvd : Nat.card E ∣ 443520 := by
    rw [← nativeM22_card_eq]
    exact Subgroup.card_subgroup_dvd_card E
  have hj2 : j ≤ 2 := by
    by_contra hc
    have h27 : 3 ^ 3 ∣ Nat.card E := by
      rw [hj]
      exact pow_dvd_pow 3 (by omega)
    have h := h27.trans hdvd
    norm_num at h
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num) hj2

theorem pRank_three_le_two_of_M22 {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) (e.trans b.symm)]
  exact pRank_three_le_two_M22

instance finite_projSU43 : Finite (projSU 4 3 1) := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 4) (GaloisField 3 (2 * 1))) :=
    Finite.of_injective Units.val Units.val_injective
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 4) (GaloisField 3 (2 * 1))) :=
    inferInstanceAs (Finite (Matrix.GeneralLinearGroup (Fin 4) (GaloisField 3 (2 * 1)) ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 4) (GaloisField 3 (2 * 1)))))
  exact inferInstance

end CFSG.RankThree.PartOne.N143.T2
