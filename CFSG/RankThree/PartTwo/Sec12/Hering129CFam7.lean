module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamE9
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL52
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowESp6

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo

namespace Hering129C

theorem not_twentySeven_dvd_card_projSL_five_two :
    ¬ 27 ∣ Nat.card (projSL 5 (GaloisField 2 1)) := by
  rw [← Nat.card_congr Sec4.Res417Four.gl5EquivProjSL.toEquiv]
  exact Sec4.RonanK432.not_27_dvd_card_gl5

theorem not_twentySeven_dvd_card_projSU_five_four : ¬ 27 ∣ Nat.card (projSU 5 2 2) := by
  rw [Sec4.Item434SmallTwoOther.U54.card_U54]
  norm_num

theorem kFCensus46Seven_L52_U54 : KFCensusOn (fun Q _ =>
    Nonempty (Q ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (Q ≃* projSU 5 2 2)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  refine (ppair_self hD).false_of_not_dvd ?_
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    exact not_twentySeven_dvd_card_projSL_five_two
  · rw [Nat.card_congr e.toEquiv]
    exact not_twentySeven_dvd_card_projSU_five_four

theorem kFCensus46Seven_Sp62 :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* projSp 3 (GaloisField 2 1))) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨e0⟩ := hQ
  let e : Q ≃* Census.Carrier.Sp6Two.H6 := e0.trans Sec4.Item434SmallTwoIII.sp62Equiv
  have hZ : Subgroup.center Q = ⊥ := by
    refine census_center_eq_bot hD fun z hz hz3 => ?_
    have hcomm : e z * Sec4.RonanK429E.Sp6.y0 = Sec4.RonanK429E.Sp6.y0 * e z := by
      have := Subgroup.mem_center_iff.mp hz (e.symm Sec4.RonanK429E.Sp6.y0)
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
      exact this.symm
    have h1 : e z = 1 :=
      Sec4.RonanK429E.Sp6.eq_one_of_commute_y0 (e z) hcomm (by rw [← map_pow, hz3, map_one])
    exact e.injective (h1.trans (map_one e).symm)
  obtain ⟨hDe, hD9, hmax⟩ := census_maximal_E9 hD hZ e
  exact Sec4.Res417Four.false_of_card_nine hDe hD9 hmax

theorem kFCensus46Seven_holds : KFCensus46Seven := by
  intro Q Lb _ _ _ c a I X f hQ hD
  rcases hQ with h | h | h
  · exact kFCensus46Seven_L52_U54 Q Lb c a I X f (Or.inl h) hD
  · exact kFCensus46Seven_Sp62 Q Lb c a I X f h hD
  · exact kFCensus46Seven_L52_U54 Q Lb c a I X f (Or.inr h) hD

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
