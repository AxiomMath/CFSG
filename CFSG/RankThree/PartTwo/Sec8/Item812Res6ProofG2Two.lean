module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.FFC2G2

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Item812Res6

theorem isPerfect_of_isSimpleGroup_of_not_comm {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ∃ x y : S, x * y ≠ y * x) : Group.IsPerfect S := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · obtain ⟨x, y, hxy⟩ := hnc
    exact (hxy (((commutator_eq_bot_iff S).mp h).is_comm.comm x y)).elim
  · exact h

end Item812Res6


theorem kFG2TwoNonsolv_holds : KFG2TwoNonsolv := by
  intro K _ _ hK
  set H := CFSG.Blueprint.Chevalley.adjointGroup .G2 K
  obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK
  obtain ⟨hs, hnc, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hK (Subgroup.topEquiv.trans E)
  have hP : Group.IsPerfect ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
    Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
  have hle := Item87Res2Proof.le_perfectResidual_of_isPerfect hP
  intro h0
  rw [h0, le_bot_iff] at hle
  have : Nontrivial ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ := IsSimpleGroup.toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this hle

theorem kF87UnitaryJ_holds : KF87UnitaryJ :=
  kF87UnitaryJ_of kFG2TwoNonsolv_holds

end CFSG.RankThree.PartTwo.Sec8
