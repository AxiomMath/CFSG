module

public import CFSG.RankThree.PartOne.NF7J.PairStmt
public import CFSG.RankThree.PartOne.PAIR22.Dich
public import CFSG.RankThree.PartOne.KF.F132Row7Frame
public import CFSG.RankThree.PartOne.K1320.RowDistinct

public section

namespace CFSG.RankThree.PartOne.NF7J

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem pairMember_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two) : PairMember := by
  intro G _ _ p A c L E h hF hF13 hT hEA _ hm7 s hs t ht hst ⟨w, hw, hsL⟩ ⟨w', hw', htL⟩
  obtain ⟨f, hf1, hpf, hmodel⟩ := hm7
  have hn8 : ¬ ∃ f' : ℕ, 1 ≤ f' ∧ p ∣ 2 ^ f' + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f' :=
    fun ⟨_, _, _, h4⟩ => K1320.not_psp_two_and_psl_four hmodel h4
  have hAt := (KF132.kf132Row7_data hGA h hF hF13 hEA hf1 hpf hmodel).1
  have hKs : KFAt p E f s :=
    KFAt.of_conj hw (hAt _ (conj_mem_reflectionSet h.prime hs hw) hsL)
  have hKt : KFAt p E f t :=
    KFAt.of_conj hw' (hAt _ (conj_mem_reflectionSet h.prime ht hw') htL)
  exact PAIR22.pair_member hS h133 h hF hF13 hT hn8 hs ht hst hw hsL (PAIR22.pairLift_of_kfAt hKs)
    (PAIR22.pairLift_of_kfAt hKt)

end CFSG.RankThree.PartOne.NF7J
