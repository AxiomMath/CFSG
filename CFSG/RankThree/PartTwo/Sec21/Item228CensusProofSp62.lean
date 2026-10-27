module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofThreeFive
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSp62
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)

@[expose] def Census228Sp62Data : Prop :=
  ThreeFiveData228 (projSp 3 (GaloisField 2 1))

namespace Item228CensusProof

theorem isSimpleGroup_projSp_three_two : IsSimpleGroup (projSp 3 (GaloisField 2 1)) := by
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (GaloisField 2 1) 3
    (by norm_num) (Or.inr (Or.inr ⟨hK, le_rfl⟩))
  exact (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
    (StatedSp 3 (GaloisField 2 1))).symm.isSimpleGroup

theorem l2Order228_projSp_three_two : L2Order228 (projSp 3 (GaloisField 2 1)) := by
  have hcard := Item223CensusResProof.card_projSp_three_two
  have : Finite (projSp 3 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact l2Order228_of_card (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num)

end Item228CensusProof

open Item228CensusProof

theorem census228Sp62_of (h : Census228Sp62Data) : Census228Sp62 := by
  intro Y _ _ ⟨e⟩
  right
  have := isSimpleGroup_projSp_three_two
  have hS : IsSimpleGroup Y := e.isSimpleGroup
  have hcard : Nat.card Y = 1451520 := by
    rw [Nat.card_congr e.toEquiv, Item223CensusResProof.card_projSp_three_two]
  have hZ : Subgroup.center Y = ⊥ :=
    Item223CensusProof.center_eq_bot_of_isSimpleGroup (by rw [hcard]; norm_num)
  have hZ1 : Nat.card (Subgroup.center Y) ∣ 3 := by
    rw [hZ, Subgroup.card_bot]
    exact one_dvd 3
  refine noL2Normal228_of_threeFive e.toMonoidHom e.surjective ?_ hZ1
    l2Order228_projSp_three_two h
  rw [hZ]
  exact (MonoidHom.ker_eq_bot_iff _).mpr e.injective

end CFSG.RankThree.PartTwo.Sec21
