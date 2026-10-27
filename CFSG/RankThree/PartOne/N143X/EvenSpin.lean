module

public import CFSG.RankThree.PartOne.N143X.EvenExcl
import CFSG.RankThree.PartOne.CTP.SpinRankFour
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.Census3 TauCeti

theorem false_of_pomegaPlus_large {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hmod : StatedClassicalModel X .POmegaPlus n 2 f) (hn : 5 ≤ n) (he : evenRank X ≤ 3) :
    False := by
  have hf : 0 < f := hmod.1.2.1
  let q : PrimePower := ⟨2, f, Nat.prime_two, hf⟩
  have hv : (LieTypeIndex.D n q).Valid :=
    (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 (show 4 ≤ n by omega),
      by simp [LieTypeIndex.isDuplicateRepresentative_iff]⟩
  have hcar := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv
    rfl (MulEquiv.refl (ValidLieTypeIndex.Group ⟨.D n q, hv⟩))
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hmod hcar
  exact false_of_four_le_carrier e he
    (CFSG.RankThree.PartOne.CTP.spinRankFour.typeD n q hv (by simp [q]; omega))

theorem false_of_pomegaMinus_large {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hmod : StatedClassicalModel X .POmegaMinus n 2 f) (hn : 5 ≤ n) (he : evenRank X ≤ 3) :
    False := by
  have hf : 0 < f := hmod.1.2.1
  let q : PrimePower := ⟨2, f, Nat.prime_two, hf⟩
  have hv : (LieTypeIndex.twistedD n q).Valid :=
    (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 (show 4 ≤ n by omega),
      by simp [LieTypeIndex.isDuplicateRepresentative_iff]⟩
  have hcar := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even
    n q hv rfl (MulEquiv.refl (ValidLieTypeIndex.Group ⟨.twistedD n q, hv⟩))
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hmod hcar
  exact false_of_four_le_carrier e he
    (CFSG.RankThree.PartOne.CTP.spinRankFour.typeTwistedD n q hv (by simp [q]; omega))

end CFSG.RankThree.PartOne.N143X
