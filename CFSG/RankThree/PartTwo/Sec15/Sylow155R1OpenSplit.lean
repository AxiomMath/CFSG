module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.PGLModel

@[expose] def Res1OpenL2Type (Y : Type) [Group Y] : Prop :=
  ∃ n : ℕ, 0 < n ∧ 4 ∣ n ∧ Nonempty (Y ≃* projSL 2 (GaloisField 2 n))

@[expose] def Res1OpenSU3Type (Y : Type) [Group Y] : Prop :=
  ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (Y ≃* projSU 3 2 n)

theorem barL_cases_of_sec15R {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (hS : Sec15R G A c L) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
  (hS.chosen136.2 c hS.zpowers_mem_omegaA L hS.mem_lA).1

end CFSG.RankThree.PartTwo.Sec15
