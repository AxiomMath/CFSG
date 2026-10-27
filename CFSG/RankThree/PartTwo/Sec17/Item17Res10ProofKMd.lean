module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofKMd
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Proof17Res10

variable {G : Type} [Group G] [Finite G]

theorem omegaA_eq_of_j2 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) {b' : G} (hb'Ω : Subgroup.zpowers b' ∈ omegaA A)
    {Lb : Subgroup G} (hLb : Lb ∈ lA A b')
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    omegaA A = {Subgroup.zpowers c} := by
  rcases h1514 Y₀ hs.mem_y0Star hMeets with ⟨-, -, hΩ, -⟩ | ⟨hA7, -, hT, -⟩ |
      ⟨-, -, -, -, hno, -⟩
  · exact hΩ
  · exact ((Proof17Res7.isEmpty_j2_of_trans hs.toSec14Std hT hA7 hb'Ω hLb).false hJ.some).elim
  · exact absurd hs.le_y0 (hno Y₀ hs.mem_y0Star)

end Proof17Res10

end CFSG.RankThree.PartTwo.Sec17
