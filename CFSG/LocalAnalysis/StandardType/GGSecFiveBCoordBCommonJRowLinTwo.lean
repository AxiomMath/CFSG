module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux1
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux3
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux4
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux5
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Line
import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf

theorem ggSecFiveBNativeRow_linTwo {K : Type} [Field K] [Finite K] {d m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (hd : d = 2 * m ∨ d = 2 * m + 1) :
    GGSecFiveBNativeRow (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) 3 m
      (fun lab => lab = ⟨.A, m - 1, 2⟩) (fun lab => lab = ⟨.A, d - 3, 1⟩) := by
  classical
  have hd6 : 6 ≤ d := by omega
  have hdmle : 2 * m ≤ d := by omega
  let eK : K ≃+* F2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 1 (by norm_num) (by simpa using hK)
  let eSL : Matrix.SpecialLinearGroup (Fin d) K ≃* Matrix.SpecialLinearGroup (Fin d) F2 :=
    CFSG.ClassicalModels.specialLinearFieldEquiv eK (Fin d)
  have hcardε : Fintype.card (Fin d) =
      Fintype.card ((Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m)) := by
    rw [rootPB_phi3_dim]
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_sum]
    omega
  let ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m) :=
    Fintype.equivOfCardEq hcardε
  let τ : Multiplicative (Fin m → ZMod 3) →* Matrix.SpecialLinearGroup (Fin d) F2 :=
    CommonJRowLinTwo.ggCommonJRowLinTwo_torus ε
  have hrow2 : GGSecFiveBNativeRow (Matrix.SpecialLinearGroup (Fin d) F2) 3 m
      (fun lab => lab = ⟨.A, m - 1, 2⟩) (fun lab => lab = ⟨.A, d - 3, 1⟩) := by
    refine GGSecFiveBNativeRow.of_std (T₀ := τ.range)
      (GGSecFiveBNativeAt.of_torus τ ?_ ?_ ?_) ?_
    · exact CommonJRowLinTwo.ggCommonJRowLinTwo_hτ ε
    · intro g hg
      exact CommonJRowLinTwo.ggCommonJRowLinTwo_hsign hd hm ε g hg
    · intro f J hJ hcardJ
      rcases CommonJRowLinTwo.ggCommonJRowLinTwo_hcompDichotomy hd hm ε f hJ hcardJ with
        ⟨hsp, ⟨eJ⟩⟩ | ⟨hdense, ⟨eJ⟩⟩
      · right
        obtain ⟨hΛ, hlab⟩ := CommonJRowLinTwo.ggCommonJRowLinTwo_labelSparse hd6 eJ.symm
        exact ⟨hsp, ⟨⟨.A, d - 3, 1⟩, rfl, hΛ, hlab⟩⟩
      · left
        obtain ⟨hΛ, hlab⟩ := CommonJRowLinTwo.ggCommonJRowLinTwo_labelDense hm eJ.symm
        refine ⟨hdense, ⟨⟨.A, m - 1, 2⟩, rfl, hΛ, hlab, ?_⟩⟩
        intro hEq
        exact absurd (congrArg LargeEvenLabel.tag hEq) (by
          intro h
          cases h)
    · intro E hE hEcard
      obtain ⟨g, hg⟩ := CommonJRowLinTwo.ggCommonJRowLinTwo_hconj hd hm ε hE hEcard
      exact ⟨MulAut.conj g, hg⟩
  have hrowK : GGSecFiveBNativeRow (Matrix.SpecialLinearGroup (Fin d) K) 3 m
      (fun lab => lab = ⟨.A, m - 1, 2⟩) (fun lab => lab = ⟨.A, d - 3, 1⟩) :=
    GGSecFiveBNativeRow.of_mulEquiv eSL.symm hrow2
  exact GGSecFiveBNativeRow.of_mulEquiv (LineL2.recipeEquivTwo hK).symm hrowK

end CFSG.StandardType

end
