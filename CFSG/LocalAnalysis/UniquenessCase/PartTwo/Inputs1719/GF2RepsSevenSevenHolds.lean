module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenATwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenBStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped commutatorElement Pointwise

theorem w4Lem7_7_of_not_normalizer_le_centralizer {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y K A : Subgroup (MulAut W)} {k : ℕ} [Finite ↥K]
    (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hlt : ∀ n, Nonempty (ACandidate ↥K n) → n < k)
    (hNC : ¬ A ⊓ Subgroup.normalizer (K : Set (MulAut W)) ≤
      Subgroup.centralizer (K : Set (MulAut W))) : ⁅A, K⁆ = ⊥ := by
  exfalso
  obtain ⟨U, _, _, hU, Y', hLn, hLq, ⟨f, hf⟩, hk⟩ :=
    SevenSevenBStar.w4Lem7_7_caseB_data hW hK hA hNC
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2
  have h := hlt _ (nonempty_aCandidate_of_surjective hKq hU Y' hLn hLq f hf)
  omega

theorem w4Lem7_7_holds : W4Lem7_7 := by
  intro W _ _ hW Y K A k hK hA hlt
  have hKfin : Finite ↥K := Finite.of_injective (fun x : ↥K => ((x : MulAut W) : W → W))
    (fun x y h => Subtype.ext (DFunLike.ext _ _ (congrFun h)))
  by_cases hNC : A ⊓ Subgroup.normalizer (K : Set (MulAut W)) ≤
      Subgroup.centralizer (K : Set (MulAut W))
  · exact w4Lem7_7_of_normalizer_le_centralizer hW hK hA hlt hNC
  · exact w4Lem7_7_of_not_normalizer_le_centralizer hW hK hA hlt hNC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
