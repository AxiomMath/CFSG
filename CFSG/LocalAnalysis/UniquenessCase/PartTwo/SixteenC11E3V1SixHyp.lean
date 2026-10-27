module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure SixHyp {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
    (M L : Subgroup (MulAut W)) (L' : Subgroup (MulAut W')) (κ : W →* W')
    (e : ↥L' →* ↥L) : Prop where
  sq : ∀ w : W, w ^ 2 = 1
  le : L ≤ M
  mA : Nonempty (↥M ≃* MulAut ↥(alternatingGroup (Fin 6)))
  isAlt : UC22.IsAlt ↥L 6
  sum : SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) L' ⊤ ⊥
  surj : Function.Surjective κ
  esurj : Function.Surjective e
  equiv : ∀ (b : ↥L') (w : W), κ ((e b : MulAut W) w) = (b : MulAut W') (κ w)
  ker : ∀ w : W, κ w = 1 → w ∈ fixV L
  comm : commV L = ⊤
  fix : fixV L' = ⊥
  ne : κ.ker ≠ ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
