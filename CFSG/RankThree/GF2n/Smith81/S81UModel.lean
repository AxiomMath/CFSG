module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Smith81.S81UModelData

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

section Act

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]
  {e : K ≃+* Fσ σ}

@[expose] def e3uVal (w : E3UWspace σ e) : Cube F := ((show Wform σ from w : Wform σ) : Cube F)

theorem e3uWact_val (g : SUid σ 6) (w : E3UWspace σ e) :
    e3uVal (e3uWact σ e g w) = rho F (g : GL (Fin 6) F) (e3uVal w) := rfl

theorem e3uWact_eq_one_iff (hσ : IsUnitaryInvolution σ) (g : SUid σ 6) :
    e3uWact σ e g = 1 ↔ ∃ l : F, l ^ 3 = 1 ∧ ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = l • 1 := by
  refine Iff.trans ?_ (U6Cube.Wact_eq_one_iff hσ g)
  constructor
  · intro h
    refine LinearEquiv.ext fun w => ?_
    exact LinearEquiv.congr_fun h (show E3UWspace σ e from w)
  · intro hW
    refine LinearEquiv.ext fun w => ?_
    exact LinearEquiv.congr_fun hW (show Wform σ from w)

end Act

end CFSG.RankThree.GF2n.Smith81
