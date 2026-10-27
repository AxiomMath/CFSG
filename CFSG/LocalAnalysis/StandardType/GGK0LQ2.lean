module

public import CFSG.LocalAnalysis.StandardType.GGK0LQRows
public import CFSG.LocalAnalysis.StandardType.GGK0LQ2Adapt

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

theorem k0_coreFactor_label
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hj : A.row.D.orbits[j].qs = true) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        ((coreFactor A.setup A.iota A.a (P.repr j)) ⧸
          Subgroup.center (coreFactor A.setup A.iota A.a (P.repr j))) := by
  obtain ⟨h1, h2⟩ := CFSG.StandardType.GGK0LQ.lq_row_all hlab hpair A P j hj
  exact ⟨h1, coreFactor_label_of_rationalComponent_label A (P.repr j) h2⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
