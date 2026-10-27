module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

structure FormData (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (Qf : QuadraticForm K (ι → K)) : Prop where
  card : Fintype.card ι = 4
  natIrr : NatIrredFor K ⇑Qf
  dickson : DicksonNatFor K ⇑Qf
  normalizer : NormalizerOmegaFor K ⇑Qf
  omega : Omega4BasicFor K ⇑Qf
  index : Nat.card (CFSG.MatrixModel.isometryCore ⇑Qf) = 2 * Nat.card (StatedOmega ⇑Qf)
  comm : ∀ P : Subgroup (GL ι K), P ≤ StatedOmega ⇑Qf → IsPGroup 2 P →
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x
  noSwap : ∀ A : Subgroup (GL ι K), A ≤ StatedOmega ⇑Qf → A ≠ ⊥ →
    (∀ g ∈ StatedOmega ⇑Qf, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
    A = StatedOmega ⇑Qf ∨
      ∀ ω ∈ CFSG.MatrixModel.isometryCore ⇑Qf, (∀ a ∈ A, ω * a * ω⁻¹ ∈ A) →
        ω ∈ StatedOmega ⇑Qf
  transv : ∃ r ∈ CFSG.MatrixModel.isometryCore ⇑Qf, r * r = 1 ∧
    Matrix.rank (((r : GL ι K) : Matrix ι ι K) - 1) = 1

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
