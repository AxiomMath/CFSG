module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Quasithin CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem j4M2Residual :
    J4M2Residual := by
  have hF : J4Facts := j4Facts
  intro B hB hBM h1 h2
  rcases J4M2.J4M2Lattice hF (le_sup_right : P0 ≤ B ⊔ P0) hBM with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · have hB' : B ∈ cComp (B ⊔ P0) := hB
    rw [h] at hB'
    exact J4M2.shape_of_mem_cComp_M2 hF B hB'

end CFSG.Quasithin.J4Fam
