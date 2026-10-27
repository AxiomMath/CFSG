module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33a

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {Y X : Subgroup G}

namespace Thm33a

omit [Finite G] in
theorem nearAsolvAction_of_mem_mtil (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    NearAsolvAction p A X where
  prime := hθ.prime
  odd := hθ.odd
  elemAbelian := hθ.elemAbelian
  admits := hX.1.1
  nearPSolvable := hX.1.2.2.2.1
  solvable_cen := hX.1.2.2.2.2

theorem thetaU_eq_iThetaU (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    thetaU p A θ Y X = iThetaU A X Y := by
  unfold thetaU iThetaU
  rw [usetX_eq_iUset hθ hX]

end Thm33a

theorem thetaU_mem_usetX'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaU p A θ Y X ∈ usetX p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  have hne : (iPairsY A X Y).Nonempty := by
    rw [← pairsYX_eq_iPairsY hθ hXm]
    exact hX.2
  rw [Thm33a.thetaU_eq_iThetaU hθ hXm, usetX_eq_iUset hθ hXm]
  exact iThetaU_mem_iUset (Thm33a.nearAsolvAction_of_mem_mtil hθ hXm) hne

end CFSG.SignalizerFunctorTheorem.McBride.Near
