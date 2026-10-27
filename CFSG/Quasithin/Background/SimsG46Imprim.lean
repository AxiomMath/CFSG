module

public import CFSG.Quasithin.Background.SimsG4Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CFSG.Quasithin.Background.SimsG46ImprimTwo
import CFSG.Quasithin.Background.SimsG46ImprimFour

public section

namespace CFSG.Quasithin.SimsG4

open G46Imprim in
theorem not_connected_of_imprimitive {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty) (himp : IsImprimitiveOnV G₀) :
    ¬ (advGraph G₀).Connected := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨r, W, hr, hne, hind, htop, hmap⟩ := himp
  rcases summands_two_or_four hdim hr hirr hne hind htop hmap with ⟨rfl, h2⟩ | ⟨rfl, h1⟩
  · exact not_connected_of_two_summands B halt hnd hdim G₀ hSp hirr hD hne hind htop hmap h2
  · exact not_connected_of_four_summands B halt hnd hdim G₀ hSp hirr hD hne hind htop hmap h1

end CFSG.Quasithin.SimsG4
