module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C126A5PermBasic

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

variable {G : Type} [Group G] [Finite G]

structure Data (H T V Y : Subgroup G) (hV : IsElemAbelian 2 V) where
  L : Subgroup (MulAut (IntMod V hV))
  θ : ↥L ≃* Perm (Fin 5)
  β : ↥(commV L) ≃* Multiplicative (evenWeight 5)
  hβ : ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV L)
    (i : Fin 5),
    ((Multiplicative.toAdd (β ⟨(h : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩) :
        evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i)
  π : Perm (Fin 5)
  L_le : L ≤ autI hV H
  L_J : L ≤ autI hV (thompsonJ H)
  J_N : autI hV (thompsonJ H) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV)))
  Y_L : ∀ φ ∈ autI hV Y, ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ ∈ Subgroup.closure {cyc3 π}
  t_lift : ∃ φ ∈ autI hV (thompsonJ T), ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ = swap (π 2) (π 3)

end CFSG.Quasithin.C126.A5
