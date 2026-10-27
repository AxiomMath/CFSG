module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.H13.LocDblCComp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

structure E23Data {Γ : Type} [Group Γ] [Finite Γ] (H T V : Subgroup Γ) (hV : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hV)))) : Prop where
  card : I.card = 1 ∨ I.card = 2
  jeq : autI hV (thompsonJ H) = ⨆ L ∈ I, L
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  indep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  trans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L'
  types : ∀ L ∈ I, (∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨
    E2.IsA5Module L
  span : fixV (autI hV (twoResidual H)) ⊔ ⨆ L ∈ I, commV L = ⊤
  dir : ∀ L ∈ I, commV L ⊓
      (fixV (autI hV (twoResidual H)) ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤
    fixV (autI hV (twoResidual H))
  two : (∀ L ∈ I, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) ∧
    conjClosure (omegaOneCenterOf (thompsonJ T)) (twoResidual H) =
      ⁅V, twoResidual H⁆ ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set Γ))
  three : (∀ L ∈ I, E2.IsA5Module L) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    autI hV (thompsonJ T) = ⨆ L ∈ I, (L ⊓ autI hV (thompsonJ T)) ∧
    ∀ L ∈ I, Nat.card ↥(L ⊓ autI hV (thompsonJ T)) = 4 ∧
      ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ autI hV (thompsonJ T) =
        Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap}

theorem e23Data_of_concl {Γ : Type} [Group Γ] [Finite Γ] {H T V : Subgroup Γ}
    {hV : IsElemAbelian 2 V} (h : E2.E23Concl H T V hV) :
    twoResidual H ≤ thompsonJ H ∧ ∃ I, E23Data H T V hV I := by
  obtain ⟨h0, I, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h0, I, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
