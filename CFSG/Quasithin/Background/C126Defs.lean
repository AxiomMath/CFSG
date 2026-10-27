module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C1GNBlocks

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique B2F E2

variable {G : Type} [Group G] [Finite G]

@[expose] def OneBlock (H T : Subgroup G) : Prop :=
  ∃ K : Subgroup G, IsChi0Block H K ∧ ⁅K, thompsonJ T⁆ = K ∧ H = T ⊔ conjClosure K T

@[expose] def Concl1 (C₁ C₂ : Subgroup G → Subgroup G) (H T : Subgroup G) : Prop :=
  C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) ∨ OneBlock H T

@[expose] def E23Fam (H T V : Subgroup G) (hV : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hV)))) : Prop :=
  (I.card = 1 ∨ I.card = 2) ∧
  autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
  (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
  (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
  (∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L') ∧
  (∀ L ∈ I, (∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨ IsA5Module L) ∧
  fixV (autI hV (twoResidual H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
  (∀ L ∈ I, commV L ⊓
      (fixV (autI hV (twoResidual H)) ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤
    fixV (autI hV (twoResidual H))) ∧
  ((∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) ∧
    conjClosure (omegaOneCenterOf (thompsonJ T)) (twoResidual H) =
      ⁅V, twoResidual H⁆ ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G))) ∧
  ((∀ L ∈ I, IsA5Module L) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    autI hV (thompsonJ T) = ⨆ L ∈ I, (L ⊓ autI hV (thompsonJ T)) ∧
    ∀ L ∈ I, Nat.card ↥(L ⊓ autI hV (thompsonJ T)) = 4 ∧
      ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ autI hV (thompsonJ T) =
        Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap})

theorem e23Concl_iff (H T V : Subgroup G) (hV : IsElemAbelian 2 V) :
    E2.E23Concl H T V hV ↔ twoResidual H ≤ thompsonJ H ∧ ∃ I, E23Fam H T V hV I :=
  Iff.rfl

@[expose] def NatCase (H T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  twoResidual H ≤ thompsonJ H ∧ ∃ I, E23Fam H T V hV I ∧
    ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n

@[expose] def A5Case (H T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  twoResidual H ≤ thompsonJ H ∧ ∃ I, E23Fam H T V hV I ∧ ∀ L ∈ I, IsA5Module L

@[expose] def NatStmt (C₁ C₂ : Subgroup G → Subgroup G) : Prop :=
  IsGNChoice C₁ C₂ → ∀ (H T M V : Subgroup G) (hV : IsElemAbelian 2 V),
    MinParabolic H T M → IsSQTKTC H → CharTwo H → IsTwoReducedIn H V → V = VZ T H →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → NatCase H T V hV → Concl1 C₁ C₂ H T

@[expose] def A5Stmt (C₁ C₂ : Subgroup G → Subgroup G) : Prop :=
  IsGNChoice C₁ C₂ → ∀ (H T M V : Subgroup G) (hV : IsElemAbelian 2 V),
    MinParabolic H T M → IsSQTKTC H → CharTwo H → IsTwoReducedIn H V → V = VZ T H →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → A5Case H T V hV → Concl1 C₁ C₂ H T

end CFSG.Quasithin.C126
