module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

@[expose] def SecLiftFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V C : Subgroup G),
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) → X ≤ Subgroup.normalizer (V : Set G) →
    IsElemAbelian 2 V → pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) → C ≤ V →
    (IsNatSec X C V ∨ IsOrthSec X C V) →
    ∀ o ∈ oTwoRes X, o ^ 2 ∈ pCoreOf 2 X → C ≤ Subgroup.centralizer ({o} : Set G) →
    ∀ f ∈ V, o * f * o⁻¹ * f⁻¹ ∈ C → o * f * o⁻¹ = f

end F53.Stellmacher

end CFSG.Quasithin
