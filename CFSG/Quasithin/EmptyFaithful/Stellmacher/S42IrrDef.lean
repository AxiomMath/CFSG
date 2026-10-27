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

@[expose] def IrrSec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V T : Subgroup G),
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) → V ≤ pCoreOf 2 X →
    X ≤ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 V →
    X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X →
    V ⊓ Subgroup.centralizer (X : Set G) = ⊥ → IsSylowTwoOf T X →
    (∀ U : Subgroup G, U ≤ V → X ≤ Subgroup.normalizer (U : Set G) →
      V ⊓ Subgroup.centralizer (T : Set G) ≤ U → U = V) →
    ∀ a ∈ oTwoRes X ⊔ pCoreOf 2 X, a ∉ pCoreOf 2 X →
      (a ^ 2 ∈ pCoreOf 2 X ∨ a ^ 3 ∈ pCoreOf 2 X) →
      (V ⊓ Subgroup.centralizer ({a} : Set G)).relIndex V ≤ 8 →
      IsOrthSec X ⊥ V ∨ IsNatSec X ⊥ V

end F53.Stellmacher

end CFSG.Quasithin
