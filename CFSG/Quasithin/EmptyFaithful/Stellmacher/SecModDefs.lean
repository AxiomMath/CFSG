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

@[expose] def Hss15Sec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V C : Subgroup G),
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) → IsSec X C V →
    pCoreOf 2 X ≤ cSecIn X C V → fixSecIn X C V = C →
    ∀ s ∈ X, secIdx (Subgroup.zpowers s) C V = 2 → IsOrthSec X C V

@[expose] def IrrSecSec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V C T : Subgroup G),
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) → IsSec X C V → C ≠ V →
    pCoreOf 2 X ≤ cSecIn X C V → fixSecIn X C V = C → IsSylowTwoOf T X →
    (∀ U : Subgroup G, C ≤ U → U ≤ V → X ≤ Subgroup.normalizer (U : Set G) →
      fixSecIn T C V ≤ U → U = V) →
    ∀ a ∈ oTwoRes X ⊔ pCoreOf 2 X, a ∉ pCoreOf 2 X →
      (a ^ 2 ∈ pCoreOf 2 X ∨ a ^ 3 ∈ pCoreOf 2 X) →
      secIdx (Subgroup.zpowers a) C V ≤ 8 → IsOrthSec X C V ∨ IsNatSec X C V

end F53.Stellmacher

end CFSG.Quasithin
