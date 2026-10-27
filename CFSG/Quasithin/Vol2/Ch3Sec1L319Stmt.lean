module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.H13.J4PlusType

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise

section Six

variable {G : Type} [Group G]

@[expose] def Six6i (T M V : Subgroup G) : Prop :=
  ∀ F : Subgroup G, F ≤ M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    (∀ x ∈ F, Nat.Coprime (orderOf x) 6) →
    ((F ⊔ T : Subgroup G) : Set G) = (F : Set G) * (T : Set G) →
    F ≤ Subgroup.centralizer (V : Set G)

end Six

end CFSG.Quasithin.H13.L319
