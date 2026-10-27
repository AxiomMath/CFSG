module

public import CFSG.Quasithin.Recognition.Stroth.Str86Props

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def Str86ZNotLeAb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    VU3Big L1 → VBig L2 → VL2 L2 →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
    Z2 L1 L2 S ≤ Q1 L1 L2 S →
      ¬ ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x

@[expose] def Str86ZNotLeNonab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    VU3Big L1 → VBig L2 → VL2 L2 →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
    Z2 L1 L2 S ≤ Q1 L1 L2 S →
      ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x

theorem str86ZNotLe_of_parts (hAb : Str86ZNotLeAb) (hNon : Str86ZNotLeNonab) :
    Str86ZNotLe := by
  intro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI hZ
  exact hAb G L1 L2 S hF hSB h1 hB2 h2 hZI hZ
    (hNon G L1 L2 S hF hSB h1 hB2 h2 hZI hZ)

end CFSG.Quasithin.Stroth
