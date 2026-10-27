module

public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Defs

variable {G : Type} [Group G]

@[expose] def Ctx24 (T M K U₁ U₂ : Subgroup G) (s u : G) : Prop :=
  Conc14619 T M ∧ Conc14620 T M ∧ Conc14623 T M ∧ K ∈ cComp (mcOf T) ∧ Conc14621 T K ∧
    Conc14622 T M K ∧ IsDecompUK T M K U₁ U₂ s ∧ IsChoiceU T M K U₁ u

@[expose] def Geom24 (T M : Subgroup G) (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T))
    (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)) : Prop :=
  F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g ∧
    F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G) <
      F8.Uγ (VZ T M) (mcOf T) (g : G) ∧
    0 < mIdx (conjClosure (VZ T M) (mcOf T))
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ∧
    mIdx (conjClosure (VZ T M) (mcOf T))
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ≤
      mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ∧
    mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) <
      mIdx (conjClosure (VZ T M) (mcOf T))
        (centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))
          (F8.Uγ (VZ T M) (mcOf T) (g : G))) ∧
    F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤
      ⁅conjClosure (VZ T M) (mcOf T), perfectCore (mcOf T)⁆ ⊔ quasithinOmegaOneCenter T

end Defs

@[expose] def Input14624Geom : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      ∃ (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
        Geom24 T M γ γ' g

@[expose] def Input14624Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      ∀ (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
        Geom24 T M γ γ' g → K = perfectCore (mcOf T) → KbarIsL3Two K

end CFSG.Quasithin
