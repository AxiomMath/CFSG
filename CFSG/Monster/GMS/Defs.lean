module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def GMSF2Type (d₀ : B) (H : Type*) [Group H] : Prop :=
  IsSimpleGroup H ∧ ∃ x : H, orderOf x = 2 ∧
    Nonempty (Subgroup.centralizer ({x} : Set H) ≃* Subgroup.centralizer ({d₀} : Set B))

@[expose] def GMSDoubleF2Centralizer (d₀ : B) {G : Type*} [Group G] (a : G) : Prop :=
  orderOf a = 2 ∧ commutator (Subgroup.centralizer ({a} : Set G)) = ⊤ ∧
    ∃ (H : Type) (_ : Group H) (φ : Subgroup.centralizer ({a} : Set G) →* H),
      Function.Surjective φ ∧
        φ.ker.map (Subgroup.centralizer ({a} : Set G)).subtype = Subgroup.zpowers a ∧
        GMSF2Type d₀ H

@[expose] def GMSLeechCentralizer {G : Type*} [Group G] (z : G) : Prop :=
  orderOf z = 2 ∧
    IsExtraspecialPGroup 2 (pCore 2 (Subgroup.centralizer ({z} : Set G))) ∧
    Nat.card (pCore 2 (Subgroup.centralizer ({z} : Set G))) = 2 ^ 25 ∧
    (∃ φ : Subgroup.centralizer ({z} : Set G) →* Co1,
      Function.Surjective φ ∧ φ.ker = pCore 2 (Subgroup.centralizer ({z} : Set G))) ∧
    Subgroup.centralizer (pCore 2 (Subgroup.centralizer ({z} : Set G)) :
        Set (Subgroup.centralizer ({z} : Set G))) ≤
      pCore 2 (Subgroup.centralizer ({z} : Set G))

@[expose] def GMSF1Type (d₀ : B) {G : Type*} [Group G] (a z : G) : Prop :=
  GMSDoubleF2Centralizer d₀ a ∧ GMSLeechCentralizer z

end CFSG.Monster.GMS
