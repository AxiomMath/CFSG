module

public import CFSG.Monster.GMS.Defs
public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Sporadic.Co1.Module.FormsBase

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def IsCo1TwoB (s : Co1) : Prop :=
  orderOf s = 2 ∧ (co1Fix s).ncard = 2 ^ 12 ∧
    ∀ v ∈ co1Fix s, CFSG.Sporadic.Co1.Module.q₀ v = 0

@[expose] def Co1DoubleCoverTwoB : Prop :=
  ∀ (C : Type) [Group C] (π : C →* Co1) (ζ : C), Function.Surjective π →
    π.ker = Subgroup.zpowers ζ → ζ ∈ Subgroup.center C → orderOf ζ = 2 →
      (∃ c : C, c * c = 1 ∧ IsCo1TwoB (π c)) →
        ∃ K : Subgroup C, Function.Bijective fun k : K => π k

@[expose] def LeechTypeUniqueness : Prop :=
  ∀ (G G' : Type) [Group G] [Group G'] [Finite G] [Finite G'] (z : G) (z' : G'),
    GMSLeechCentralizer z → GMSLeechCentralizer z' →
    ∀ (φ : Subgroup.centralizer ({z} : Set G) →* Co1)
      (φ' : Subgroup.centralizer ({z'} : Set G') →* Co1),
      Function.Surjective φ → φ.ker = pCore 2 (Subgroup.centralizer ({z} : Set G)) →
      Function.Surjective φ' → φ'.ker = pCore 2 (Subgroup.centralizer ({z'} : Set G')) →
      (∀ t, orderOf t = 2 → ¬ IsCo1TwoB (φ t)) → (∀ t, orderOf t = 2 → ¬ IsCo1TwoB (φ' t)) →
        Nonempty (Subgroup.centralizer ({z} : Set G) ≃* Subgroup.centralizer ({z'} : Set G'))

end CFSG.Monster.GMS
