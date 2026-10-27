module

public import CFSG.Quasithin.EmptyFaithful.S153D31
public import CFSG.Quasithin.EmptyFaithful.T1531Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

abbrev conjBy153 {G : Type} [Group G] (t : G) (X : Subgroup G) : Subgroup G :=
  X.map (MulAut.conj t).toMonoidHom

abbrev X153 {G : Type} [Group G] (T M V₁ : Subgroup G) : Subgroup G :=
  oPrimeResidualOf 3 (Subgroup.centralizer (ZS153 T M V₁ : Set G))

structure Ctx15332 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15331 T Mc M V₁ V₂ Yp I L t where
  c31 : Nonempty (↥(Star153 T I I) ≃* Equiv.Perm (Fin 8))

structure Concl15332 {G : Type} [Group G] [Finite G] (T M V₁ I L : Subgroup G) : Prop where
  orthogonal : ∃ q : ↥(UL153 T I L) → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
    (∃ E : Subgroup ↥(UL153 T I L), Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) ∧
      Nat.card ↥(UL153 T I L) = 2 ^ 6 ∧ autOn I (UL153 T I L) = orthogonalGroupOf q
  Z1 : ZS153 T M V₁ ⊓ Subgroup.centralizer (L : Set G) = ZS153 T M V₁ ⊓ V₁ ∧
    Nat.card ↥(ZS153 T M V₁ ⊓ V₁) = 2
  L_eq : L = oPrimeResidualOf 3
    (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G))
  X_eq : ∃ K : Subgroup G, K ≤ L ∧ IsMaxParabolic2 (Star153 T I L) (Star153 T I K) ∧
    Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G) ∧ X153 T M V₁ = oPrimeResidualOf 3 K
  W_direct : ∀ t' ∈ T, t' ∉ Sgp153 T V₁ →
    (⁅UL153 T I L, conjBy153 t' (UL153 T I L)⁆ = ⊥ ∧ UL153 T I L ⊓ conjBy153 t' (UL153 T I L) = ⊥ ∧
      X153 T M V₁ ⊔ Sgp153 T V₁ ≤
        Subgroup.normalizer ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G))
  P_split : ∀ t' ∈ T, t' ∉ Sgp153 T V₁ →
    (pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) =
        (Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)) ⊔
          (Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G)) ∧
      ⁅Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G),
          Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G)⁆ ≤
        Subgroup.centralizer ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G))

@[expose] def Input15332 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L

end CFSG.Quasithin
