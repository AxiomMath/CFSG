module

public import CFSG.Quasithin.EmptyFaithful.S153D27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Ctx15328 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15327 T Mc M V₁ V₂ Yp I L t where
  c27 : Concl15327 T Yp I L
  minimal : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I
  I_eq : I = L ⊔ Sgp153 T V₁
  unique_max : ∀ K : Subgroup G, Yp ⊔ Sgp153 T V₁ ≤ K → K < I → K ≤ M ⊓ I

@[expose] def Concl15328 {G : Type} [Group G] [Finite G] (T M V₁ I L : Subgroup G) : Prop :=
  ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n ↥(Star153 T I L)) ∧
      IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L))) ∨
  ((IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) ∧
      IsMinParabolicOf (Star153 T I L) (Star153 T I (M ⊓ L)) ∧
      ∀ P : Subgroup (MulAut ↥(UI153 T I)), IsMinParabolicOf (Star153 T I L) P →
        Star153 T I L ⊓ Subgroup.normalizer
          (Star153 T I (Sgp153 T V₁ ⊓ L) : Set (MulAut ↥(UI153 T I))) ≤ P →
          Star153 T I (Sgp153 T V₁) ≤ Subgroup.normalizer (P : Set (MulAut ↥(UI153 T I)))) ∨
  (Nonempty (↥(Star153 T I I) ≃* Equiv.Perm (Fin 8)) ∧
      IsMinParabolicOf (Star153 T I L) (Star153 T I (M ⊓ L)))

@[expose] def Input15328 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15328 T Mc M V₁ V₂ Yp I L t → Concl15328 T M V₁ I L

end CFSG.Quasithin
