module

public import CFSG.Quasithin.EmptyFaithful.T1531Gold2
public import CFSG.Quasithin.Background.G2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

structure Ctx15350 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G) : Prop where
  c : Ctx153 G T Mc M V₁ V₂ t
  r45 : Res15345 T Mc M V₁ V₂
  r46 : Res15346 T M V₁ V₂
  r47 : Res15347 T M V₁
  r49 : Res15349 T Mc M V₁
  hF : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) Mc

section Vocabulary

variable {G : Type} [Group G]

abbrev UH153 (T M V₁ Mc : Subgroup G) : Subgroup G := conjClosure (ZS153 T M V₁) Mc

noncomputable abbrev HStar153 (T M V₁ Mc : Subgroup G) :
    Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :=
  autOn (tildeOf (quasithinOmegaOneCenter T) Mc)
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

noncomputable abbrev XStar153 (T M V₁ Mc : Subgroup G) (X : Subgroup G) :
    Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :=
  autOn (tildeOf (quasithinOmegaOneCenter T) X)
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

abbrev UCT153 (T M V₁ Mc : Subgroup G) : Subgroup G :=
  UH153 T M V₁ Mc ⊔ (T ⊓ Subgroup.centralizer (VZ T M : Set G))

end Vocabulary

section OrthogonalSpace

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

noncomputable def qV153 (c : Ctx153 G T Mc M V₁ V₂ t) : ↥(VZ T M) → ZMod 2 :=
  Classical.choose c.decomp.definite

theorem qV153_spec (c : Ctx153 G T Mc M V₁ V₂ t) :
    IsQuadraticFormOn (qV153 c) ∧ IsNondegQuadratic (qV153 c) ∧ IsPlusType (qV153 c) ∧
      autOn M (VZ T M) = orthogonalGroupOf (qV153 c) ∧
      ∀ (v : G) (hv : v ∈ VZ T M), qV153 c ⟨v, hv⟩ = 1 ↔ (v ∈ V₁ ∨ v ∈ V₂) ∧ v ≠ 1 :=
  Classical.choose_spec c.decomp.definite

@[expose] def Orth153 (c : Ctx153 G T Mc M V₁ V₂ t) (a b : G) : Prop :=
  ∃ (ha : a ∈ VZ T M) (hb : b ∈ VZ T M), quadPolar (qV153 c) ⟨a, ha⟩ ⟨b, hb⟩ = 0

@[expose] def IsPerp153 (c : Ctx153 G T Mc M V₁ V₂ t) (A B : Subgroup G) : Prop :=
  ∀ v : G, v ∈ B ↔ v ∈ VZ T M ∧ ∀ a ∈ A, Orth153 c a v

@[expose] def IsOmega4PlusOfM153 (T M : Subgroup G) (hV : IsElemAbelian 2 (VZ T M))
    (Ω : Subgroup (MulAut ↥(VZ T M))) : Prop :=
  ∀ g : MulAut ↥(VZ T M), g ∈ Ω ↔ g ∈ autOn M (VZ T M) ∧ IsDicksonEven153 hV g

end OrthogonalSpace

section Preimages

variable {G : Type} [Group G]

@[expose] noncomputable def preAut153 (V A : Subgroup G) (N : Subgroup (MulAut ↥V)) : Subgroup G :=
  A ⊓ ((N.comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype)

@[expose] noncomputable def Ni153 (T Mc M V₁ : Subgroup G) (N : Subgroup (MulAut ↥(VZ T M))) : Subgroup G :=
  preAut153 (VZ T M) (Y153 Mc M ⊔ UH153 T M V₁ Mc) N

@[expose] noncomputable def Yi153 (T Mc M V₁ : Subgroup G) (N : Subgroup (MulAut ↥(VZ T M))) : Subgroup G :=
  oTwoUpper (Y153 Mc M ⊓ Ni153 T Mc M V₁ N)

end Preimages

@[expose] def IsNonabelian153 {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a

@[expose] def NonabelianVH153 {G : Type} [Group G] (T M Mc : Subgroup G) : Prop :=
  IsNonabelian153 (conjClosure (VZ T M) Mc)

@[expose] def NotOrth153 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
    (c : Ctx153 G T Mc M V₁ V₂ t) (g : G) : Prop :=
  ¬ ∀ z ∈ quasithinOmegaOneCenter T, ∀ z' ∈ conjSubgroup (quasithinOmegaOneCenter T) g, Orth153 c z z'

section Concl51

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15351 (cx : Ctx15350 T Mc M V₁ V₂ t) : Prop where
  one : ¬ VZ T M ≤ pCoreOf 2 Mc
  two :
    (IsNonabelian153 (UH153 T M V₁ Mc) ∧
        IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
        autOn (UH153 T M V₁ Mc) (VZ T M) ≤ autOn T (VZ T M) ∧
        autOn (UH153 T M V₁ Mc) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
        ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
          IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω) ∨
    (IsElemAbelian 2 (UH153 T M V₁ Mc) ∧ UH153 T M V₁ Mc ≤ Sgp153 T V₁ ∧
        centerOf (autOn T (VZ T M)) ≤ autOn (UH153 T M V₁ Mc) (VZ T M) ∧
        ZS153 T M V₁ = VZ T M ⊓ UH153 T M V₁ Mc)
  three : Y153 Mc M = ⁅Y153 Mc M, UH153 T M V₁ Mc⁆
  four_Q : ⁅VZ T M, pCoreOf 2 Mc⁆ ≤ VZ T M ⊓ pCoreOf 2 Mc
  four_U : ⁅VZ T M, UH153 T M V₁ Mc⁆ ≤ VZ T M ⊓ UH153 T M V₁ Mc

end Concl51

@[expose] def Concl15352 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
    (_cx : Ctx15350 T Mc M V₁ V₂ t) : Prop :=
  IsNonabelian153 (UH153 T M V₁ Mc)

section Concl53

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15353One (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) :
    Prop where
  omega : ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
    autOn (UH153 T M V₁ Mc) (VZ T M) ⊔ autOn (Y153 Mc M) (VZ T M) = Ω ∧ N₁ ⊔ N₂ = Ω
  inf : N₁ ⊓ N₂ = ⊥
  comm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a
  iso₁ : Nonempty (↥N₁ ≃* Equiv.Perm (Fin 3))
  iso₂ : Nonempty (↥N₂ ≃* Equiv.Perm (Fin 3))
  comm₁ : ⁅VZ T M, Ni153 T Mc M V₁ N₁⁆ = VZ T M
  comm₂ : ⁅VZ T M, Ni153 T Mc M V₁ N₂⁆ = VZ T M

structure Concl15353Two (cx : Ctx15350 T Mc M V₁ V₂ t) : Prop where
  perp : ∃ P : Subgroup G, IsPerp153 cx.c (quasithinOmegaOneCenter T) P ∧
    VZ T M ⊓ pCoreOf 2 Mc = P ∧ VZ T M ⊓ UH153 T M V₁ Mc = P ∧ ⁅UH153 T M V₁ Mc, VZ T M⁆ = P
  card_Vstar : (VZ T M ⊓ pCoreOf 2 Mc).relIndex (VZ T M) = 2

end Concl53

end CFSG.Quasithin
