module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs3
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

section Chains

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Chain15353 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) : Prop where
  nonab : NonabelianVH153 T M Mc
  h51 : Concl15351 cx
  h52 : Concl15352 cx
  h53one : Concl15353One cx N₁ N₂
  h53two : Concl15353Two cx

structure Chain15354 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) : Prop extends Chain15353 cx N₁ N₂ where
  hg : g ∈ Y153 Mc M
  hgZ : NotOrth153 cx.c g
  h54 : Concl15354 cx N₁ N₂ g s

structure Chain15355 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) : Prop extends Chain15354 cx N₁ N₂ g s where
  h55 : Concl15355 cx g

structure Chain15356 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) (y t₁ : G) : Prop extends Chain15355 cx N₁ N₂ g s where
  hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)
  ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc
  h56 : Concl15356 cx N₁ s y t₁

structure Chain15357 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) (y t₁ : G) : Prop extends Chain15356 cx N₁ N₂ g s y t₁ where
  h57 : Concl15357 cx s

structure Chain15358 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) (y t₁ : G) : Prop extends Chain15357 cx N₁ N₂ g s y t₁ where
  h58 : Concl15358 cx s

structure Chain15359 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) (y t₁ : G) : Prop extends Chain15358 cx N₁ N₂ g s y t₁ where
  h59 : Concl15359 cx

end Chains

@[expose] def Input15309Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Hyp153 G T Mc M →
    VZ T M < pCoreOf 2 (Y153 Mc M)

end CFSG.Quasithin
