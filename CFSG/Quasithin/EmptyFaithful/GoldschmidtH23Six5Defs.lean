module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.EmptyFaithful.S151bW3Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Six5Data (T M V : Subgroup G) (hV : IsElemAbelian 2 V) where
  hMN : M ≤ Subgroup.normalizer (V : Set G)
  hTM : T ≤ M
  hsyl : IsSylowTwoOf T M
  S : SixData151b (IntMod V hV) 5
  hA₁ : S.A₁ ≤ autI hV M
  hA₂ : S.A₂ ≤ autI hV M
  hτ : S.τ ∈ autI hV T
  hsup : S.A₁ ⊔ S.A₂ = Jhat (autI hV M)
  hcard : Nat.card (IntMod V hV) = 256

@[expose] def valHomI {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul


namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)

@[expose] noncomputable def V₁ : Subgroup G := d.S.W₁.map (valHomI hV)

@[expose] noncomputable def V₂ : Subgroup G := d.S.W₂.map (valHomI hV)

@[expose] noncomputable def Sg : Subgroup G := T ⊓ Subgroup.normalizer (d.V₁ : Set G)

@[expose] noncomputable def Z₁ : Subgroup G := d.V₁ ⊓ Subgroup.centralizer (d.Sg : Set G)

@[expose] noncomputable def Z₂ : Subgroup G := d.V₂ ⊓ Subgroup.centralizer (d.Sg : Set G)

end Six5Data

end CFSG.Quasithin
