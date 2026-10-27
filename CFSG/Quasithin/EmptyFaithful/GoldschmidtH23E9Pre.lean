module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Defs
public import CFSG.Quasithin.EmptyFaithful.T1515Defs

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def HasE9 (T Mc M : Subgroup G) : Prop :=
  ∃ E : Subgroup (MulAut ↥(V154 T Mc M)),
    E ≤ autOn M (V154 T Mc M) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9

structure E9Pre (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G) : Prop where
  h5 : Ce15Six T Mc M 5
  e9 : HasE9 T Mc M
  data : ∃ (hVe : IsElemAbelian 2 (V154 T Mc M)) (d : Six5Data T M (V154 T Mc M) hVe),
    V₁ = d.V₁ ∧ V₂ = d.V₂
  z₁ : Z₁ = vE1516 T Mc M ⊓ V₁
  z₂ : Z₂ = vE1516 T Mc M ⊓ V₂

end CFSG.Quasithin.E9
