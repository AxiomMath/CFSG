module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Z37 {V : Type} [CommGroup V] [Finite V] (D X G T' : Subgroup (MulAut V))
    (s : MulAut V) : Prop where
  exp : ∀ v : V, v ^ 2 = 1
  nontrivial : Nontrivial V
  simple : IsSimpleGroup ↥D
  nonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a
  typeD : A38Types ↥D
  sqtkD : SQTKGroup ↥D
  comm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g
  swapDX : X = D.map (MulAut.conj s).toMonoidHom
  swapXD : D = X.map (MulAut.conj s).toMonoidHom
  s_mem : s ∈ T'
  DX_le : D ⊔ X ≤ G
  G_eq : G = (D ⊔ X) ⊔ T'
  DX_norm : ∀ g ∈ G, ∀ h ∈ D ⊔ X, g * h * g⁻¹ ∈ D ⊔ X
  T_perm : ∀ g ∈ T', D.map (MulAut.conj g).toMonoidHom = D ∨
    D.map (MulAut.conj g).toMonoidHom = X
  T_sylow : IsSylowTwoOf T' G
  irr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤
  qhat : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)

@[expose] def Z37Concl {V : Type} [CommGroup V] (D X : Subgroup (MulAut V)) : Prop :=
  (∃ n, IsPSL 2 2 n ↥D ∧ Omega4PlusModule (D ⊔ X) n) ∨
    (IsPSL 3 2 1 ↥D ∧ TensorNatL32 (D ⊔ X))

@[expose] def Z1Stmt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (D X : Subgroup (MulAut V)), (∀ g ∈ D, ∀ x ∈ X, g * x = x * g) →
      commV (D ⊔ X) = ⊤ →
      (∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → fixV (D ⊔ X) ≤ U →
        U = fixV (D ⊔ X) ∨ U = ⊤) →
      ¬ D ≤ centSec ⊤ (fixV (D ⊔ X)) → ¬ X ≤ centSec ⊤ (fixV (D ⊔ X)) →
        fixV (D ⊔ X) = ⊥

@[expose] def Z37Main : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (D X G T' : Subgroup (MulAut V)) (s : MulAut V),
    Z37 D X G T' s → Z37Concl D X

end CFSG.Quasithin
