module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingIntersections

namespace CFSG
end CFSG
open CFSG

/-!
# The normal-complement core of Theorem 6

The source proof chooses a subgroup `W` normal in `M`, minimal subject to
`W ⊔ D = M`, and then spends Sections 9--11 proving `W ⊓ D = ⊥`.  This
file records that decomposition explicitly: the minimal supplement exists by
finiteness, and disjointness of every such minimal supplement is exactly the
remaining hard input needed for a normal complement.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

/-- `W` is a subgroup of `M`, normal in `M`, whose join with `D` is all of
`M`. -/
public structure IsNormalSupplement {X : Type u} [Group X]
    (M D W : Subgroup X) : Prop where
  le_M : W ≤ M
  normal_in_M : (W.subgroupOf M).Normal
  sup_eq : W ⊔ D = M

/-- `W` is inclusion-minimal among normal supplements of `D` in `M`. -/
public def IsMinimalNormalSupplement {X : Type u} [Group X]
    (M D W : Subgroup X) : Prop :=
  Minimal (IsNormalSupplement M D) W

namespace IsMinimalNormalSupplement

/-- The supplement fields carried by a minimal normal supplement. -/
public theorem prop
    {X : Type u} [Group X] {M D W : Subgroup X}
    (hW : IsMinimalNormalSupplement M D W) :
    IsNormalSupplement M D W := by
  exact hW.1

/-- Minimality of a normal supplement is available as an explicit
order-theoretic eliminator to downstream Section 9 modules. -/
public theorem eq_of_le
    {X : Type u} [Group X] {M D W Q : Subgroup X}
    (hW : IsMinimalNormalSupplement M D W)
    (hQ : IsNormalSupplement M D Q)
    (hQW : Q ≤ W) :
    Q = W := by
  exact le_antisymm hQW (hW.2 hQ hQW)

end IsMinimalNormalSupplement

/-- `Q` is a normal complement to `D` inside `M`. -/
public structure IsNormalComplementIn {X : Type u} [Group X]
    (M D Q : Subgroup X) : Prop extends IsNormalSupplement M D Q where
  disjoint_D : Disjoint Q D

/-- Every subgroup `D ≤ M` has an inclusion-minimal normal supplement in
the finite ambient group. -/
public theorem exists_isMinimalNormalSupplement
    {X : Type u} [Group X] [Finite X] {M D : Subgroup X}
    (hDle : D ≤ M) :
    ∃ W : Subgroup X, IsMinimalNormalSupplement M D W := by
  classical
  have hM : IsNormalSupplement M D M := by
    refine ⟨le_rfl, ?_, sup_eq_left.mpr hDle⟩
    rw [Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨W, _, hWmin⟩ :=
    Finite.exists_le_minimal (p := IsNormalSupplement M D) hM
  exact ⟨W, hWmin⟩

/-- Every normal supplement contains an inclusion-minimal normal supplement.
This is the change-of-choice form used in Lemma 9.7. -/
public theorem exists_isMinimalNormalSupplement_le
    {X : Type u} [Group X] [Finite X] {M D Q : Subgroup X}
    (hQ : IsNormalSupplement M D Q) :
    ∃ W : Subgroup X, W ≤ Q ∧ IsMinimalNormalSupplement M D W := by
  classical
  obtain ⟨W, hWQ, hWmin⟩ :=
    Finite.exists_le_minimal (p := IsNormalSupplement M D) hQ
  exact ⟨W, hWQ, hWmin⟩

/-- To obtain a normal complement, it is enough to prove that every minimal
normal supplement is disjoint from `D`. -/
public theorem exists_isNormalComplementIn_of_minimal_disjoint
    {X : Type u} [Group X] [Finite X] {M D : Subgroup X}
    (hDle : D ≤ M)
    (hcore : ∀ {W : Subgroup X},
      IsMinimalNormalSupplement M D W → Disjoint W D) :
    ∃ Q : Subgroup X, IsNormalComplementIn M D Q := by
  obtain ⟨Q, hQmin⟩ := exists_isMinimalNormalSupplement hDle
  exact ⟨Q,
    { le_M := hQmin.prop.le_M
      normal_in_M := hQmin.prop.normal_in_M
      sup_eq := hQmin.prop.sup_eq
      disjoint_D := hcore hQmin }⟩

end CFSG.BenderSuzuki
