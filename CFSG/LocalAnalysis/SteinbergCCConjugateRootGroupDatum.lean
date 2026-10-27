module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.LocalAnalysis

structure IsFiniteConjugateRootGroupDatum (G Ω : Type*) [Group G] [MulAction G Ω]
    (U : Ω → Subgroup G) : Prop where
  finite_group : Finite G
  finite_set : Finite Ω
  three_le_card : 3 ≤ Nat.card Ω
  fixes : ∀ (x : Ω), ∀ u ∈ U x, u • x = x
  regular : ∀ x y z : Ω, y ≠ x → z ≠ x → ∃! u : U x, (u : G) • y = z
  conj : ∀ (g : G) (x : Ω), (U x).map (MulAut.conj g).toMonoidHom = U (g • x)

@[expose] def rootPointStabilizer (G : Type*) {Ω : Type*} [Group G] [MulAction G Ω] (x : Ω) :
    Subgroup G :=
  MulAction.stabilizer G x

theorem mem_rootPointStabilizer_iff {G Ω : Type*} [Group G] [MulAction G Ω] {x : Ω} {g : G} :
    g ∈ rootPointStabilizer G x ↔ g • x = x :=
  MulAction.mem_stabilizer_iff

end CFSG.LocalAnalysis
