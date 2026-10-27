module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph
open scoped Pointwise

section Defs

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def PushReach : Track Γ G → Track Γ G → Prop := Relation.ReflTransGen TrackPrec

@[expose] def InPiStar (T : Track Γ G) : Prop :=
  TrackInPi T ∧ ∃ (d : ℤ) (f : G), valence Γ (T.line.vert d) = 3 ∧
    f ∈ Subgroup.normalizer (omega1 T.fixer : Set G) ∧ IsLenTwoReflection T.line d f

@[expose] def Lcirc (L : Subgroup G) (α β α₂ : V) : Subgroup G :=
  L ⊓ MulAction.stabilizer G β ⊓ MulAction.stabilizer G ({α, α₂} : Set V)

@[expose] def ZT (T : Track Γ G) (d : ℤ) : Subgroup G :=
  T.fixer ⊓ Subgroup.centralizer (↑(nbrStab Γ G (T.line.vert d)) : Set G)

theorem PushReach.refl (T : Track Γ G) : PushReach T T := Relation.ReflTransGen.refl

theorem PushReach.single {T T' : Track Γ G} (h : TrackPrec T T') : PushReach T T' :=
  Relation.ReflTransGen.single h

theorem PushReach.trans {T T' T'' : Track Γ G} (h : PushReach T T') (h' : PushReach T' T'') :
    PushReach T T'' := Relation.ReflTransGen.trans h h'

theorem PushReach.omega1_le {T T' : Track Γ G} (h : PushReach T T') :
    omega1 T.fixer ≤ omega1 T'.fixer := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans hbc.1

theorem mem_lcirc_iff {L : Subgroup G} {α β α₂ : V} {g : G} :
    g ∈ Lcirc L α β α₂ ↔ g ∈ L ∧ g • β = β ∧
      (g • α = α ∧ g • α₂ = α₂ ∨ g • α = α₂ ∧ g • α₂ = α) := by
  simp only [Lcirc, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Set.smul_set_insert,
    Set.smul_set_singleton, Set.pair_eq_pair_iff]
  tauto

end Defs

end CFSG.Quasithin.Fan86
