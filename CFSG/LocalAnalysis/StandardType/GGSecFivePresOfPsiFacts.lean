module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

section Facts

variable {U : Type*} [Group U] (D : UniversalRootDatum U)

@[expose] def GGHasWeylLift : Prop := ∃ ν : GGWeyl D →* U, GGWeylLift D ν

@[expose] def GGRootsGenerate : Prop := ggSub D D.roots = ⊤

@[expose] def GGRootGroupsRigid : Prop :=
  ∀ γ ∈ D.roots, ∀ w : GGWeyl D,
    D.rootGroup (weylAction D.isFiniteType w γ) = D.rootGroup γ →
      weylAction D.isFiniteType w γ = γ

@[expose] def GGSimpleRootGroupsRigid : Prop :=
  ∀ (i : Fin D.rank) (w : GGWeyl D),
    D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) = D.rootGroup (Pi.single i 1) →
      weylAction D.isFiniteType w (Pi.single i 1) = Pi.single i 1

@[expose] def GGRootNotCentral : Prop :=
  ∃ γ ∈ D.roots, ¬ D.rootGroup γ ≤ Subgroup.center U

variable {D}

theorem ggSimpleRootGroupsRigid_of_rigid (h : GGRootGroupsRigid D) : GGSimpleRootGroupsRigid D := by
  intro i w hw
  exact h (Pi.single i 1) (single_mem_roots i) w hw

theorem ggWeyl_eq_one_of_fixes_simple {w : GGWeyl D}
    (h : ∀ i : Fin D.rank, weylAction D.isFiniteType w (Pi.single i 1) = Pi.single i 1) : w = 1 := by
  refine weylAction_injective D.isFiniteType ?_
  rw [map_one]
  apply LinearMap.pi_ext
  intro i x
  rw [Module.End.one_apply]
  show weylAction D.isFiniteType w (Pi.single i x) = Pi.single i x
  have hx : (Pi.single i x : Fin D.rank → ℤ) = x • Pi.single i 1 := by
    rw [← Pi.single_smul' i x (1 : ℤ)]
    simp
  calc weylAction D.isFiniteType w (Pi.single i x)
      = weylAction D.isFiniteType w (x • Pi.single i 1) := by rw [hx]
    _ = x • weylAction D.isFiniteType w (Pi.single i 1) := map_smul _ _ _
    _ = x • Pi.single i 1 := by rw [h i]
    _ = Pi.single i x := hx.symm

end Facts

end CFSG.StandardType

end
