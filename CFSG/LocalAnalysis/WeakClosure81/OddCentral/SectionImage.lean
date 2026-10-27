module
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Action.End
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable (Y M : Type*) [Group Y] [AddCommGroup M] [DistribMulAction Y M]

@[expose] def imgGroup : Subgroup (Equiv.Perm M) := (MulAction.toPermHom Y M).range

@[expose] instance imgAct : DistribMulAction (imgGroup Y M) M :=
  { (inferInstance : MulAction (imgGroup Y M) M) with
    smul_zero := fun g => by
      obtain ⟨y, hy⟩ := g.2
      show (g : Equiv.Perm M) 0 = 0
      rw [← hy]; exact smul_zero y
    smul_add := fun g m m' => by
      obtain ⟨y, hy⟩ := g.2
      show (g : Equiv.Perm M) (m + m') = (g : Equiv.Perm M) m + (g : Equiv.Perm M) m'
      rw [← hy]; exact smul_add y m m' }

@[expose] def imgHom : Y →* imgGroup Y M := (MulAction.toPermHom Y M).rangeRestrict

variable {Y M}

theorem imgHom_smul (y : Y) (m : M) : imgHom Y M y • m = y • m := rfl

theorem imgHom_surjective : Function.Surjective (imgHom Y M) :=
  MonoidHom.rangeRestrict_surjective _

theorem img_faithful : ∀ g : imgGroup Y M, (∀ m : M, g • m = m) → g = 1 := fun g h =>
  Subtype.ext (Equiv.ext h)

theorem img_irr (hirr : ∀ N : AddSubgroup M, (∀ y : Y, ∀ m ∈ N, y • m ∈ N) → N = ⊥ ∨ N = ⊤) :
    ∀ N : AddSubgroup M, (∀ g : imgGroup Y M, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤ :=
  fun N hN => hirr N fun y m hm => by rw [← imgHom_smul]; exact hN _ m hm

theorem imgHom_eq_one_iff (y : Y) : imgHom Y M y = 1 ↔ ∀ m : M, y • m = m := by
  constructor
  · intro h m; rw [← imgHom_smul, h, one_smul]
  · intro h; exact img_faithful _ fun m => by rw [imgHom_smul]; exact h m

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

