
module

public import CFSG.YGroups.Y443.EvenPresentation
public import CFSG.YGroups.Y443.Native.Words
public import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native CFSG.Open

local instance : DecidableRel e443Lt := fun a b => by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩ <;> unfold e443Lt <;> infer_instance

local instance : DecidableRel MonsterY443Adj := fun a b => by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩ <;> unfold MonsterY443Adj <;>
    infer_instance

def wIdx (g : E443Gen) : ℕ := ([0, 4, 8] : List ℕ)[(g.1 : ℕ)]! + g.2

theorem wIdx_lt : ∀ g : E443Gen, wIdx g < 11 := by decide

theorem wIdx_lt_of_lt : ∀ g g' : E443Gen, e443Lt (some g) (some g') → wIdx g < wIdx g' := by
  decide

theorem mI_of_adj : ∀ g g' : E443Gen, e443Lt (some g) (some g') →
    MonsterY443Adj (some g) (some g') → mI (wIdx g) (wIdx g') = 3 := by decide

theorem mI_of_nadj : ∀ g g' : E443Gen, e443Lt (some g) (some g') →
    ¬ MonsterY443Adj (some g) (some g') → mI (wIdx g) (wIdx g') = 2 := by decide

theorem ordI_of_zero : ∀ g : E443Gen, g.2.val = 0 → ordI (wIdx g) = 3 := by decide

theorem ordI_of_ne_zero : ∀ g : E443Gen, g.2.val ≠ 0 → ordI (wIdx g) = 2 := by decide

theorem ordI_pos (k : ℕ) : 1 ≤ ordI k := by
  unfold ordI
  split_ifs <;> norm_num

noncomputable def gGen (g : E443Gen) : Gmat := ⟨M (wIdx g), M_mem _⟩

theorem coe_gGen (g : E443Gen) : ((gGen g : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = M (wIdx g) := rfl

noncomputable def fGen (g : E443Gen) : Gmat :=
  ⟨(M (wIdx g))⁻¹, Subgroup.inv_mem _ (M_mem _)⟩

theorem coe_fGen (g : E443Gen) : ((fGen g : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = (M (wIdx g))⁻¹ := rfl

theorem fGen_eq (g : E443Gen) : fGen g = (gGen g)⁻¹ := rfl

def y443U11 : E443Gen := ⟨0, ⟨0, by decide⟩⟩

def axElt (g : E443Gen) : MonsterY443Derived :=
  ⟨PresentedGroup.of none * PresentedGroup.of (some g), e443_ax_mem_derived g⟩

theorem axElt_eq (g : E443Gen) : axElt g = e443Phi (PresentedGroup.of g) :=
  (e443Phi_of g).symm

def IsFM (f : MonsterY443Derived →* Gmat) : Prop :=
  ∀ g : E443Gen, f (axElt g) = gGen g

end CFSG.YGroups.Y443
