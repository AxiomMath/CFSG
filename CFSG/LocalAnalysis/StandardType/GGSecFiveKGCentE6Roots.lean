module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

@[expose] def roots72 : List (Fin Tag.E6.rank → ℤ) :=
  [ ![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -3, -2, -1], ![-1, -1, -2, -2, -2, -1],
    ![-1, -1, -2, -2, -1, -1], ![-1, -1, -2, -2, -1, 0], ![-1, -1, -1, -2, -2, -1],
    ![-1, -1, -1, -2, -1, -1], ![-1, -1, -1, -2, -1, 0], ![-1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, 0], ![-1, -1, -1, -1, 0, 0], ![-1, 0, -1, -1, -1, -1],
    ![-1, 0, -1, -1, -1, 0], ![-1, 0, -1, -1, 0, 0], ![-1, 0, -1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0],
    ![0, -1, -1, -2, -2, -1], ![0, -1, -1, -2, -1, -1], ![0, -1, -1, -2, -1, 0],
    ![0, -1, -1, -1, -1, -1], ![0, -1, -1, -1, -1, 0], ![0, -1, -1, -1, 0, 0],
    ![0, -1, 0, -1, -1, -1], ![0, -1, 0, -1, -1, 0], ![0, -1, 0, -1, 0, 0], ![0, -1, 0, 0, 0, 0],
    ![0, 0, -1, -1, -1, -1], ![0, 0, -1, -1, -1, 0], ![0, 0, -1, -1, 0, 0], ![0, 0, -1, 0, 0, 0],
    ![0, 0, 0, -1, -1, -1], ![0, 0, 0, -1, -1, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, -1],
    ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0],
    ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

theorem single_mem_roots72 :
    ∀ j : Fin Tag.E6.rank, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ roots72 := by
  decide +kernel

theorem reflect_mem_roots72 :
    ∀ i : Fin Tag.E6.rank, ∀ v ∈ roots72, reflect Tag.E6 i v ∈ roots72 := by
  decide +kernel

theorem mem_roots72_of_isRoot {v : Fin Tag.E6.rank → ℤ} (h : IsRoot Tag.E6 v) : v ∈ roots72 := by
  induction h with
  | basis j => exact single_mem_roots72 j
  | reflect i _ ih => exact reflect_mem_roots72 i _ ih

theorem iform_self_roots72 : ∀ v ∈ roots72, iform v v = 2 := by
  decide +kernel

theorem iform_self_eq_two_of_isRoot_E6 {v : Fin Tag.E6.rank → ℤ} (h : IsRoot Tag.E6 v) :
    iform v v = 2 :=
  iform_self_roots72 v (mem_roots72_of_isRoot h)

theorem claimF_check : ∀ j : Fin Tag.E6.rank, ∀ β ∈ roots72, β ≠ Pi.single j 1 →
    ¬ (3 : ℤ) ∣ iform (β - Pi.single j 1) (β - Pi.single j 1) ∨
      ∃ i, ¬ (3 : ℤ) ∣ (Tag.cartan Tag.E6 *ᵥ (β - Pi.single j 1)) i := by
  decide +kernel

end CFSG.StandardType.KGCentE6
