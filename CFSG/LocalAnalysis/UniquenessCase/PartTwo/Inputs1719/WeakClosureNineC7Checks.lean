module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC7Data
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC7Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7.C914

open CFSG.QuasithinUnique.A6Facts

set_option maxRecDepth 100000

theorem mrow_ok (i : Fin 4) : RowOK (mrow i) := by
  constructor <;> revert i <;> decide +kernel

theorem srow_ok (j : Fin 9) : RowOK (srow j) := by
  constructor <;> revert j <;> decide +kernel

theorem m_nor : ∀ i : Fin 4, ∀ v ∈ (row i).V, ∀ h ∈ (mrow i).K,
    ∃ h' ∈ (mrow i).K, Core.cmul v h = Core.cmul h' v := by
  decide +kernel

theorem m_nor' : ∀ i : Fin 4, ∀ v ∈ (row i).V, ∀ h ∈ (mrow i).K,
    ∃ h' ∈ (mrow i).K, Core.cmul h v = Core.cmul v h' := by
  decide +kernel

theorem m_sq : ∀ i : Fin 4, ∀ h ∈ (mrow i).K, ∃ d ∈ gLit, Core.cmul d d = h := by
  decide +kernel

theorem m_comm : ∀ i : Fin 4, ∀ a ∈ (mrow i).Y, ∀ b ∈ (mrow i).Y,
    Core.cmul a b = Core.cmul b a := by
  decide +kernel

theorem m_y : ∀ i : Fin 4, ∃ y ∈ (mrow i).K, y ∈ tLit ∧
    (∀ a ∈ (mrow i).Y, ∃ a' ∈ (mrow i).Y, Core.cmul y a = Core.cmul a' y) ∧
    (∀ a ∈ (mrow i).Y, ∃ a' ∈ (mrow i).Y, Core.cmul a y = Core.cmul y a') ∧
    ∃ x ∈ (mrow i).Y, Core.cmul y x ≠ Core.cmul x y := by
  decide +kernel

theorem f_w : ∀ i : Fin 4, ∃ v ∈ (row i).V, ∃ k ∈ (row i).K, ∃ u ∈ (row i).K,
    Core.cmul k v = Core.cmul u k ∧
    Core.cmul (Core.cmul (Core.cmul v u) (Core.cmul v u)) (Core.cmul v u) = cid ∧
    Core.cmul v u ≠ cid := by
  decide +kernel

theorem s_w : ∀ c ∈ tLit, c ≠ cid → Core.cmul c c = cid → ∃ j ∈ List.finRange 9,
    c ∈ (srow j).K ∧ ∃ k ∈ (srow j).K, ∃ u ∈ (srow j).K, Core.cmul k c = Core.cmul u k ∧
      Core.cmul (Core.cmul (Core.cmul c u) (Core.cmul c u)) (Core.cmul c u) = cid ∧
      Core.cmul c u ≠ cid := by
  decide +kernel

theorem row_V_nd : ∀ i : Fin 4, (row i).V.Nodup ∧ (row i).V.length = 4 := by
  decide +kernel

theorem inv_row : ∀ c ∈ tLit, Core.cmul c c = cid → ∃ i ∈ List.finRange 4, c ∈ (row i).V := by
  decide +kernel

theorem z_cent : ∀ c ∈ tLit, c ≠ cid → (∀ t ∈ tLit, Core.cmul t c = Core.cmul c t) →
    c = zC := by
  decide +kernel

theorem p_w : pL ∈ gLit ∧ (∃ d ∈ gLit, Core.cmul d d = pL) ∧ pZ ∈ gLit ∧
    Core.cmul pL zC = Core.cmul pZ pL ∧ pH ∈ gLit ∧ pC1 ∈ tLit ∧ pC2 ∈ tLit ∧
    Core.cmul pH zC = Core.cmul pC1 pH ∧ Core.cmul pH pZ = Core.cmul pC2 pH ∧
    Core.cmul zC pZ ≠ Core.cmul pZ zC := by
  decide +kernel

theorem sq_w : ∃ d ∈ tLit, (∃ e ∈ gLit, Core.cmul e e = d) ∧ Core.cmul d d ≠ cid := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NFF7.C914
