module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7

open CFSG.QuasithinUnique.A6Facts

set_option maxRecDepth 100000

@[expose] def cid : List ℕ := List.range 8

theorem g_build : gLit = Core.buildCodes cid gGenC gTree := by decide +kernel

theorem g_tbl : Core.tblCheckC cid gGenC gLit gTbl = true := by decide +kernel

theorem g_nodup : gLit.Nodup := by decide +kernel

theorem g_length : gLit.length = 336 := by decide +kernel

theorem t_one : cid ∈ tLit := by decide +kernel

theorem t_mul : ∀ c ∈ tLit, ∀ d ∈ tLit, Core.cmul c d ∈ tLit := by decide +kernel

theorem t_sub : ∀ c ∈ tLit, c ∈ gLit := by decide +kernel

theorem t_nodup : tLit.Nodup := by decide +kernel

theorem t_length : tLit.length = 16 := by decide +kernel

theorem pair_check : ∀ c ∈ gLit, Core.cmul c c = cid → c ≠ cid →
    ∃ h ∈ gLit, ∃ c' ∈ tLit, Core.cmul h c = Core.cmul c' h ∧
      ∃ m ∈ tLit, ∃ d ∈ tLit, Core.cmul m c' = Core.cmul d m ∧
        Core.cmul c' d ≠ Core.cmul d c' := by
  decide +kernel

theorem ident_check : ∀ a ∈ tLit, ∀ b ∈ tLit, Core.cmul a a = cid → Core.cmul b b = cid →
    a ≠ cid → b ≠ cid → a ≠ b → Core.cmul a b = Core.cmul b a →
    ∃ i ∈ List.finRange 4, a ∈ (row i).V ∧ b ∈ (row i).V ∧
      (∀ v ∈ (row i).V, v = cid ∨ v = a ∨ v = b ∨ v = Core.cmul a b) ∧
      ∀ t ∈ tLit, Core.cmul t a = Core.cmul a t → Core.cmul t b = Core.cmul b t →
        t ∈ (row i).V := by
  decide +kernel

theorem row_V_sub : ∀ i : Fin 4, ∀ v ∈ (row i).V, v ∈ (row i).K := by decide +kernel

theorem row_K_sub : ∀ i : Fin 4, ∀ k ∈ (row i).K, k ∈ gLit := by decide +kernel

theorem row_Y_sub : ∀ i : Fin 4, ∀ y ∈ (row i).Y, y ∈ (row i).K := by decide +kernel

theorem row_U_sub : ∀ i : Fin 4, ∀ u ∈ (row i).U, u ∈ (row i).K := by decide +kernel

theorem row_M_sub : ∀ i : Fin 4, ∀ m ∈ (row i).M, m ∈ (row i).K := by decide +kernel

theorem row_V_one : ∀ i : Fin 4, cid ∈ (row i).V := by decide +kernel

theorem row_V_mul : ∀ i : Fin 4, ∀ c ∈ (row i).V, ∀ d ∈ (row i).V, Core.cmul c d ∈ (row i).V := by
  decide +kernel

theorem row_K_one : ∀ i : Fin 4, cid ∈ (row i).K := by decide +kernel

theorem row_Y_one : ∀ i : Fin 4, cid ∈ (row i).Y := by decide +kernel

theorem row_U_one : ∀ i : Fin 4, cid ∈ (row i).U := by decide +kernel

theorem row_M_one : ∀ i : Fin 4, cid ∈ (row i).M := by decide +kernel

theorem row_K_mul : ∀ i : Fin 4, ∀ c ∈ (row i).K, ∀ d ∈ (row i).K, Core.cmul c d ∈ (row i).K := by
  decide +kernel

theorem row_Y_mul : ∀ i : Fin 4, ∀ c ∈ (row i).Y, ∀ d ∈ (row i).Y, Core.cmul c d ∈ (row i).Y := by
  decide +kernel

theorem row_U_mul : ∀ i : Fin 4, ∀ c ∈ (row i).U, ∀ d ∈ (row i).U, Core.cmul c d ∈ (row i).U := by
  decide +kernel

theorem row_M_mul : ∀ i : Fin 4, ∀ c ∈ (row i).M, ∀ d ∈ (row i).M, Core.cmul c d ∈ (row i).M := by
  decide +kernel

theorem row_U_norm : ∀ i : Fin 4, ∀ k ∈ (row i).K, ∀ u ∈ (row i).U,
    ∃ u' ∈ (row i).U, Core.cmul k u = Core.cmul u' k := by
  decide +kernel

theorem row_M_norm : ∀ i : Fin 4, ∀ k ∈ (row i).K, ∀ m ∈ (row i).M,
    ∃ m' ∈ (row i).M, Core.cmul k m = Core.cmul m' k := by
  decide +kernel

theorem row_U_sq : ∀ i : Fin 4, ∀ u ∈ (row i).U, Core.cmul u u = cid := by decide +kernel

theorem row_M_cube : ∀ i : Fin 4, ∀ m ∈ (row i).M, Core.cmul (Core.cmul m m) m ∈ (row i).U := by
  decide +kernel

theorem row_K_sq : ∀ i : Fin 4, ∀ k ∈ (row i).K, Core.cmul k k ∈ (row i).M := by decide +kernel

theorem row_Y_cube : ∀ i : Fin 4, ∀ y ∈ (row i).Y, Core.cmul (Core.cmul y y) y = cid := by
  decide +kernel

theorem row_Y_length : ∀ i : Fin 4, (row i).Y.length = 3 := by decide +kernel

theorem row_Y_nodup : ∀ i : Fin 4, (row i).Y.Nodup := by decide +kernel

theorem row_K_nodup : ∀ i : Fin 4, (row i).K.Nodup := by decide +kernel

theorem row_KT_length : ∀ i : Fin 4,
    ((row i).K.filter fun k => decide (k ∈ tLit)).length * 3 = (row i).K.length := by
  decide +kernel

theorem row_K_nine : ∀ i : Fin 4, ¬ 9 ∣ (row i).K.length := by decide +kernel

theorem row_cent : ∀ i : Fin 4, ∀ t ∈ tLit, (∀ v ∈ (row i).V, Core.cmul t v = Core.cmul v t) →
    t ∈ (row i).K := by
  decide +kernel

theorem row_wit : ∀ i : Fin 4, ∃ k ∈ (row i).K, ∃ v ∈ (row i).V, ∀ d ∈ tLit,
    Core.cmul k v ≠ Core.cmul d k := by
  decide +kernel

theorem row_notNormal : ∀ i : Fin 4, ∃ t ∈ tLit, ∃ v ∈ (row i).V, ∀ w ∈ (row i).V,
    Core.cmul t v ≠ Core.cmul w t := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NFF7
