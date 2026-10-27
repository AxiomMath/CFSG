
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclDefBase

public import CFSG.Monster.Existence.TwoPoint.Fi23S4
public import Certificates.Certificate16034
public import CFSG.Monster.Existence.TwoPoint.Fi23

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem gx_square_mem_rels :
    ∀ i < 10, [(i, true), (i, true)] ∈ rels :=
  Certificates.certificate16034

theorem gx_fiE_mul_self
    {i : ℕ} (hi : i < 10) : fiE i * fiE i = 1 := by
  have hv := gx_square_mem_rels i hi
  have h : wordProd fiE [(i, true), (i, true)] = 1 := by
    rw [wordProd_fiE (fiRels_lt _ hv) (fiRels_pos _ hv), fiMkW_eq_one_iff]
    exact fiRelCheck_all _ hv
  simpa [wordProd] using h

theorem gxElem_mul_self
    (k : ℕ) : gxElem k * gxElem k = 1 := by
  unfold gxElem
  split_ifs with h1 h2 h3
  · exact gx_fiE_mul_self h1
  · exact gammaZero_mul_self
  · exact fiAlpha_mul_self
  · exact fiBeta_mul_self

theorem gxElem_inv
    (k : ℕ) : (gxElem k)⁻¹ = gxElem k :=
  inv_eq_of_mul_eq_one_right (gxElem_mul_self k)

theorem gxProd_inv
    (L : List ℕ) : ((L.map gxElem).prod)⁻¹ = (L.reverse.map gxElem).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, gxElem_inv, List.reverse_cons,
      List.map_append, List.prod_append]
    simp

theorem xHat_eq_prod
    (j : ℕ) : xHat j = ((gxXList j).map gxElem).prod := by
  induction j using Nat.strongRecOn with
  | _ j ih =>
    by_cases h : 0 < j ∧ gxParent j < j
    · rw [xHat, dite_eq_left h, gxXList, dite_eq_left h, ih _ h.2, List.map_append,
        List.prod_append]
      congr 1
      have e10 : gxElem 10 = gammaZero := by simp [gxElem]
      unfold gxT
      rw [gxW_eq_prod, gxProd_inv, List.map_append, List.map_append, List.prod_append,
        List.prod_append]
      simp [e10, ← List.map_reverse, mul_assoc]
    · rw [xHat, dite_eq_right h, gxXList, dite_eq_right h]
      simp

end CFSG.Monster.Existence
