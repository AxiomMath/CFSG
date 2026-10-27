
module

public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.J4.Cert
import all Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Quasithin.H13.J4WordsInputs

@[expose] public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native

theorem wordProd_append {G : Type*} [Group G] (gs : ℕ → G) (w₁ w₂ : List ℤ) :
    wordProd gs (w₁ ++ w₂) = wordProd gs w₁ * wordProd gs w₂ := by
  simp only [wordProd, List.map_append, List.prod_append]

theorem wordProd_replicate {G : Type*} [Group G] (gs : ℕ → G) (w : List ℤ) (n : ℕ) :
    wordProd gs (List.replicate n w).flatten = wordProd gs w ^ n := by
  induction n with
  | zero => simp [wordProd]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, wordProd_append, ih, pow_succ']

theorem wordProd_cons {G : Type*} [Group G] (gs : ℕ → G) (l : ℤ) (w : List ℤ) :
    wordProd gs (l :: w) =
      (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹) * wordProd gs w := by
  simp only [wordProd, List.map_cons, List.prod_cons]

theorem wordProd_nil {G : Type*} [Group G] (gs : ℕ → G) : wordProd gs [] = 1 := by
  simp [wordProd]

theorem u_eq_wordProd : u = wordProd baseGL uLetters := by
  rw [uLetters, wordProd_append, wordProd_append, wordProd_replicate, wordProd_replicate,
    wordProd_replicate]
  simp only [wordProd_cons, wordProd_nil, baseGL]
  norm_num
  rw [u, zpow_neg, zpow_ofNat, ← inv_pow, _root_.mul_inv_rev]
  simp only [mul_assoc]

theorem v_eq_wordProd : v = wordProd baseGL vLetters := by
  rw [vLetters, wordProd_append, wordProd_append, wordProd_replicate, wordProd_replicate,
    wordProd_replicate]
  simp only [wordProd_cons, wordProd_nil, baseGL]
  norm_num
  rw [v, show gB ^ 3 = gB * gB * gB by rw [pow_succ, pow_succ, pow_one]]
  simp only [mul_assoc]

theorem eq_of_eqRows {g h : GL (Fin 112) (ZMod 2)} {X Y : Array V2}
    (hg : rowsMatrix X = (g : Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (hh : rowsMatrix Y = (h : Matrix (Fin 112) (Fin 112) (ZMod 2))) (e : eqRows X Y = true) :
    g = h :=
  Units.ext (by rw [← hg, ← hh, eqRows_iff.1 e])

theorem rowsMatrix_ne_of_rowsNe {X Y : Array V2} (h : rowsNe X Y = true) :
    rowsMatrix X ≠ rowsMatrix Y := by
  intro e
  simp only [rowsNe, vNe, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, j, hj, hne⟩ := h
  have := congrFun (congrFun e ⟨i, hi⟩) ⟨j, hj⟩
  rw [rowsMatrix_apply, rowsMatrix_apply, V2.toVec_apply, V2.toVec_apply] at this
  apply hne
  revert this
  cases (X[i]?.getD V2.zero).testBit j <;> cases (Y[i]?.getD V2.zero).testBit j <;> simp

theorem u_mem_W : u ∈ W := Subgroup.subset_closure (Set.mem_insert _ _)

theorem v_mem_W : v ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem uvGen_mem_W (i : ℕ) : uvGen i ∈ W := by
  unfold uvGen
  split_ifs
  · exact u_mem_W
  · exact v_mem_W
  · exact W.one_mem

theorem d_mem_W : d ∈ W :=
  W.mul_mem (W.mul_mem (W.mul_mem (W.inv_mem v_mem_W) u_mem_W) v_mem_W) u_mem_W

theorem t_mem_W : t ∈ W := W.pow_mem d_mem_W 22

theorem r_mem_W : r ∈ W := W.pow_mem d_mem_W 11

theorem conjugator_mem_W (i : Fin 12) : conjugator i ∈ W := wordProd_mem W uvGen_mem_W _

theorem rConj_mem_W (i : Fin 12) : rConj i ∈ W :=
  W.mul_mem (W.mul_mem (conjugator_mem_W i) r_mem_W) (W.inv_mem (conjugator_mem_W i))

theorem P_le_W : P ≤ W := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | ⟨i, rfl⟩)
  · exact t_mem_W
  · exact rConj_mem_W i

end CFSG.Quasithin.H13.J4
