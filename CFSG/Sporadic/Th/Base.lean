
module

public import CFSG.Sporadic.Th.BaseBase1

public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public meta import Certificates.Data.CFSGNative.Th.Base
public import Certificates.Certificate1020
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import Certificates.Certificate1020Base

public section

namespace CFSG.Sporadic.Th

open Native Matrix Pointwise

theorem baseCode_check : formBaseCheck 124 baseCode = true :=
  Certificates.certificate1020.1

theorem cRows_inv_check : eqRows (mulRows (invRows cRows) cRows) idRows = true :=
  Certificates.certificate1020.2

theorem span_keyVec :
    Submodule.span (ZMod 2)
        (Set.range fun p : Fin 124 × Fin 2 => keyVec (deltaKeys[p.1.val]!) p.2) = ⊤ := by
  have hmul : rowsMatrix (invRows cRows) * rowsMatrix cRows = 1 := by
    have h := rowsMatrix_eq_of_eqRows cRows_inv_check
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h
  rw [eq_top_iff]
  intro v _
  have hrow (k : Fin 248) : (fun j => rowsMatrix cRows k j) ∈ Submodule.span (ZMod 2)
      (Set.range fun p : Fin 124 × Fin 2 => keyVec (deltaKeys[p.1.val]!) p.2) := by
    apply Submodule.subset_span
    refine ⟨(⟨k.val / 2, by omega⟩, ⟨k.val % 2, Nat.mod_lt _ two_pos⟩), ?_⟩
    funext j
    simp only [rowsMatrix_apply]
    rw [cRows_getD]
  have hv : v = ∑ i : Fin 248, ∑ k : Fin 248, (v i * rowsMatrix (invRows cRows) i k) •
      (fun j => rowsMatrix cRows k j) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hj (i : Fin 248) : ∑ k : Fin 248, v i * rowsMatrix (invRows cRows) i k *
        rowsMatrix cRows k j = v i * (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) i j := by
      rw [← hmul, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hj, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  rw [hv]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (hrow k)

theorem eq_one_of_fixes_deltaPlanes (g : J)
    (hg : ∀ j < 124, g • keyPlane (deltaKeys[j]!) = keyPlane (deltaKeys[j]!)) : g = 1 := by
  have hcode : ∀ i j : Fin 124, baseCode i j =
      gramCode (fun a b => keyVec (deltaKeys[i.val]!) a ⬝ᵥ
        (formF *ᵥ keyVec (deltaKeys[j.val]!) b)) := fun i j => gramCodeN_formT _ _
  have hmat := eq_one_of_isometry_image_planes formF
    (fun i a => keyVec (deltaKeys[i.val]!) a) span_keyVec baseCode hcode baseCode_check
    ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))
    (form_invariant g g.property) (fun i => by
      have h := hg i.val i.isLt
      rw [smul_set_eq_image, keyPlane_eq_span] at h
      simpa [keyVec] using h)
  apply Subtype.ext
  apply Units.ext
  simpa using hmat

end CFSG.Sporadic.Th
