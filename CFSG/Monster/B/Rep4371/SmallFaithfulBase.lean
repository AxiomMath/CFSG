
module

public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Assembly.LowTwoRankDefs

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Rep4371
open scoped Matrix

theorem xB_inA (a : symMat) : xB (inA a) = inA a := by
  rw [xB_apply]
  simp

theorem xB_inX (x : SpaceX) : xB (inX x) = inX x := by
  rw [xB_apply]
  simp

theorem xB_inW (N : SpaceW) : xB (inW N) = -inW N := by
  rw [xB_apply]
  simp

theorem xB_Rraw (k : ℕ) : xB (Rraw k) = if k ≤ 2322 then Rraw k else -Rraw k := by
  unfold Rraw
  split_ifs with h0 h1 h2 h3 h4 h5 h6 <;>
    first
    | omega
    | simp only [rawDiag, rawA, rawD, rawP, rawOdd, octVec, rawOct, rawSpin, xB_inA, xB_inX,
        xB_inW]

theorem xbar_eq_kappa : xbar = kappa ⟨xB, xmat_eq_xB ▸ xmat_mem_Cgen⟩ := by
  rw [xbar]
  congr 1
  exact Subtype.ext xmat_eq_xB

theorem chi_xbar_Rbasis
    (t : Fin 4371) :
    chi xbar (Rbasis t) = if (t : ℕ) ≤ 2322 then Rbasis t else -Rbasis t := by
  apply Subtype.ext
  rw [xbar_eq_kappa, coe_chi_kappa_apply]
  change xB (Rbasis t : SpaceB) = _
  rw [coe_Rbasis, xB_Rraw]
  split_ifs <;> simp [coe_Rbasis]

theorem trace_chi_xbar :
    LinearMap.trace ℚ Vst (chi xbar : Vst →ₗ[ℚ] Vst) = 275 := by
  rw [LinearMap.trace_eq_matrix_trace ℚ Rbasis, Matrix.trace]
  have hdiag : ∀ t : Fin 4371, (LinearMap.toMatrix Rbasis Rbasis (chi xbar : Vst →ₗ[ℚ] Vst)).diag t =
      if (t : ℕ) ≤ 2322 then 1 else -1 := by
    intro t
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    change Rbasis.repr (chi xbar (Rbasis t)) t = _
    rw [chi_xbar_Rbasis]
    split_ifs
    · rw [Module.Basis.repr_self, Finsupp.single_eq_same]
    · rw [show Rbasis.repr (-Rbasis t) = -Rbasis.repr (Rbasis t) from
        map_neg Rbasis.repr (Rbasis t), Module.Basis.repr_self, Finsupp.neg_apply,
        Finsupp.single_eq_same]
  rw [Finset.sum_congr rfl fun t _ => hdiag t,
    Fin.sum_univ_eq_sum_range (fun t => if t ≤ 2322 then (1 : ℚ) else -1) 4371,
    show 4371 = 2323 + 2048 from rfl, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range 2323, (if x ≤ 2322 then (1 : ℚ) else -1) = 2323 := by
    rw [Finset.sum_congr rfl fun x hx => ite_eq_left (by simp at hx; omega)]
    simp
  have h2 : ∑ x ∈ Finset.range 2048, (if 2323 + x ≤ 2322 then (1 : ℚ) else -1) = -2048 := by
    rw [Finset.sum_congr rfl fun x _ => ite_eq_right (by omega)]
    simp
  rw [h1, h2]
  norm_num

noncomputable def matR :
    Module.End ℚ Vst ≃ₐ[ℚ] Matrix (Fin 4371) (Fin 4371) ℚ :=
  LinearMap.toMatrixAlgEquiv Rbasis

noncomputable def chiMat :
    Cbar →* GL (Fin 4371) ℚ :=
  (Units.map (matR : Module.End ℚ Vst →* Matrix (Fin 4371) (Fin 4371) ℚ)).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Vst).symm.toMonoidHom.comp chi)

end CFSG.Monster.B
