module

public import CFSG.Sporadic.Co2Smith.Chain
public import Certificates.Certificate16032

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Assembly.LowTwoRank
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem colsA_sp :
    (colsMat Native.colsA)ᵀ * spJ * colsMat Native.colsA = spJ :=
  Certificates.certificate16032.1

theorem colsB_sp :
    (colsMat Native.colsB)ᵀ * spJ * colsMat Native.colsB = spJ :=
  Certificates.certificate16032.2

theorem zetaB_apply
    (y : Fin 3 ⊕ Fin 3) : (zetaB y : V) = zetaV (finSumFinEquiv y) := by
  rw [zetaB, Module.Basis.reindex_apply, Equiv.symm_symm, zetaB6_apply]

theorem res_eq_colsMat
    {g : Cz} {R : Array ℕ} (hg : g.1.val.val = rowsMatrix 22 R)
    {cols : List ℕ} (h : ∀ j < 6, Native.zetaComb cols[j]! = Native.colAct R Native.zetaVecs[j]!) :
    (res g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = colsMat cols := by
  ext x y
  rw [res_val, LinearMap.toMatrixAlgEquiv_apply]
  have key : resLin g (zetaB y) = ∑ i : Fin 6,
      (if (cols[(finSumFinEquiv y : ℕ)]!).testBit i then (1 : ZMod 2) else 0) • zetaB6 i := by
    apply Subtype.ext
    rw [resLin_apply, zetaB_apply, zetaV, mulVec_vec hg, ← h _ (finSumFinEquiv y).2,
      vec_zetaComb, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, zetaB6_apply]
    split_ifs <;> simp
  rw [key, zetaB, Module.Basis.repr_reindex_apply, Equiv.symm_symm, Module.Basis.repr_sum_self,
    colsMat]

theorem res_aE :
    (res ⟨aE, aE_mem_Cz⟩ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
    colsMat Native.colsA :=
  res_eq_colsMat aE_val' fun j hj => (res_spec.1 j hj).1

theorem res_bE :
    (res ⟨bE, bE_mem_Cz⟩ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
    colsMat Native.colsB :=
  res_eq_colsMat bE_val' fun j hj => (res_spec.1 j hj).2

theorem res_mem_of_colsMat
    {g : Cz} {cols : List ℕ}
    (h : (res g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = colsMat cols)
    (hsp : (colsMat cols)ᵀ * spJ * colsMat cols = spJ) : res g ∈ StatedSp 3 (ZMod 2) :=
  Subgroup.subset_closure (show _ = _ by rw [h]; exact hsp)

theorem res_aE_mem :
    res ⟨aE, aE_mem_Cz⟩ ∈ StatedSp 3 (ZMod 2) :=
  res_mem_of_colsMat res_aE colsA_sp

theorem res_bE_mem :
    res ⟨bE, bE_mem_Cz⟩ ∈ StatedSp 3 (ZMod 2) :=
  res_mem_of_colsMat res_bE colsB_sp

end CFSG.Sporadic.Co2Smith
