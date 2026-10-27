module

public import CFSG.Sporadic.Co2Smith.Vectors
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

abbrev Cz : Subgroup K := Subgroup.centralizer ({z0} : Set K)

theorem comm_of_mem_Cz {g : K} (hg : g ∈ Cz) : g * z0 = z0 * g :=
  Subgroup.mem_centralizer_singleton_iff.mp hg

theorem mem_Cz_of_comm {g : K} (hg : g * z0 = z0 * g) : g ∈ Cz :=
  Subgroup.mem_centralizer_singleton_iff.mpr hg

@[expose] noncomputable def resLin (g : Cz) : Zsub →ₗ[ZMod 2] Zsub :=
  (g.1.val.val.mulVecLin).restrict fun _ hv => mem_Zsub_of_comm (comm_of_mem_Cz g.2) hv

theorem resLin_apply
    (g : Cz) (v : Zsub) : (resLin g v : V) = g.1.val.val *ᵥ (v : V) := rfl

@[expose] noncomputable def resEnd :
    Cz →* Module.End (ZMod 2) Zsub where
  toFun := resLin
  map_one' := by
    ext v
    rw [resLin_apply, Module.End.one_apply, Subgroup.coe_one, val_val_one, Matrix.one_mulVec]
  map_mul' g h := by
    ext v
    rw [resLin_apply, Module.End.mul_apply, resLin_apply, resLin_apply, Subgroup.coe_mul,
      val_val_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def zetaB :
    Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) Zsub :=
  zetaB6.reindex (finSumFinEquiv (m := 3) (n := 3)).symm

@[expose] noncomputable def res :
    Cz →* GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (((LinearMap.toMatrixAlgEquiv zetaB).toRingEquiv.toRingHom.toMonoidHom).comp resEnd).toHomUnits

theorem res_val (g : Cz) :
    (res g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      LinearMap.toMatrixAlgEquiv zetaB (resLin g) := rfl

theorem res_eq_one_iff
    (g : Cz) : res g = 1 ↔ ∀ v ∈ Zsub, g.1.val.val *ᵥ v = v := by
  constructor
  · intro h v hv
    have h1 : resLin g = 1 := by
      apply (LinearMap.toMatrixAlgEquiv zetaB).injective
      rw [← res_val, h, map_one]
      rfl
    have := congrArg (fun f : Module.End (ZMod 2) Zsub => (f ⟨v, hv⟩ : V)) h1
    simpa [resLin_apply] using this
  · intro h
    apply Units.ext
    rw [res_val]
    have h1 : resLin g = 1 := by
      ext v
      rw [resLin_apply, h v v.2]
      rfl
    rw [h1, map_one]
    rfl

end CFSG.Sporadic.Co2Smith
