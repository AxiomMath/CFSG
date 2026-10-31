
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionGenBase
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionGenBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.Rep4371.SmallFaithfulBase
public import CFSG.Monster.B.Gen.Max2AssemblyBase
public import CFSG.Monster.B.Gen.PacketGenerationBase
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2

abbrev V8 : Type := Fin 8 → ZMod 2

theorem sum_single_smul (v : V8) : v = ∑ j, v j • (Pi.single j 1 : V8) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem bvec_actD8 (arr : Array ℕ) (x : ℕ) :
    bvec 8 (Native.actD 8 arr x) = ∑ j : Fin 8, bvec 8 x j • bvec 8 arr[(j : ℕ)]! := by
  rw [bvec_actD, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

theorem linear_bvec {f : V8 →ₗ[ZMod 2] V8} {arr : Array ℕ}
    (h : ∀ j : Fin 8, f (Pi.single j 1) = bvec 8 arr[(j : ℕ)]!) (x : ℕ) :
    f (bvec 8 x) = bvec 8 (Native.actD 8 arr x) := by
  conv_lhs => rw [sum_single_smul (bvec 8 x)]
  rw [map_sum, bvec_actD8]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, h]

def genArr (k : ℕ) : Array ℕ := (genRows.getD k []).toArray

theorem genArr_get : ∀ k : Fin 45, ∀ j : Fin 8, (genArr k)[(j : ℕ)]! = genRow k j := by decide

theorem mem_isometryGroup_of_basis {f : V8 ≃ₗ[ZMod 2] V8}
    (h : ∀ i j : Fin 8, b0 (f (Pi.single i 1)) (f (Pi.single j 1)) =
      b0 (Pi.single i 1) (Pi.single j 1)) : f ∈ TauCeti.BilinForm.isometryGroup b0 := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  have e := LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin 8))
    (B := b0.compl₁₂ f.toLinearMap f.toLinearMap) (F₂ := b0) (fun i j => by
      simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, LinearEquiv.coe_coe]
      exact h i j)
  exact LinearMap.congr_fun₂ e x y

theorem map_subgroupOf_closure_range {G H ι : Type*} [Group G] [Group H] {N : Subgroup G}
    (f : N →* H) (g : ι → G) (hg : ∀ i, g i ∈ N) :
    ((Subgroup.closure (Set.range g)).subgroupOf N).map f =
      Subgroup.closure (Set.range fun i => f ⟨g i, hg i⟩) := by
  have hsub : (Subgroup.closure (Set.range g)).subgroupOf N =
      Subgroup.closure (Set.range fun i => (⟨g i, hg i⟩ : N)) := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_closure, ← Set.range_comp]
    exact inf_of_le_left ((Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hg i))
  rw [hsub, MonoidHom.map_closure, ← Set.range_comp]
  rfl

end CFSG.Monster.B.TwoA.Sp8
