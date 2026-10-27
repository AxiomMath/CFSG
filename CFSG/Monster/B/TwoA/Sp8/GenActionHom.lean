
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionGen
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionGen
public import Certificates.Certificate3075
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
public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Monster.B.Gen.PacketGeneration
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import Certificates.Certificate3055Base

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2

abbrev NA8 : Subgroup Dfull := Subgroup.normalizer (A8 : Set Dfull)

theorem conj_mem_A8 {n : Dfull} (hn : n ∈ NA8) {x : Dfull}
    (hx : x ∈ A8) : n * x * n⁻¹ ∈ A8 :=
  (Subgroup.mem_normalizer_iff.1 hn x).1 hx

theorem aEquiv_coe_injective
    {v w : V8}
    (h : (aEquiv (Multiplicative.ofAdd v) : Dfull) = aEquiv (Multiplicative.ofAdd w)) : v = w :=
  Multiplicative.ofAdd.injective (aEquiv.injective (Subtype.ext h))

@[expose] def conjFun
    (n : NA8)
    (v : V8) : V8 :=
  Multiplicative.toAdd (aEquiv.symm ⟨(n : Dfull) * aEquiv (Multiplicative.ofAdd v) * (n : Dfull)⁻¹,
    conj_mem_A8 n.2 (aEquiv _).2⟩)

theorem aEquiv_conjFun
    (n : NA8)
    (v : V8) :
    (aEquiv (Multiplicative.ofAdd (conjFun n v)) : Dfull) =
      n * aEquiv (Multiplicative.ofAdd v) * (n : Dfull)⁻¹ := by
  rw [conjFun, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem conjFun_add
    (n : NA8)
    (v w : V8) : conjFun n (v + w) = conjFun n v + conjFun n w := by
  apply aEquiv_coe_injective
  rw [aEquiv_conjFun, ofAdd_add, map_mul, ofAdd_add, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    aEquiv_conjFun, aEquiv_conjFun]
  group

theorem conjFun_mul
    (n m : NA8)
    (v : V8) : conjFun (n * m) v = conjFun n (conjFun m v) := by
  apply aEquiv_coe_injective
  rw [aEquiv_conjFun, aEquiv_conjFun, aEquiv_conjFun, Subgroup.coe_mul]
  group

theorem conjFun_one
    (v : V8) : conjFun
    1 v = v := by
  apply aEquiv_coe_injective
  rw [aEquiv_conjFun, OneMemClass.coe_one, one_mul, inv_one, mul_one]

@[expose] def conjLin
    (n : NA8) : V8
    →ₗ[ZMod 2] V8 :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' (conjFun n) (conjFun_add n))

@[expose] def conjHom :
    NA8 →*
    (V8 ≃ₗ[ZMod 2] V8) where
  toFun n :=
    { conjLin n with
      invFun := conjFun n⁻¹
      left_inv := fun v => by
        show conjFun n⁻¹ (conjFun n v) = v
        rw [← conjFun_mul, inv_mul_cancel, conjFun_one]
      right_inv := fun v => by
        show conjFun n (conjFun n⁻¹ v) = v
        rw [← conjFun_mul, mul_inv_cancel, conjFun_one] }
  map_one' := LinearEquiv.ext fun v => conjFun_one v
  map_mul' n m := LinearEquiv.ext fun v => conjFun_mul n m v

theorem conjHom_apply
    (n : NA8)
    (v : V8) : conjHom n v = conjFun n v := rfl

theorem aEquiv_conjHom
    (n : NA8)
    (v : V8) :
    (aEquiv (Multiplicative.ofAdd (conjHom n v)) : Dfull) =
      n * aEquiv (Multiplicative.ofAdd v) * (n : Dfull)⁻¹ :=
  aEquiv_conjFun n v

theorem conjHom_single
    {n : NA8}
    {r : ℕ} {j : Fin 8}
    (h : (n : Dfull) * aT j * (n : Dfull)⁻¹ = aEquiv (Multiplicative.ofAdd (bvec 8 r))) :
    conjHom n (Pi.single j 1) = bvec 8 r := by
  apply aEquiv_coe_injective
  rw [aEquiv_conjHom, aEquiv_single, h]

@[expose] def xGen (k : Fin 45) :
    Dfull := if h : (k : ℕ) < 44 then
    h1LiftD ⟨k, h⟩ else tauhat

theorem xGen_lift {k : Fin 45}
    (h : (k : ℕ) < 44) : xGen k = h1LiftD
    ⟨k, h⟩ := dite_eq_left h

theorem xGen_tau {k : Fin 45}
    (h : 44 ≤ (k : ℕ)) : xGen k = tauhat :=
    dite_eq_right (by omega)

theorem xGen_conj_aT
    (k : Fin 45) (j : Fin 8) :
    xGen k * aT j * (xGen k)⁻¹ = (aEquiv (Multiplicative.ofAdd (bvec 8 (genRow k j))) : Dfull) := by
  by_cases h : (k : ℕ) < 44
  · rw [xGen_lift h]
    exact h1LiftD_conj_aT ⟨k, h⟩ j
  · have hk : (k : ℕ) = 44 := by omega
    rw [xGen_tau (by omega), hk]
    exact tauhat_conj_genRow j

theorem xGen_mem_NA8
    (k : Fin 45) : xGen k ∈ NA8 := by
  by_cases h : (k : ℕ) < 44
  · rw [xGen_lift h]
    exact h1LiftD_mem_normalizer _
  · rw [xGen_tau (by omega)]
    exact tauhat_mem_normalizer_A8

theorem Xgrp_eq_closure_xGen :
    Xgrp = Subgroup.closure
    (Set.range xGen) := by
  rw [Xgrp_eq_closure]
  congr 1
  ext x
  constructor
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨44, xGen_tau le_rfl⟩
    · exact ⟨⟨k, by omega⟩, xGen_lift k.2⟩
  · rintro ⟨k, rfl⟩
    by_cases h : (k : ℕ) < 44
    · exact Or.inr ⟨_, (xGen_lift h).symm⟩
    · exact Or.inl (xGen_tau (by omega))

@[expose] def xGenL
    (k : Fin 45) : V8 ≃ₗ[ZMod 2] V8 := conjHom
    ⟨xGen k, xGen_mem_NA8 k⟩

theorem xGenL_single
    (k : Fin 45) (j : Fin 8) : xGenL k (Pi.single j 1) = bvec 8 (genRow k j) :=
  conjHom_single (xGen_conj_aT k j)

theorem xGenL_bvec
    (k : Fin 45) (x : ℕ) :
    xGenL k (bvec 8 x) = bvec 8 (Native.actD 8 (genArr k) x) :=
  linear_bvec (f := (xGenL k : V8 →ₗ[ZMod 2] V8)) (fun j => by
    rw [genArr_get]
    exact xGenL_single k j) x

theorem gramCheck : ∀ k : Fin 45, ∀ i j : Fin 8,
    ∑ a : Fin 8, ∑ b : Fin 8, bvec 8 (genRow k i) a * bvec 8 (gramRows.getD a 0) b *
      bvec 8 (genRow k j) b = bvec 8 (gramRows.getD i 0) j :=
  Certificates.certificate3075

theorem xGenL_mem_isometryGroup
    (k : Fin 45) :
    xGenL k ∈ TauCeti.BilinForm.isometryGroup b0 :=
  mem_isometryGroup_of_basis fun i j => by
    rw [xGenL_single, xGenL_single, b0_single, b0, Matrix.toBilin'_apply]
    exact gramCheck k i j

theorem conjImage_X :
    (Xgrp.subgroupOf NA8).map conjHom = Subgroup.closure (Set.range xGenL) := by
  rw [Xgrp_eq_closure_xGen]
  exact map_subgroupOf_closure_range conjHom xGen xGen_mem_NA8

theorem h1LiftD_eq_xGen (k : Fin 44)
    : h1LiftD k = xGen ⟨k, by omega⟩
    :=
  (xGen_lift (k := ⟨k, by omega⟩) k.2).symm

theorem conjImage_H1 :
    (H1.subgroupOf NA8).map conjHom =
      Subgroup.closure (Set.range fun k : Fin 44 => xGenL ⟨k, by omega⟩) := by
  have hf : h1LiftD = fun k : Fin 44 => xGen ⟨k, by omega⟩ := funext h1LiftD_eq_xGen
  have h : H1 = Subgroup.closure (Set.range fun k : Fin 44 => xGen ⟨k, by omega⟩) := by
    rw [H1_eq_closure, hf]
  rw [h]
  exact map_subgroupOf_closure_range conjHom _ fun k => xGen_mem_NA8 _

theorem conjImage_Ehat :
    (Ehat.subgroupOf NA8).map conjHom =
      Subgroup.closure (Set.range fun i : Fin 23 => xGenL ⟨i, by omega⟩) := by
  have hf : pauliD = fun i : Fin 23 => xGen ⟨i, by omega⟩ :=
    funext fun i => h1LiftD_eq_xGen ⟨i, by omega⟩
  have h : Ehat = Subgroup.closure (Set.range fun i : Fin 23 => xGen ⟨i, by omega⟩) := by
    rw [Ehat_eq_closure, hf]
  rw [h]
  exact map_subgroupOf_closure_range conjHom _ fun i => xGen_mem_NA8 _

theorem conjImage_X_le :
    (Xgrp.subgroupOf NA8).map conjHom ≤ TauCeti.BilinForm.isometryGroup b0 := by
  rw [conjImage_X, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact xGenL_mem_isometryGroup k

end CFSG.Monster.B.TwoA.Sp8
